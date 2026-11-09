#!/usr/bin/env python3
"""Make (or verify) the patched copy of the pinned sail-aarch64-oracle crate that builds the model in parallel.

usage: split_crate.py CRATE_CHECKOUT DEST ORIG_BUILD_RS_SHA256 PATCHED_BUILD_RS_SHA256 PATCH

CRATE_CHECKOUT is the crate at its pinned git revision (scripts/oracle-sail.sh fetch_crate). DEST/sail-aarch64-oracle
becomes a copy of it in which ONLY build.rs differs: `patch` applies oracle-sail/build.rs.patch (an opt-in
AARCH64_ORACLE_SAIL_MODEL_PARTS=<dir>: compile <dir>/model_part_*.cpp instead of the one model.cpp; nothing else changes),
and both build.rs hashes are pinned. DEST/config.toml is a cargo `--config` file replacing the crate's git source with
this directory (cargo's directory-source mechanism, as `cargo vendor` writes it): Cargo.lock is untouched and
`cargo build --locked` still checks the crate's source id, and cargo re-checks every file against DEST's
.cargo-checksum.json on each build. The copy is verified file by file against CRATE_CHECKOUT on every call
(an existing DEST that differs anywhere but build.rs, or whose build.rs is not the pinned patched file, is an error).
Prints the config path.
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

checkout, dest, orig_sha, patched_sha, patch = sys.argv[1:6]
SRC_ID = "git+https://github.com/yufengzjj/sail-aarch64-oracle?rev=%s"


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def tree(root, skip_root=False):
    """({relative path: (sha256, executable bit)} of every file under `root`, the set of its directories).
    With skip_root (the pinned checkout only), `.git` and `target` are skipped directly under the crate root, the
    checkout's git dir and build dir; the copy has neither, so there they are paths like any other; every other path at any depth, dotted names included, is compared. A symlink (file or
    directory) anywhere is an error."""
    out, dirs_out = {}, set()
    for d, dirs, files in os.walk(root):
        if skip_root and d == root:
            dirs[:] = [x for x in dirs if x not in (".git", "target")]
        dirs.sort()
        for x in dirs:
            p = os.path.join(d, x)
            assert not os.path.islink(p), "symlinked directory " + p
            dirs_out.add(os.path.relpath(p, root))
        for f in sorted(files):
            p = os.path.join(d, f)
            assert not os.path.islink(p), "symlink " + p
            out[os.path.relpath(p, root)] = (sha(p), bool(os.stat(p).st_mode & 0o111))
    return out, dirs_out


def shas(t):
    return {k: v[0] for k, v in t.items()}


def rev_of(checkout):
    return subprocess.run(["git", "-C", checkout, "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()


rev = rev_of(checkout)
assert subprocess.run(["git", "-C", checkout, "status", "--porcelain", "--untracked-files=no"], capture_output=True, text=True).stdout.strip() == "", "crate checkout is modified"
base, base_dirs = tree(checkout, True)
assert base["build.rs"][0] == orig_sha, "pinned crate build.rs is not the expected file"
crate = os.path.join(dest, "sail-aarch64-oracle")


def make():
    os.makedirs(os.path.dirname(os.path.abspath(dest)), exist_ok=True)
    tmp = tempfile.mkdtemp(prefix=".split-crate.", dir=os.path.dirname(os.path.abspath(dest)))
    c = os.path.join(tmp, "sail-aarch64-oracle")
    shutil.copytree(checkout, c, ignore=lambda d, names: [n for n in names if d == checkout and n in (".git", "target")], symlinks=True)
    subprocess.run(["patch", "-s", "-p0", os.path.join(c, "build.rs"), patch], check=True)
    got = sha(os.path.join(c, "build.rs"))
    assert got == patched_sha, "patched build.rs hash %s != pinned %s" % (got, patched_sha)
    files = shas(tree(c)[0])
    json.dump({"files": files, "package": None}, open(os.path.join(c, ".cargo-checksum.json"), "w"), sort_keys=True)
    with open(os.path.join(tmp, "config.toml"), "w") as f:
        f.write('[source."%s"]\ngit = "https://github.com/yufengzjj/sail-aarch64-oracle"\nrev = "%s"\nreplace-with = "janus-split-crate"\n'
                '[source.janus-split-crate]\ndirectory = "%s"\n' % (SRC_ID % rev, rev, dest))
    try:
        os.rename(tmp, dest)
    except OSError:  # a concurrent build made it first: verify theirs below
        shutil.rmtree(tmp)


if not os.path.isdir(dest):
    make()
want = dict(base)
want["build.rs"] = (patched_sha, base["build.rs"][1])
try:
    have, have_dirs = tree(crate)
except AssertionError as ex:
    sys.exit("split crate %s: %s" % (dest, ex))
have.pop(".cargo-checksum.json", None)
if have != want or have_dirs != base_dirs:
    bad = sorted(k for k in set(have) | set(want) if have.get(k) != want.get(k)) + sorted(have_dirs ^ base_dirs)
    sys.exit("split crate %s differs from the pinned crate beyond build.rs (content, executable bit, extra or missing path): %s" % (dest, bad[:5]))
rec = json.load(open(os.path.join(crate, ".cargo-checksum.json")))
if rec["files"] != shas(have):
    sys.exit("split crate %s: .cargo-checksum.json does not match its files" % dest)
cfg = open(os.path.join(dest, "config.toml")).read()
expect = ('[source."%s"]\ngit = "https://github.com/yufengzjj/sail-aarch64-oracle"\nrev = "%s"\nreplace-with = "janus-split-crate"\n'
          '[source.janus-split-crate]\ndirectory = "%s"\n' % (SRC_ID % rev, rev, dest))
if cfg != expect:
    sys.exit("split crate %s: config.toml was altered" % dest)
print(os.path.join(dest, "config.toml"))
