#!/usr/bin/env python3
"""Cache-vs-cold comparison for the nightly cold gate (scripts/gate/nightly-cold-gate.sh; docs/TESTING.md
"Build cache policy").

    gate-cachecmp.py hashes WORKTREE OUT.json     SHA-256 of the build artifacts the ASL/Sail caches serve:
                                                  every ArmASL and JanusASL .olean, and every emitted C file and
                                                  compiled C object (ir:<tree>/<path>; ArmASL's modules build under models/asl/.lake/build/ir/ArmASL, i.e. the janusasl tree; a symlinked file is recorded as symlink:<target>) of the janus, janusasl and Sail
                                                  Lake trees (and their combined digest)
                                                  and the Sail oracle driver binary, plus the build
                                                  configuration the driver depends on (config:SAIL_SPLIT from
                                                  the environment, default 1, and config:SAIL_SPLIT_PARTS from
                                                  scripts/validation/sail-arm.sh), which is not part of the digest
    gate-cachecmp.py compare CACHED_OUT COLD_OUT  compare two gate output directories (timeline.jsonl and
                                                  artifact-hashes.json each)

Byte hashes of .olean files are not comparable across directories: Lean 4.34 stores the module's linter messages
(`Lean.Linter.lintLogExt`) in the .olean together with the absolute source path, so a module that emits a warning
differs between two worktrees (and from the copy a cache entry was published from) in thousands of bytes although every
declaration is the same. For the modules under models/asl/JanusASL/Proofs/ ONLY, `hashes` therefore also records
`sem:<module>` = the SHA-256 of the module re-serialized with its message log removed (tools/oleandigest: Lean's own
saveModuleData, the WHOLE file: header, constants, every other extension's entries, compiled code), `lint:<module>` = the
number of message-log entries and `lay:<module>` = "ok" when the original file has no bytes the module data does not
account for (its size equals the re-serialization of the unstripped module and its header matches). `compare` accepts a file
hash difference as "path-only" ONLY for such a module when both runs recorded lay "ok", a non-empty message log and equal
semantic digests; everything else (ArmASL/*, Janus/*, lean-sail, the Sail driver, a module with an empty message log, a
trailing-garbage file, a missing digest, a module in only one run) must be byte-identical or it is a P0 / fail-closed.
The digest executable is built once from the trusted checkout that holds this script and the same executable is used for
every tree; the SHA-256 of its source and binary are recorded as config:oleandigest-* (a difference is a configuration
mismatch, rc 2).

`compare` exits 0 when the two runs agree on the commit, on the status of every prebuild step, stage, item
and lane (PASS/FAIL), and on every artifact hash; 1 with a "P0 CACHE BUG" report on any difference (the
cached run and the truly cold run of one commit must not differ: any difference means the cache served
something the inputs do not determine, or a key misses an input); 2 when a run cannot be compared (missing
or malformed files, different commits, or DIFFERENT BUILD CONFIGURATION: the cached and the cold run recorded
another SAIL_SPLIT or parts count, so their drivers differ by construction and a difference between them says nothing
about the cache; reported as a CONFIGURATION MISMATCH, never as a P0 CACHE BUG, and never a pass. Run both gates with
the same SAIL_SPLIT set explicitly (scripts/gate/nightly-cold-gate.sh does))."""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

CONFIG = "config:"
SEM = "sem:"
LINT = "lint:"
LAY = "lay:"
# only these modules may differ in bytes between the cached and the cold run (message log with the source path)
PATH_ONLY_PREFIX = "JanusASL/Proofs/"
HEADER = 80  # "olean", version, flags, Lean version, git hash; the 8 bytes after it are the base address (module-name derived)
LINE_RE = re.compile(r"^(\d+)\t([^\t\n]+)\t(\d+)\t(\d+)\t(\d+)\t(\d+)$")


def sha_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


TRUSTED_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def digest_tool():
    """Build (once) tools/oleandigest of the TRUSTED checkout that holds this script and return (exe, source sha, binary sha);
    raises RuntimeError when it cannot be built (the caller fails closed)."""
    d = os.path.join(TRUSTED_ROOT, "tools", "oleandigest")
    exe = os.path.join(d, ".lake", "build", "bin", "janus-olean-digest")
    if not os.path.isdir(d):
        raise RuntimeError("%s does not exist" % d)
    r = subprocess.run(["lake", "build"], cwd=d, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if r.returncode != 0 or not os.access(exe, os.X_OK):
        raise RuntimeError("cannot build %s: %s" % (d, r.stdout[-500:]))
    src = hashlib.sha256()
    for f in ("Main.lean", "lakefile.toml", "lean-toolchain"):
        src.update(("%s %s\n" % (f, sha_file(os.path.join(d, f)))).encode())
    return exe, src.hexdigest(), sha_file(exe)


def semantic(exe, paths):
    """{path: (sha256 of the stripped re-serialization, message-log entries, layout)} from janus-olean-digest, in batches.
    Fails closed: a non-zero exit, a crash, a line that is not exactly the expected shape, a missing, duplicate or unexpected
    module raises RuntimeError."""
    out = {}
    for i in range(0, len(paths), 20):
        batch = paths[i:i + 20]
        tmp = tempfile.mkdtemp(prefix="oleandigest.")
        try:
            r = subprocess.run([exe, tmp] + batch, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            if r.returncode != 0:
                raise RuntimeError("janus-olean-digest failed (rc %s): %s" % (r.returncode, r.stderr[-400:]))
            got = {}
            for line in r.stdout.splitlines():
                m = LINE_RE.match(line)
                if not m:
                    raise RuntimeError("janus-olean-digest: unexpected output line %r" % line[:200])
                idx = int(m.group(1))
                if idx >= len(batch) or idx in got or batch[idx] != m.group(2):
                    raise RuntimeError("janus-olean-digest: unexpected, duplicate or mismatched module in line %r" % line[:200])
                got[idx] = m
            if len(got) != len(batch):
                raise RuntimeError("janus-olean-digest: %d of %d modules reported" % (len(got), len(batch)))
            for idx, m in got.items():
                strp = os.path.join(tmp, "%d.stripped" % idx)
                if os.path.getsize(strp) != int(m.group(6)):
                    raise RuntimeError("janus-olean-digest: size of %s differs from the reported one" % strp)
                with open(strp, "rb") as f:
                    shead = f.read(HEADER)
                with open(batch[idx], "rb") as f:
                    ohead = f.read(HEADER)
                lay = "ok"
                if int(m.group(3)) != int(m.group(4)):
                    lay = "bad:size %s != re-serialization %s" % (m.group(3), m.group(4))
                elif ohead != shead:
                    lay = "bad:header"
                out[batch[idx]] = (sha_file(strp), int(m.group(5)), lay)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    return out


def hashes(worktree):
    out = {}
    lib = os.path.join(worktree, "models", "asl", ".lake", "build", "lib", "lean")
    oleans = []
    for d, dirs, files in os.walk(lib):
        dirs.sort()
        for f in sorted(files):
            if f.endswith(".olean"):
                p = os.path.join(d, f)
                rel = os.path.relpath(p, lib)
                out["olean:" + rel] = sha_file(p)
                if rel.startswith(PATH_ONLY_PREFIX):
                    oleans.append(p)
    if oleans:
        exe, src, binsha = digest_tool()
        out[CONFIG + "oleandigest-src"] = src
        out[CONFIG + "oleandigest-bin"] = binsha
        for p, (dg, lint, lay) in semantic(exe, oleans).items():
            rel = os.path.relpath(p, lib)
            out[SEM + rel] = dg
            out[LINT + rel] = str(lint)
            out[LAY + rel] = lay
    # EVERY emitted C file and compiled C object of every Lake tree (module-cache entries carry ir/<M>.c and ir/<M>.c.o.export
    # for Janus.*, JanusASL.* and ArmASL.*; they are linked into janus-audit, janus-decode, janus-oracle and janus-asl-check
    # and, unlike an .olean, nothing replays them): the cached and the cold run of one commit must have byte-identical ones.
    # The .trace files are left out (they record absolute paths of the two worktrees); the .hash files are Lake's own hash of
    # the file next to them. The .cin files are left out too: they are the object cache's own record of the C an object was
    # compiled from, written only when an object is restored from (or published to) the cache, so a cold run never has them;
    # the C files and the objects they describe ARE compared here, and the cache audit checks each entry's .cin against its C.
    # Keys carry the tree and the path under build/ir, so a file present in one run only is a difference.
    for tree, lake in (("janus", os.path.join(worktree, ".lake")),
                       ("janusasl", os.path.join(worktree, "models", "asl", ".lake")),
                       ("sail", os.path.join(worktree, "models", "asl", ".lake", "packages", "Sail", ".lake"))):
        base = os.path.join(lake, "build", "ir")
        for d, dirs, files in os.walk(base):
            dirs.sort()
            for f in sorted(files):
                if f.endswith(".trace") or f.endswith(".setup.json") or f.endswith(".cin"):
                    continue
                if f.endswith(".c") or f.endswith(".c.hash") or ".c.o." in f:
                    p = os.path.join(d, f)
                    key = "ir:%s/%s" % (tree, os.path.relpath(p, base).replace(os.sep, "/"))
                    # a symlinked file is RECORDED, never skipped: 'symlink:<target>' differs from any regular file's hash
                    out[key] = "symlink:" + os.readlink(p) if os.path.islink(p) else sha_file(p)
    drv = os.path.join(worktree, "validation", "reference-models", "sail-arm", "target", "release", "janus-oracle-sail")
    if os.path.isfile(drv):
        out["sail-driver"] = sha_file(drv)
    out.update(config(worktree))
    # `combined`: every artifact digest that is path independent (the sem/lint/lay records and the driver, and the file hashes of
    # the modules outside models/asl/JanusASL/Proofs/); `combined:bytes` all file hashes (informational)
    h = hashlib.sha256()
    for k in sorted(k for k in out if not k.startswith(CONFIG) and not (k.startswith("olean:") and k[6:].startswith(PATH_ONLY_PREFIX))):
        h.update(("%s %s\n" % (k, out[k])).encode())
    out["combined"] = h.hexdigest()
    hb = hashlib.sha256()
    for k in sorted(k for k in out if k.startswith("olean:")):
        hb.update(("%s %s\n" % (k, out[k])).encode())
    out["combined:bytes"] = hb.hexdigest()
    return out


def config(worktree):
    """The build configuration the Sail driver is a function of, recorded next to its hash."""
    parts = "unknown"
    try:
        m = re.search(r"^SAIL_SPLIT_PARTS=(\d+)\s*$", open(os.path.join(worktree, "scripts", "validation", "sail-arm.sh")).read(), re.M)
        if m:
            parts = m.group(1)
    except OSError:
        pass
    return {CONFIG + "SAIL_SPLIT": os.environ.get("SAIL_SPLIT", "1"), CONFIG + "SAIL_SPLIT_PARTS": parts}


def load_timeline(d):
    rows = []
    with open(os.path.join(d, "timeline.jsonl")) as f:
        for line in f:
            if line.strip():
                rows.append(json.loads(line))
    gate = next((r for r in rows if r.get("kind") == "gate"), None)
    st = {}
    for r in rows:
        k = r.get("kind")
        if k in ("prebuild", "stage"):
            st["%s:%s" % (k, r["name"])] = "PASS" if r.get("rc") in (0, "0") else "FAIL"
        elif k == "item":
            st["item:%s:%s" % (r.get("pool"), r["id"])] = "PASS" if str(r.get("status")).upper().startswith("PASS") else "FAIL(%s)" % r.get("status")
    return gate, st


def path_only_reason(rel, h1, h2):
    """None when the file difference of module rel is explained by the stored message log alone, else why it is not."""
    for tag, h in (("cached", h1), ("cold", h2)):
        if not h.get(SEM + rel) or not h.get(LINT + rel) or not h.get(LAY + rel):
            return "%s run recorded no semantic digest for it (fail closed)" % tag
        if h[LAY + rel] != "ok":
            return "%s run: the file has bytes the module data does not account for (%s)" % (tag, h[LAY + rel])
        if h[LINT + rel] in ("0", ""):
            return "%s run: its message log is empty, so the stored log cannot be what differs" % tag
    if h1[SEM + rel] != h2[SEM + rel]:
        return "SEMANTIC digests differ (cached %s, cold %s): the module declares something different" % (h1[SEM + rel][:16], h2[SEM + rel][:16])
    return None


def compare(cached, cold):
    try:
        g1, s1 = load_timeline(cached)
        g2, s2 = load_timeline(cold)
        h1 = json.load(open(os.path.join(cached, "artifact-hashes.json")))
        h2 = json.load(open(os.path.join(cold, "artifact-hashes.json")))
        if not isinstance(h1, dict) or not isinstance(h2, dict):
            raise ValueError("artifact-hashes.json is not a JSON object")
    except (OSError, ValueError, KeyError) as ex:
        print("cachecmp: cannot compare the runs: %s" % ex)
        return 2
    if not g1 or not g2 or g1.get("commit") != g2.get("commit"):
        print("cachecmp: the runs are of different commits (%s vs %s): not comparable" % (
            (g1 or {}).get("commit"), (g2 or {}).get("commit")))
        return 2
    # an unrecorded setting (artifact-hashes.json of an older gate) is a mismatch too: fail closed
    cfg = [k for k in sorted(set(h1) | set(h2) | {CONFIG + "SAIL_SPLIT", CONFIG + "SAIL_SPLIT_PARTS"})
           if k.startswith(CONFIG) and (h1.get(k) is None or h1.get(k) != h2.get(k))]
    if cfg:
        print("cachecmp: CONFIGURATION MISMATCH (not a cache verdict): the cached and the cold run of commit %s were built with different settings:" % g1.get("commit"))
        for k in cfg:
            print("  %s: cached %s, cold %s" % (k[len(CONFIG):], h1.get(k, "not recorded"), h2.get(k, "not recorded")))
        print("cachecmp: not comparable (the Sail drivers differ by construction). Re-run both with the same SAIL_SPLIT set explicitly.")
        return 2
    # fail closed: the C/object comparison needs both runs to have hashed some (an older gate, a build that did not run)
    none = [n for n, h in (("cached", h1), ("cold", h2)) if not any(k.startswith("ir:") for k in h)]
    if none:
        print("cachecmp: not comparable: no emitted C file or compiled C object was hashed in the %s run (ir:* missing from "
              "artifact-hashes.json): the C/object comparison did not run" % " and ".join(none))
        return 2
    diffs = []
    for k in sorted(set(s1) | set(s2)):
        a, b = s1.get(k, "MISSING"), s2.get(k, "MISSING")
        if a != b:
            diffs.append("%s: cached run %s, cold run %s" % (k, a, b))
    path_only = []
    for k in sorted(k for k in set(h1) | set(h2) if not k.startswith(CONFIG)):
        a, b = h1.get(k), h2.get(k)
        if k == "combined:bytes":
            continue
        if k.startswith((SEM, LINT, LAY)):
            rel = k.split(":", 1)[1]
            if ("olean:" + rel) in h1 and ("olean:" + rel) in h2:
                continue   # judged together with the file hash of the same module below
        if k.startswith("olean:"):
            rel = k[len("olean:"):]
            if a and b and a == b:
                continue
            if a and b and rel.startswith(PATH_ONLY_PREFIX):
                why = path_only_reason(rel, h1, h2)
                if why is None:
                    path_only.append(rel)
                else:
                    diffs.append("artifact %s: cached %s, cold %s; not accepted as path-only: %s" % (k, a[:16], b[:16], why))
                continue
        if a != b:
            diffs.append("artifact %s: cached %s, cold %s" % (k, (a or "MISSING")[:16], (b or "MISSING")[:16]))
    if diffs:
        print("P0 CACHE BUG: the cached gate and the cold gate of commit %s disagree (%d differences):" % (g1.get("commit"), len(diffs)))
        for d in diffs:
            print("  " + d)
        print("P0: owner is the main session (docs/TESTING.md 'Build cache policy'): treat every cached gate result since the last agreeing nightly as unproven.")
        return 1
    if path_only:
        print("cachecmp: %d module file hashes differ ONLY by the stored message log / source path (semantic digests equal): %s" % (
            len(path_only), ", ".join(path_only[:40]) + (" ..." if len(path_only) > 40 else "")))
    print("cachecmp: cached and cold runs of commit %s agree on %d prebuild steps/stages/items/lanes and %d artifact hashes (SAIL_SPLIT=%s, %s parts; %d path-only)" % (
        g1.get("commit"), len(s1), len([k for k in h1 if not k.startswith(CONFIG)]), h1[CONFIG + "SAIL_SPLIT"], h1[CONFIG + "SAIL_SPLIT_PARTS"], len(path_only)))
    return 0


def main(a):
    if len(a) == 3 and a[0] == "hashes":
        json.dump(hashes(a[1]), open(a[2], "w"), sort_keys=True, indent=1)
        return 0
    if len(a) == 3 and a[0] == "compare":
        return compare(a[1], a[2])
    sys.exit(__doc__)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
