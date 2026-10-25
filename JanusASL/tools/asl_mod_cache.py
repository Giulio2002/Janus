#!/usr/bin/env python3
"""Shared per-module build cache for the JanusASL proofs and the Janus framework modules they
import (scripts/asl.sh, ASL_CACHE; docs/ASL.md "Build cache").

    python3 -I JanusASL/tools/asl_mod_cache.py restore REPO_ROOT CACHE   copy cached builds in
    python3 -I JanusASL/tools/asl_mod_cache.py publish REPO_ROOT CACHE [--exe]
                                    store the builds of the JanusASL library's closure (--exe: and
                                    of its executables'), after `lake build` has built them
    python3 -I JanusASL/tools/asl_mod_cache.py keys    REPO_ROOT         module -> key, one per line
    python3 -I JanusASL/tools/asl_mod_cache.py show    REPO_ROOT MODULE  the canonical inputs of a key
    python3 -I JanusASL/tools/asl_mod_cache.py gc      CACHE --max SIZE [--root REPO_ROOT]
                                    [--grace SECONDS] [--dry-run]
                                    evict entries (see "Eviction" below)

The ArmASL model and lean-sail are cached as one entry (asl_cache_key.py). This adds one entry per
Lean module of the JanusASL package (JanusASL.*) and of the janus package (Janus.*), so a worktree
at a commit some other worktree already built restores every module instead of elaborating it, and
an edit to one file leaves the entries of everything that does not depend on it valid.

**The key of a module** is the SHA-256 of exactly the inputs Lake 4.34 hashes into the module's
trace (`.trace`, `inputs`; Lake/Build/Module.lean) and of the inputs that reach its outputs without
being traced, each one replaced by its own content:

  * the module's name and the SHA-256 of its source file (Lake: the source file's hash);
  * for every direct import, the import's key (Lake: the import's trace and `importAllArts`, which
    are themselves functions of its sources and imports, so the recursion covers the transitive
    closure): a JanusASL.* or Janus.* module by this same key; an ArmASL module by the ArmASL
    cache key (asl_cache_key.py: the vendored model, toolchain, lean-sail entry, ArmASL lib
    settings); a Sail.* module by the manifest's lean-sail entry; Init/Std/Lean/Lake by the
    toolchain;
  * the module's package configuration: its lakefile parsed and reduced to every package-level
    setting except metadata (asl_cache_key.PKG_IGNORED), and *every* lean_lib / lean_exe table of
    the package (Lake builds a module with its library's leanOptions / moreLeanArgs /
    moreLeancArgs; keying all of them is a superset of the owning one), plus the extraDepTargets of
    both packages (Lake: `extraDep`, mixed into every module trace);
  * the toolchain: both lean-toolchain files and `lean --version` (Lake: "Lean 4.34.1, commit ...");
  * the machine (`uname -m`: the C and object outputs) and the version of this scheme.

A module whose imports cannot be resolved this way (an import from no known package) has no key:
it is never restored or published (Lake builds it as usual).

**An entry** is `CACHE/mods/<key>/tree/<package dir>/...` with the module's build outputs exactly
as Lake writes them under the package's `.lake/build` (`lib/lean/<M>.olean|.ilean|.trace|.hash`,
`ir/<M>.c|.c.hash|.c.o.export|...`, except `.setup.json`, which holds absolute paths and is an input
Lake regenerates), and `MANIFEST.sha256` over them. Restore checks every copied file against the
manifest (and drops the module's outputs if one differs); publish writes into a temporary
directory and renames it into place, one publisher per key (flock), never replacing an entry.
Lake remains the judge: a restored module whose trace does not match what Lake computes here is
simply rebuilt. Publish stores only modules of the closure of the targets just built (they are up
to date), and only if their trace is newer than their source.

**Locks.** Every entry has a lock file next to it (`<key>.lock`): publish holds it exclusively,
restore holds it shared while it copies the entry's files and then touches the entry's use stamp
(`<key>.use`, its last restore), and the collector removes an entry only under it, taken
exclusively without waiting. A lock file can be removed by the collector while held, so a lock is
retried until the path still names the locked file (as cmd/janus does). The ArmASL entries of
scripts/asl.sh (`CACHE/<32 hex>`, `.lock`, `.use`) follow the same protocol.

**Eviction** (`gc`; scripts/asl.sh runs it after every publish with `--max $ASL_CACHE_MAX`, default
15G): first every ArmASL entry that no module entry references (an `armasl:<key>` import in its
INPUTS.json) and that is not the checkout's own key (`--root`; both the current and the legacy
key); then, while the cache is larger than SIZE, the least recently used entry (by its use stamp,
else the entry's own modification time, i.e. its publication), modules and ArmASL entries alike
except the checkout's ArmASL entry; then the ArmASL entries the evicted modules were the last to
reference. Entries used or published within the grace period (default 3600 s) are never removed,
which also covers a restore by an older copy of this script that takes no lock. An entry is made
invisible in one step (renamed into a fresh `CACHE/.gc-trash-*` directory on the same filesystem,
so a reader sees the whole entry or none, and Lake rebuilds a module whose entry vanished) and only
then deleted; its use stamp and lock file are removed while the lock is held. Collecting only
ever deletes: a missing entry is a miss, never a different result. Leftover `.gc-trash-*` and
publish `.tmp-*` directories older than a day are removed too.

**Trust.** As for the ArmASL entry: the cache must be writable only by users you trust, since a
restored `.olean` is what later modules (and `janus verify --asl`) are checked against; the kernel
replay (`scripts/asl.sh replay`, the replay of `janus verify --asl`) re-checks every declaration,
and the manifest catches corruption, not a malicious writer.
"""
import fcntl
import hashlib
import importlib.util
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile

SCHEME = "janusasl-module-cache-v1"
CORE = {"Init", "Std", "Lean", "Lake"}


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


def sha_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def load_armasl_key(root):
    sys.dont_write_bytecode = True  # no __pycache__ in the checkout
    path = os.path.join(root, "JanusASL", "tools", "asl_cache_key.py")
    spec = importlib.util.spec_from_file_location("asl_cache_key", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


IMPORT_RE = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][\w.]*)")


def header_imports(path):
    """The modules a Lean file imports (its header: everything before the first non-import line
    other than comments, `prelude` and `module`)."""
    imps = []
    in_block = 0
    with open(path, encoding="utf-8") as f:
        for line in f:
            s = line.strip()
            if in_block:
                in_block += s.count("/-") - s.count("-/")
                continue
            if s.startswith("/-"):
                in_block = s.count("/-") - s.count("-/")
                continue
            if not s or s.startswith("--") or s in ("prelude", "module"):
                continue
            m = IMPORT_RE.match(line)
            if m:
                imps.append(m.group(1))
                continue
            break
    return imps


class Pkg:
    def __init__(self, name, dir, prefix, cfg):
        self.name, self.dir, self.prefix, self.cfg = name, dir, prefix, cfg

    def source(self, mod):
        return os.path.join(self.dir, *mod.split(".")) + ".lean"

    def owns(self, mod):
        return mod.split(".")[0] == self.prefix

    def build(self):
        return os.path.join(self.dir, ".lake", "build")


def reduced_lakefile(akey, path):
    try:
        import tomllib
    except ImportError:
        tomllib = None
    if tomllib is None or not path.endswith(".toml") or not os.path.exists(path):
        return {"whole": sha_file(path)}
    with open(path, "rb") as f:
        cfg = tomllib.load(f)
    return {"package": {k: v for k, v in cfg.items() if k not in akey.PKG_IGNORED},
            "lean_lib": cfg.get("lean_lib", []), "lean_exe": cfg.get("lean_exe", []),
            "extraDepTargets": cfg.get("extraDepTargets", [])}


def lakefile_path(d):
    lean = os.path.join(d, "lakefile.lean")
    return lean if os.path.exists(lean) else os.path.join(d, "lakefile.toml")


class Keys:
    def __init__(self, root):
        self.root = os.path.abspath(root)
        pkgdir = os.path.join(self.root, "JanusASL")
        self.akey = load_armasl_key(self.root)
        self.pkgs = [Pkg("janusasl", pkgdir, "JanusASL", reduced_lakefile(self.akey, lakefile_path(pkgdir))),
                     Pkg("janus", self.root, "Janus", reduced_lakefile(self.akey, lakefile_path(self.root)))]
        try:
            ver = subprocess.run(["lean", "--version"], cwd=pkgdir, capture_output=True, text=True, timeout=120).stdout.strip()
        except Exception:
            ver = ""
        with open(os.path.join(self.root, "lean-toolchain")) as f:
            tc = f.read().strip()
        with open(os.path.join(pkgdir, "lean-toolchain")) as f:
            tcj = f.read().strip()
        self.common = {
            "scheme": SCHEME, "toolchain": tc, "toolchain.JanusASL": tcj, "lean": ver, "machine": platform.machine(),
            "extraDepTargets": {p.name: p.cfg.get("extraDepTargets", p.cfg.get("whole")) for p in self.pkgs},
        }
        self.armasl = self.akey.sha(self.akey.canonical(self.akey.inputs(self.root)).encode())[:32]
        with open(os.path.join(pkgdir, "lake-manifest.json")) as f:
            manifest = json.load(f)
        self.sail = [p for p in manifest.get("packages", []) if p.get("name") == "Sail"]
        self.memo = {}
        self.inputs_of = {}

    def pkg_of(self, mod):
        for p in self.pkgs:
            if p.owns(mod):
                return p
        return None

    def key(self, mod, stack=()):
        if mod in self.memo:
            return self.memo[mod]
        root = mod.split(".")[0]
        if root in CORE:
            return "core:" + self.common["lean"] + self.common["toolchain"]
        if root == "ArmASL":
            return "armasl:" + self.armasl
        if root == "Sail":
            return "sail:" + canonical(self.sail)
        p = self.pkg_of(mod)
        if p is None or mod in stack:
            self.memo[mod] = None
            return None
        src = p.source(mod)
        if not os.path.exists(src):
            self.memo[mod] = None
            return None
        imps = []
        for i in header_imports(src):
            k = self.key(i, stack + (mod,))
            if k is None:
                self.memo[mod] = None
                return None
            imps.append([i, k])
        inp = dict(self.common, module=mod, package=p.name, source=sha_file(src), imports=imps, lakefile=p.cfg)
        k = sha_bytes(canonical(inp).encode())[:40]
        self.memo[mod] = k
        self.inputs_of[mod] = inp
        return k

    def modules(self):
        """Every module of the two packages with a source file (JanusASL.*, Janus.*)."""
        out = []
        for p in self.pkgs:
            top = os.path.join(p.dir, p.prefix)
            cands = [p.prefix] if os.path.exists(os.path.join(p.dir, p.prefix + ".lean")) else []
            for d, dirs, files in os.walk(top):
                dirs[:] = sorted(x for x in dirs if not x.startswith("."))
                for fn in sorted(files):
                    if fn.endswith(".lean"):
                        rel = os.path.relpath(os.path.join(d, fn[:-5]), p.dir)
                        cands.append(rel.replace(os.sep, "."))
            out += cands
        return out


def outputs(p, mod):
    """The build outputs of mod under p's .lake/build, relative to p.dir (existing files only)."""
    rel = os.path.join(*mod.split("."))
    res = []
    for sub in ("lib/lean", "ir"):
        d = os.path.join(p.build(), sub, os.path.dirname(rel))
        base = os.path.basename(rel) + "."
        if not os.path.isdir(d):
            continue
        for fn in sorted(os.listdir(d)):
            full = os.path.join(d, fn)
            if fn.startswith(base) and os.path.isfile(full) and not fn.endswith(".setup.json"):
                res.append(os.path.relpath(full, p.dir))
    return res


def lock_path(path, shared, block=True):
    """flock path (created if missing), shared or exclusive; None if not block and it is held.
    The collector removes lock files while holding them, so after the lock is granted the path
    must still name the locked file; otherwise the lock is taken again on the new one."""
    while True:
        f = open(path, "a+")
        try:
            fcntl.flock(f, (fcntl.LOCK_SH if shared else fcntl.LOCK_EX) | (0 if block else fcntl.LOCK_NB))
        except BlockingIOError:
            f.close()
            return None
        try:
            if os.path.samestat(os.fstat(f.fileno()), os.stat(path)):
                return f
        except FileNotFoundError:
            pass
        f.close()


def touch_use(e):
    p = e + ".use"
    try:
        with open(p, "a"):
            pass
        os.utime(p, None)
    except OSError:
        pass


def entry_dir(cache, key):
    return os.path.join(cache, "mods", key[:2], key)


def read_manifest(e):
    out = {}
    with open(os.path.join(e, "MANIFEST.sha256")) as f:
        for line in f:
            h, path = line.rstrip("\n").split("  ", 1)
            out[path] = h
    return out


def restore(ks, cache):
    hit = miss = same = bad = 0
    for mod in ks.modules():
        k = ks.key(mod)
        if k is None:
            continue
        p = ks.pkg_of(mod)
        e = entry_dir(cache, k)
        if not os.path.isfile(os.path.join(e, "MANIFEST.sha256")):
            miss += 1
            continue
        # Shared while copying: the collector never removes an entry being read.
        lk = lock_path(e + ".lock", shared=True)
        try:
            r = restore_one(p, mod, e)
        finally:
            lk.close()
        if r == "miss":
            miss += 1
        elif r == "same":
            same += 1
            touch_use(e)
        elif r == "bad":
            bad += 1
        else:
            hit += 1
            touch_use(e)
    print("asl module cache: restored %d modules, %d already current, %d not cached, %d rejected (%s)" % (hit, same, miss, bad, cache))


def restore_one(p, mod, e):
    """Copy the entry e of mod into p's build (the caller holds e's lock shared). Any failure
    (a file that does not match the manifest, or cannot be read) removes every output of mod, so
    that no copied trace can vouch for an output that was not copied: Lake then builds it."""
    if not os.path.isfile(os.path.join(e, "MANIFEST.sha256")):
        return "miss"
    man = read_manifest(e)
    # tree/<package>/<path relative to the package dir>
    if all(os.path.isfile(os.path.join(p.dir, rel)) and sha_file(os.path.join(p.dir, rel)) == h
           for rel, h in ((r.split("/", 1)[1], h) for r, h in man.items())):
        return "same"
    copied = []
    why = None
    try:
        for r, h in man.items():
            rel = r.split("/", 1)[1]
            src, dst = os.path.join(e, "tree", r), os.path.join(p.dir, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            tmp = dst + ".asl-cache-tmp"
            shutil.copy2(src, tmp)
            if sha_file(tmp) != h:
                os.unlink(tmp)
                why = "a copied file does not match the entry's manifest"
                break
            os.replace(tmp, dst)
            copied.append(dst)
    except OSError as ex:
        why = "cannot copy the entry (%s)" % ex
    if why is None:
        return "hit"
    for d in copied + [os.path.join(p.dir, x) for x in outputs(p, mod)]:
        try:
            os.unlink(d)
        except FileNotFoundError:
            pass
    print("asl module cache: %s: %s; Lake builds it" % (mod, why), file=sys.stderr)
    return "bad"


def closure(ks, roots):
    seen, todo = set(), list(roots)
    while todo:
        m = todo.pop()
        if m in seen or ks.pkg_of(m) is None:
            continue
        seen.add(m)
        src = ks.pkg_of(m).source(m)
        if os.path.exists(src):
            todo += header_imports(src)
    return seen


def publish(ks, cache, roots):
    stored = present = skipped = 0
    mods = closure(ks, roots) if roots else set(ks.modules())
    os.makedirs(os.path.join(cache, "mods"), exist_ok=True)
    for mod in sorted(mods):
        k = ks.key(mod)
        if k is None:
            continue
        p = ks.pkg_of(mod)
        e = entry_dir(cache, k)
        if os.path.isfile(os.path.join(e, "MANIFEST.sha256")):
            present += 1
            continue
        outs = outputs(p, mod)
        trace = os.path.join(p.build(), "lib", "lean", *mod.split(".")) + ".trace"
        olean = os.path.join(p.build(), "lib", "lean", *mod.split(".")) + ".olean"
        if not (os.path.isfile(trace) and os.path.isfile(olean)) or os.path.getmtime(trace) < os.path.getmtime(p.source(mod)):
            skipped += 1
            continue
        os.makedirs(os.path.dirname(e), exist_ok=True)
        with lock_path(e + ".lock", shared=False):
            if os.path.isfile(os.path.join(e, "MANIFEST.sha256")):
                present += 1
                continue
            tmp = tempfile.mkdtemp(prefix=".tmp-", dir=os.path.dirname(e))
            lines = []
            for rel in outs:
                r = p.name + "/" + rel.replace(os.sep, "/")
                dst = os.path.join(tmp, "tree", r)
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                shutil.copy2(os.path.join(p.dir, rel), dst)
                lines.append("%s  %s\n" % (sha_file(dst), r))
            with open(os.path.join(tmp, "MANIFEST.sha256"), "w") as f:
                f.writelines(sorted(lines))
            with open(os.path.join(tmp, "INPUTS.json"), "w") as f:
                json.dump(ks.inputs_of.get(mod), f, sort_keys=True, indent=1)
            os.rename(tmp, e)
            stored += 1
    print("asl module cache: stored %d modules, %d already cached, %d not built (%s)" % (stored, present, skipped, cache))


# ---- eviction (gc) ----

ARMASL_RE = re.compile(r"^[0-9a-f]{32}$")
MOD_RE = re.compile(r"^[0-9a-f]{40}$")


def parse_size(t):
    t = t.strip().upper().rstrip("B").rstrip("I")
    mult = {"K": 1 << 10, "M": 1 << 20, "G": 1 << 30, "T": 1 << 40}
    if t and t[-1] in mult:
        return int(float(t[:-1]) * mult[t[-1]])
    return int(t)


def tree_bytes(p):
    n = 0
    try:
        st = os.lstat(p)
    except FileNotFoundError:
        return 0
    n += st.st_blocks * 512
    if os.path.isdir(p) and not os.path.islink(p):
        for d, dirs, files in os.walk(p):
            for x in dirs + files:
                try:
                    n += os.lstat(os.path.join(d, x)).st_blocks * 512
                except FileNotFoundError:
                    pass
    return n


def last_use(e):
    t = 0.0
    for q in (e + ".use", e):
        try:
            t = max(t, os.lstat(q).st_mtime)
        except FileNotFoundError:
            pass
    return t


class Entry:
    def __init__(self, kind, path, key):
        self.kind, self.path, self.key = kind, path, key
        self.size = tree_bytes(path) + tree_bytes(path + ".use") + tree_bytes(path + ".lock")
        self.used = last_use(path)
        self.refs = set()
        if kind == "mod":
            try:
                with open(os.path.join(path, "INPUTS.json")) as f:
                    inp = json.load(f) or {}
                for _, k in inp.get("imports", []):
                    if isinstance(k, str) and k.startswith("armasl:"):
                        self.refs.add(k[len("armasl:"):])
            except (OSError, ValueError, TypeError):
                pass


def scan(cache):
    out = []
    for n in sorted(os.listdir(cache)) if os.path.isdir(cache) else []:
        q = os.path.join(cache, n)
        if ARMASL_RE.match(n) and os.path.isdir(q) and not os.path.islink(q):
            out.append(Entry("armasl", q, n))
    mods = os.path.join(cache, "mods")
    for sh in sorted(os.listdir(mods)) if os.path.isdir(mods) else []:
        sd = os.path.join(mods, sh)
        if len(sh) != 2 or not os.path.isdir(sd) or os.path.islink(sd):
            continue
        for n in sorted(os.listdir(sd)):
            q = os.path.join(sd, n)
            if MOD_RE.match(n) and os.path.isdir(q) and not os.path.islink(q):
                out.append(Entry("mod", q, n))
    return out


def checkout_armasl_keys(root):
    """The checkout's ArmASL keys: the current one (asl_cache_key.py) and the legacy one that
    scripts/asl.sh still reads (asl_cache_legacy_key)."""
    akey = load_armasl_key(root)
    keys = {akey.sha(akey.canonical(akey.inputs(root)).encode())[:32]}
    pkg = os.path.join(root, "JanusASL")
    try:
        h = hashlib.sha256()
        for f in (os.path.join(pkg, "vendor", "ArmASL.tar.gz.sha256"), os.path.join(root, "lean-toolchain"),
                  os.path.join(pkg, "lakefile.toml"), os.path.join(pkg, "lake-manifest.json"),
                  os.path.join(pkg, "sail", "split_lean.py")):
            with open(f, "rb") as fh:
                h.update(fh.read())
        keys.add(h.hexdigest()[:32])
    except OSError:
        pass
    return keys


def evict(e, cache, cutoff, dry, trash):
    """Remove entry e under its lock (exclusive, without waiting); False if it is in use or was
    used again since the scan."""
    if dry:
        return True
    lk = lock_path(e.path + ".lock", shared=False, block=False)
    if lk is None:
        return False
    try:
        if last_use(e.path) >= cutoff or not os.path.isdir(e.path):
            return False
        if trash[0] is None:
            trash[0] = tempfile.mkdtemp(prefix=".gc-trash-", dir=cache)
        os.rename(e.path, os.path.join(trash[0], "%s-%s" % (e.kind, e.key)))
        for q in (e.path + ".use", e.path + ".lock"):  # under the lock: waiters retry on a new file
            try:
                os.unlink(q)
            except FileNotFoundError:
                pass
        return True
    finally:
        lk.close()


def gc(cache, budget, root=None, grace=3600, dry=False, now=None):
    import time
    now = time.time() if now is None else now
    cutoff = now - grace
    cache = os.path.abspath(cache)
    keep = checkout_armasl_keys(root) if root else set()
    ents = scan(cache)
    total = sum(e.size for e in ents)
    before = total
    trash = [None]
    removed = []

    def drop(e):
        nonlocal total
        if e.used >= cutoff or not evict(e, cache, cutoff, dry, trash):
            return False
        removed.append(e)
        total -= e.size
        ents.remove(e)
        return True

    def unreferenced():
        refs = set().union(*[e.refs for e in ents if e.kind == "mod"]) if ents else set()
        for e in [x for x in ents if x.kind == "armasl" and x.key not in refs and x.key not in keep]:
            drop(e)

    unreferenced()
    if budget is not None:
        for e in sorted([x for x in ents if not (x.kind == "armasl" and x.key in keep)], key=lambda x: x.used):
            if total <= budget:
                break
            drop(e)
        unreferenced()
    # Leftovers of interrupted collections and publishes (older than a day).
    if not dry:
        for d in [cache, os.path.join(cache, "mods")] + [os.path.join(cache, "mods", x) for x in
                                                          (os.listdir(os.path.join(cache, "mods")) if os.path.isdir(os.path.join(cache, "mods")) else [])]:
            if not os.path.isdir(d):
                continue
            for n in os.listdir(d):
                q = os.path.join(d, n)
                if (n.startswith(".gc-trash-") or n.startswith(".tmp-")) and os.path.isdir(q) and q != trash[0]:
                    try:
                        if os.lstat(q).st_mtime < now - 86400:
                            shutil.rmtree(q, ignore_errors=True)
                    except FileNotFoundError:
                        pass
        if trash[0]:
            shutil.rmtree(trash[0], ignore_errors=True)
    def hb(n):
        return "%.1f GiB" % (n / 2**30) if n >= 2**30 else "%.1f MiB" % (n / 2**20)
    print("asl module cache gc: %s %d entries (%s); %s -> %s (budget %s, grace %ds)%s" % (
        "would remove" if dry else "removed", len(removed), hb(sum(e.size for e in removed)), hb(before),
        hb(total), "none" if budget is None else hb(budget), grace, " (dry run)" if dry else ""))
    return removed


def gc_main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="asl_mod_cache.py gc")
    ap.add_argument("cache")
    ap.add_argument("--max", help="size budget (15G, 500M, bytes; 'off' for none)")
    ap.add_argument("--root", help="checkout whose ArmASL entry is always kept")
    ap.add_argument("--grace", type=int, default=3600, help="seconds since the last use or publication that keep an entry")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)
    budget = None if a.max in (None, "off", "none") else parse_size(a.max)
    gc(a.cache, budget, root=a.root, grace=a.grace, dry=a.dry_run)


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    cmd, root = sys.argv[1], sys.argv[2]
    if cmd == "gc":
        gc_main(sys.argv[2:])
        return
    ks = Keys(root)
    if cmd == "keys":
        for m in ks.modules():
            print(m, ks.key(m))
    elif cmd == "show":
        ks.key(sys.argv[3])
        print(json.dumps(ks.inputs_of.get(sys.argv[3]), sort_keys=True, indent=1))
    elif cmd == "restore":
        restore(ks, sys.argv[3])
    elif cmd == "publish":
        # the roots of the JanusASL library (and with --exe, of its executables): the targets
        # `scripts/asl.sh` has just built; their closure is up to date
        roots = [a for a in sys.argv[4:] if not a.startswith("--")]
        cfg = ks.pkgs[0].cfg
        for lib in cfg.get("lean_lib", []):
            if lib.get("name") == "JanusASL":
                roots += lib.get("roots", ["JanusASL"])
        if "--exe" in sys.argv[4:]:
            roots += [e["root"] for e in cfg.get("lean_exe", []) if "root" in e]
        publish(ks, sys.argv[3], roots)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
