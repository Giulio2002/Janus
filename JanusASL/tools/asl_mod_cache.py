#!/usr/bin/env python3
"""Shared per-module build cache for the JanusASL proofs and the Janus framework modules they
import (scripts/asl.sh, ASL_CACHE; docs/ASL.md "Build cache").

    python3 -I JanusASL/tools/asl_mod_cache.py restore REPO_ROOT CACHE [--record FILE]   copy cached builds in
    python3 -I JanusASL/tools/asl_mod_cache.py publish REPO_ROOT CACHE [--exe]
                                    store the builds of the JanusASL library's closure (--exe: and
                                    of its executables'), after `lake build` has built them
    python3 -I JanusASL/tools/asl_mod_cache.py keys    REPO_ROOT         module -> key, one per line
    python3 -I JanusASL/tools/asl_mod_cache.py show    REPO_ROOT MODULE  the canonical inputs of a key
    python3 -I JanusASL/tools/asl_mod_cache.py gc      CACHE --max SIZE [--root REPO_ROOT]
                                    [--grace SECONDS] [--dry-run]
                                    evict entries (see "Eviction" below)
    python3 -I JanusASL/tools/asl_mod_cache.py objkey  REPO_ROOT [arm|jasl]  id of the object entry (below)
    python3 -I JanusASL/tools/asl_mod_cache.py objfiles REPO_ROOT [arm|jasl] its files, NUL-separated, relative
                                    to JanusASL/.lake (nothing if the object set is incomplete)

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

**Compiled objects** (`CACHE/armobj/<id>`, kind `armobj` of scripts/lib/bcache.py; two scopes, `arm` and `jasl`).
The id binds the C content of the scope, the keyed compiler BINARY's content, the ArmASL key (toolchain, flags,
environment incl. CCC_*), the machine and (jasl) the JanusASL lib/exe tables; a store checks that each object's
trace/hash bind to the current C and the keyed compiler (objstage) and recompiles a sample; Lake does not re-check a
restored object, so there is no second check at use time and no kernel replay: see docs/ASL.md "Compiled objects"
(key + HMAC + the nightly reproducibility audit of gate-cachecmp.py).

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

SCHEME = "janusasl-module-cache-v2"
CORE = {"Init", "Std", "Lean", "Lake"}


def load_bcache(root):
    """scripts/lib/bcache.py: the integrity layer (per-user HMAC key, signed manifests)."""
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("bcache", os.path.join(root, "scripts", "lib", "bcache.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


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
        self.bc = load_bcache(self.root)
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
            "toolchain.content": self.akey.toolchain_content(pkgdir), "env": self.akey.env_inputs(),
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


def is_object(rel):
    """A compiled C object (or its .hash/.trace) under ir/: NOT carried by module entries. Module entries are protected
    by the HMAC and file hashes only; a native object needs the armobj entry's staging checks, recompile sample,
    tombstones and the nightly audit (docs/ASL.md "Compiled objects"), so objects travel only there (ASL_OBJ_CACHE=1)."""
    return "/ir/" in rel.replace(os.sep, "/") and ".c.o." in os.path.basename(rel)


def outputs(p, mod, objects=True):
    """The build outputs of mod under p's .lake/build, relative to p.dir (existing files only); objects=False leaves
    out the compiled C objects (what a module entry stores)."""
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
                rel_ = os.path.relpath(full, p.dir)
                if objects or not is_object(rel_):
                    res.append(rel_)
    return res


def open_lock(path):
    """Open (creating, 0600) a lock file without following a symlink; refuse a non-regular or foreign file
    (scripts/lib/bcache.py open_lock; duplicated because the collector runs without a checkout's bcache)."""
    import stat
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
    except OSError as ex:
        raise OSError("cannot open the lock file %s safely (%s)" % (path, "a symbolic link" if ex.errno == 40 else ex.strerror))
    st = os.fstat(fd)
    if not stat.S_ISREG(st.st_mode) or st.st_uid != os.getuid():
        os.close(fd)
        raise OSError("the lock file %s is not a regular file owned by this user" % path)
    return os.fdopen(fd, "r+")


def lock_path(path, shared, block=True):
    """flock path (created if missing), shared or exclusive; None if not block and it is held.
    The collector removes lock files while holding them, so after the lock is granted the path
    must still name the locked file; otherwise the lock is taken again on the new one."""
    while True:
        f = open_lock(path)
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
        os.close(os.open(p, os.O_WRONLY | os.O_CREAT | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600))
        os.utime(p, None, follow_symlinks=False)
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


RESTORED = {}   # absolute path -> SHA-256 of every file this process restored or found current (signed manifest entries)


def restore(ks, cache):
    hit = miss = same = bad = 0
    try:
        ks.bc.hmac_key()
    except ks.bc.CacheError as ex:
        print("asl module cache: %s; not using the cache (Lake builds everything)" % ex, file=sys.stderr)
        return
    # one restorer at a time per tree (lanes of scripts/gate.sh share an isolated tree): the same lock as
    # scripts/lib/bcache.py's fetch, taken in a fixed order, held for the whole restore
    tls = [ks.bc.tree_lock(os.path.join(p.dir, ".lake")) for p in ks.pkgs]
    try:
        hit, miss, same, bad = restore_locked(ks, cache)
    finally:
        for t in reversed(tls):
            t.close()
    print("asl module cache: restored %d modules, %d already current, %d not cached, %d rejected (%s)" % (hit, same, miss, bad, cache))


def restore_locked(ks, cache):
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
        try:
            lk = lock_path(e + ".lock", shared=True)
        except OSError as ex:
            print("asl module cache: %s: %s; Lake builds it" % (mod, ex), file=sys.stderr)
            bad += 1
            continue
        try:
            r = restore_one(ks, p, mod, k, e)
        finally:
            lk.close()
        if r == "miss":
            miss += 1
        elif r == "same":
            same += 1
            touch_use(e)
        elif r == "bad":
            bad += 1
            quarantine(e, cache)
        else:
            hit += 1
            touch_use(e)
    return hit, miss, same, bad


def quarantine(e, cache):
    """Move a rejected entry out of the way (under its exclusive lock, without waiting), so that the
    next publish stores a fresh one. Failing to is harmless: the entry is rejected again."""
    lk = lock_path(e + ".lock", shared=False, block=False)
    if lk is None:
        return
    try:
        if os.path.isdir(e):
            q = tempfile.mkdtemp(prefix=".bad-", dir=os.path.dirname(e))
            os.rename(e, os.path.join(q, "entry"))
            shutil.rmtree(q, ignore_errors=True)
    except OSError:
        pass
    finally:
        lk.close()


def restore_one(ks, p, mod, key, e):
    """Copy the entry e of mod into p's build (the caller holds e's lock shared). The manifest must
    carry a valid HMAC; every copied file is hashed and compared with it. Any failure (no HMAC, a
    wrong one, a file that does not match, cannot be read, or is not a regular file) removes every
    output of mod, so that no copied trace can vouch for an output that was not copied: Lake then
    builds it."""
    bc = ks.bc
    if not os.path.isfile(os.path.join(e, "MANIFEST.sha256")):
        return "miss"
    copied = []
    why = None
    try:
        man = bc.read_signed_manifest("mod", key, e)
        # tree/<package>/<path relative to the package dir>
        # legacy entries carry compiled objects: never restored from here (is_object), only from a verified armobj entry
        rels = {r.split("/", 1)[1]: (r, h) for r, h in man.items() if not is_object(r.split("/", 1)[1])}
        if all(os.path.isfile(os.path.join(p.dir, rel)) and not os.path.islink(os.path.join(p.dir, rel))
               and sha_file(os.path.join(p.dir, rel)) == h for rel, (_, h) in rels.items()):
            for rel, (_, h) in rels.items():
                RESTORED[os.path.join(p.dir, rel)] = h
            return "same"
        for rel, (r, h) in rels.items():
            src, dst = os.path.join(e, "tree", r), os.path.join(p.dir, rel)
            bc._regular(src)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            tmp = bc._tmp_name(dst)
            fd = os.open(src, os.O_RDONLY | os.O_NOFOLLOW)
            with os.fdopen(fd, "rb") as fi, open(tmp, "wb") as fo:
                shutil.copyfileobj(fi, fo, 1 << 20)
            os.chmod(tmp, (os.stat(src).st_mode & 0o111) | 0o644)
            if sha_file(tmp) != h:
                os.unlink(tmp)
                why = "a copied file does not match the entry's manifest"
                break
            os.replace(tmp, dst)
            copied.append(dst)
            RESTORED[dst] = h
    except (OSError, bc.CacheError) as ex:
        why = "entry rejected (%s)" % ex
    if why is None:
        return "hit"
    for d in copied:
        RESTORED.pop(d, None)
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


def entry_present(ks, k, e):
    """A cheap check that an existing entry is worth keeping: its manifest verifies and every file
    exists with the manifest's size class (regular file). Content is verified on every restore."""
    try:
        man = ks.bc.read_signed_manifest("mod", k, e)
        return all(os.path.isfile(os.path.join(e, "tree", r)) and not os.path.islink(os.path.join(e, "tree", r))
                   for r in man)
    except (OSError, ks.bc.CacheError):
        return False


def stamp_mismatch(ks, p, mod):
    """The first output of a Janus module that differs from the framework stamp's pin for it, or None. A tree whose
    framework build is stamped (.lake/janus-framework.ready) must not sign a Janus module that is not the stamped file;
    a tree without a stamp, and files the stamp does not pin, are unconstrained."""
    if p.name != "janus":
        return None
    try:
        with open(os.path.join(p.dir, ".lake", "janus-framework.ready")) as f:
            pins = json.load(f).get("pins")
    except (OSError, ValueError, AttributeError):
        return None
    if not isinstance(pins, dict):
        return None
    lib = os.path.join(".lake", "build", "lib", "lean") + os.sep
    for out in outputs(p, mod):
        if out.startswith(lib):
            want = pins.get(out[len(lib):].replace(os.sep, "/"))
            if want is not None and sha_file(os.path.join(p.dir, out)) != want:
                return out
    return None


def publish(ks, cache, roots):
    stored = present = skipped = 0
    try:
        ks.bc.hmac_key()
    except ks.bc.CacheError as ex:
        print("asl module cache: %s; not storing" % ex, file=sys.stderr)
        return
    mods = closure(ks, roots) if roots else set(ks.modules())
    os.makedirs(os.path.join(cache, "mods"), exist_ok=True)
    for mod in sorted(mods):
        k = ks.key(mod)
        if k is None:
            continue
        p = ks.pkg_of(mod)
        e = entry_dir(cache, k)
        if os.path.isfile(os.path.join(e, "MANIFEST.sha256")) and entry_present(ks, k, e):
            present += 1
            continue
        outs = outputs(p, mod, objects=False)
        trace = os.path.join(p.build(), "lib", "lean", *mod.split(".")) + ".trace"
        olean = os.path.join(p.build(), "lib", "lean", *mod.split(".")) + ".olean"
        if not (os.path.isfile(trace) and os.path.isfile(olean)) or os.path.getmtime(trace) < os.path.getmtime(p.source(mod)):
            skipped += 1
            continue
        bad = stamp_mismatch(ks, p, mod)
        if bad:
            print("asl module cache: %s: %s differs from the framework stamp's pin; not stored" % (mod, bad), file=sys.stderr)
            skipped += 1
            continue
        os.makedirs(os.path.dirname(e), exist_ok=True)
        try:
            xl = lock_path(e + ".lock", shared=False)
        except OSError as ex:
            print("asl module cache: %s: %s; not stored" % (mod, ex), file=sys.stderr)
            skipped += 1
            continue
        with xl:
            if os.path.isdir(e):
                if entry_present(ks, k, e):
                    present += 1
                    continue
                q = tempfile.mkdtemp(prefix=".bad-", dir=os.path.dirname(e))
                os.rename(e, os.path.join(q, "entry"))
                shutil.rmtree(q, ignore_errors=True)
            tmp = tempfile.mkdtemp(prefix=".tmp-", dir=os.path.dirname(e))
            try:
                lines = []
                for rel in outs:
                    r = p.name + "/" + rel.replace(os.sep, "/")
                    dst = os.path.join(tmp, "tree", r)
                    os.makedirs(os.path.dirname(dst), exist_ok=True)
                    shutil.copyfile(os.path.join(p.dir, rel), dst)
                    os.chmod(dst, (os.stat(os.path.join(p.dir, rel)).st_mode & 0o111) | 0o444)
                    lines.append("%s  %s\n" % (sha_file(dst), r))
                data = "".join(sorted(lines)).encode()
                with open(os.path.join(tmp, "MANIFEST.sha256"), "wb") as f:
                    f.write(data)
                with open(os.path.join(tmp, "MANIFEST.hmac"), "w") as f:
                    f.write(ks.bc.mac("mod", k, data) + "\n")
                with open(os.path.join(tmp, "INPUTS.json"), "w") as f:
                    json.dump(ks.inputs_of.get(mod), f, sort_keys=True, indent=1)
                os.rename(tmp, e)
            except BaseException:
                shutil.rmtree(tmp, ignore_errors=True)
                raise
            stored += 1
    print("asl module cache: stored %d modules, %d already cached, %d not built (%s)" % (stored, present, skipped, cache))


# ---- compiled C objects of ArmASL and lean-sail (CACHE/armobj) ----

OBJ_SCHEME = "janusasl-obj-cache-v3"
OBJ_SUFFIXES = (".c.o.export", ".c.o.noexport")


PER_OBJECT = ("jasl", "janus")  # one entry per object (a changed module recompiles only itself); "arm" is one entry


def scope_lake(root, scope):
    """The .lake directory whose build/ir holds the scope's C (JanusASL/.lake)."""
    return os.path.join(root, ".lake") if scope == "janus" else os.path.join(root, "JanusASL", ".lake")


def obj_dirs(lake, scope="arm"):
    """(directory under .lake, filter on the first path component) holding the C of the scope:
    "arm" = ArmASL and Sail (known after `lake build ArmASL`), "jasl" = the JanusASL library (its C is restored with the module entries; the object of a huge proof module,
    e.g. JanusASL.Proofs.Config, costs ~10 min)."""
    if scope == "jasl":
        return [(os.path.join(lake, "build", "ir"), lambda n: n == "JanusASL.c" or n == "JanusASL")]
    if scope == "janus":  # the root package's Janus library (linked into janus-asl-check, janus-audit, janus-decode, ...)
        return [(os.path.join(lake, "build", "ir"), lambda n: n == "Janus.c" or n == "Janus")]
    return [(os.path.join(lake, "build", "ir"), lambda n: n == "ArmASL.c" or n == "ArmASL"),
            (os.path.join(lake, "packages", "Sail", ".lake", "build", "ir"), lambda n: True)]


def obj_c_files(lake, scope="arm"):
    """Emitted C files in scope: {path relative to .lake: sha256 of the content}."""
    out = {}
    for d, ok in obj_dirs(lake, scope):
        if not os.path.isdir(d):
            continue
        for top in sorted(os.listdir(d)):
            if not ok(top):
                continue
            q = os.path.join(d, top)
            cands = [q] if os.path.isfile(q) else [os.path.join(dp, fn) for dp, _, fns in os.walk(q) for fn in fns]
            for full in cands:
                if full.endswith(".c") and os.path.isfile(full) and not os.path.islink(full):
                    out[os.path.relpath(full, lake).replace(os.sep, "/")] = sha_file(full)
    return out


_CC = {}


def obj_compiler(root):
    """(compiler path, SHA-256 of its content, toolchain prefix) of the C compiler Lake runs. The path and prefix are
    the STRINGS `lean --print-prefix` gives (<prefix>/bin/clang; a logged command must equal them: bcache.expected_argv),
    the hash is of the binary's content now. LEAN_CC set: the binary it names, hashed (the id differs) but such objects
    are never published (bcache.keyed_toolchain refuses)."""
    if root in _CC:
        return _CC[root]
    akey = load_armasl_key(root)
    cc = os.environ.get("LEAN_CC")
    pre = subprocess.run(["lean", "--print-prefix"], cwd=os.path.join(root, "JanusASL"), capture_output=True,
                         text=True, timeout=120).stdout.strip()
    p = (shutil.which(cc.split()[0]) or cc.split()[0]) if cc else os.path.join(pre, "bin", "clang")
    try:
        _CC[root] = (p, akey.sha(akey.read(os.path.realpath(p))), pre)
    except OSError:
        sys.exit("asl_mod_cache: cannot read the compiler %s" % p)
    return _CC[root]


def obj_tables(root, scope="jasl"):
    """The lean_lib/lean_exe tables of the scope's package, whole (leancArgs, moreLeancArgs, weakLeancArgs,
    moreLinkArgs, roots, ...): Lake's trace does not cover the weak arguments. lean_lib JanusASL and lean_exe
    janus-asl-check of JanusASL/lakefile.toml."""
    import tomllib
    path = os.path.join(root, "lakefile.toml" if scope == "janus" else os.path.join("JanusASL", "lakefile.toml"))
    with open(path, "rb") as f:
        cfg = tomllib.load(f)
    if scope == "janus":
        return {"lean_lib": [t for t in cfg.get("lean_lib", []) if t.get("name") == "Janus"], "lean_exe": cfg.get("lean_exe", []),
                "package": {k: v for k, v in cfg.items() if k not in ("lean_lib", "lean_exe", "require")}}
    return {"lean_lib": [t for t in cfg.get("lean_lib", []) if t.get("name") == "JanusASL"],
            "lean_exe": [t for t in cfg.get("lean_exe", []) if t.get("name") == "janus-asl-check"]}


_AKEY = {}


def armasl_sha(root):
    if root not in _AKEY:
        akey = load_armasl_key(root)
        _AKEY[root] = akey.sha(akey.canonical(akey.inputs(root)).encode())[:32]
    return _AKEY[root]


def obj_id(root, cs, scope="arm"):
    inp = {"scheme": OBJ_SCHEME, "armasl": armasl_sha(root),
           "machine": platform.machine(), "c": cs, "compiler": obj_compiler(root)[1]}
    sl = [os.path.join(scope_lake(root, scope), "packages", "Sail", n) for n in ("lakefile.toml", "lakefile.lean")]
    inp["sail.lakefile"] = [sha_file(f) if os.path.isfile(f) else None for f in sl]  # the vendored package's build flags (RTOBJ2: not keyed before)
    if scope != "arm":
        inp["scope"] = scope
        inp["tables"] = obj_tables(root, scope)
    return sha_bytes(canonical(inp).encode())[:40]


def obj_units(root, scope, cs=None):
    """[(id, {C: sha})]: one unit for arm, one per C file for the per-object scopes."""
    cs = obj_c_files(scope_lake(root, scope), scope) if cs is None else cs
    if scope in PER_OBJECT:
        return [(obj_id(root, {c: h}, scope), {c: h}) for c, h in sorted(cs.items())]
    return [(obj_id(root, cs, scope), cs)] if cs else []


def obj_files(lake, cs, partial=False):
    """The object triples of every C file in cs; None if one is missing (nothing to publish). partial: a C file
    with no object at all is skipped (JanusASL: Lake compiles only what the executable links), one with an
    incomplete triple still fails."""
    res = []
    for c in sorted(cs):
        found = [c + s[len(".c"):] for s in OBJ_SUFFIXES if os.path.isfile(os.path.join(lake, c + s[len(".c"):]))]
        if partial and not found:
            continue  # jasl scope: only the modules the executable links have an object
        if len(found) != 1:
            return None
        o = found[0]
        trio = [o, o + ".hash", o + ".trace"]
        if not all(os.path.isfile(os.path.join(lake, x)) and not os.path.islink(os.path.join(lake, x)) for x in trio):
            return None
        res += trio
    return res


def load_bcache(root):
    path = os.path.join(root, "scripts", "lib", "bcache.py")
    spec = importlib.util.spec_from_file_location("bcache", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def no_symlink_path(lake, rel):
    """No component of lake/rel (below lake) is a symbolic link."""
    cur = lake
    for part in rel.split("/"):
        cur = os.path.join(cur, part)
        if os.path.islink(cur):
            return False
    return True


def stage_unit(root, scope, lake, ident, cs, stage):
    """Publish-side checks of one entry's objects, then copy them into `stage` (the entry is stored from THAT copy,
    so what is checked is what is signed). Per object (only .c.o.export is cacheable): all files regular, no symlink on
    the way; Lake's file hash of the object equals its .hash and of the C text its .c.hash; the trace's recorded output
    is that object hash and its recorded C hash is the CURRENT one; the logged compile command EQUALS the command built
    from the keyed compiler path and toolchain prefix (bcache.argv_problem); the C is re-hashed now and is the id's. A
    `.cin` record per object and the signed set `armobj.set` ({C: sha256}, the id's C set) are added. Returns the relative
    paths, [] if the unit has no object at all (jasl: Lake compiles only what the executable links); SystemExit on a lie."""
    bc = load_bcache(root)
    cc, _, prefix = obj_compiler(root)
    try:
        kpre, kcc = bc.keyed_toolchain(os.path.join(root, "JanusASL"))
    except bc.CacheError as ex:
        sys.exit("objstage: %s" % ex)
    if cc != kcc or prefix != kpre:
        sys.exit("objstage: the compiler %s is not the toolchain's %s" % (cc, kcc))
    rels = []
    for c in sorted(cs):
        found = [c + s_[len(".c"):] for s_ in OBJ_SUFFIXES if os.path.lexists(os.path.join(lake, c + s_[len(".c"):]))]
        if scope in PER_OBJECT and not found:
            continue
        if len(found) != 1 or not found[0].endswith(".c.o.export"):
            sys.exit("objstage: %s has objects %s (only one .c.o.export is cacheable)" % (c, found))
        o = found[0]
        for x in (o, o + ".hash", o + ".trace", c, c + ".hash"):
            if not no_symlink_path(lake, x) or not os.path.isfile(os.path.join(lake, x)):
                sys.exit("objstage: %s is missing or a symbolic link" % x)
        with open(os.path.join(lake, c), "rb") as f:
            cdata = f.read()
        if sha_bytes(cdata) != cs[c]:
            sys.exit("objstage: %s changed while publishing" % c)
        with open(os.path.join(lake, o), "rb") as f:
            odata = f.read()
        with open(os.path.join(lake, o + ".hash"), "rb") as f:
            ohash_raw = f.read()
        ohash = ohash_raw.decode("ascii", "replace").strip()
        with open(os.path.join(lake, c + ".hash"), "rb") as f:
            chash = f.read().decode("ascii", "replace").strip()
        with open(os.path.join(lake, o + ".trace"), "rb") as f:
            tdata = f.read()
        try:
            outputs, pairs, argv = bc.trace_facts(tdata)
        except Exception as ex:
            sys.exit("objstage: %s: unreadable trace (%s)" % (o, ex))
        if bc.lake_hash(odata) != ohash:
            sys.exit("objstage: %s: the object's bytes do not hash (Lake's hash) to its .hash %s: swapped object" % (o, ohash))
        if bc.lake_hash(cdata, text=True) != chash:
            sys.exit("objstage: %s: the C file does not hash (Lake's text hash) to its .hash %s" % (c, chash))
        why = bc.argv_problem(argv, kcc, kpre, c)
        if why:
            sys.exit("objstage: %s: the logged compile command is not the one Lake logs for the keyed toolchain (%s)" % (o, why))
        if outputs != ohash + ".o":
            sys.exit("objstage: %s: the trace records output %r, the .hash says %r" % (o, outputs, ohash))
        if not any(h == chash and p.replace(os.sep, "/").endswith("/" + c) for p, h in pairs):
            sys.exit("objstage: %s: the trace does not record the hash of the current %s (%s)" % (o, c, chash))
        for x, data in ((o, odata), (o + ".hash", ohash_raw), (o + ".trace", tdata), (o + ".cin", (cs[c] + "\n").encode())):
            d = os.path.join(stage, x)
            os.makedirs(os.path.dirname(d), exist_ok=True)
            with open(d, "wb") as f:
                f.write(data)
            rels.append(x)
    if rels:
        with open(os.path.join(stage, bc.ARMOBJ_SET), "w") as f:
            f.write(canonical(cs))
        rels.append(bc.ARMOBJ_SET)
    return rels


def obj_stage(root, scope, stage, listfile, index=0):
    """CLI/tests: stage unit `index`; prints its id."""
    lake = scope_lake(root, scope)
    units = obj_units(root, scope)
    if not units or index >= len(units):
        sys.exit("objstage: no C files")
    ident, cs = units[index]
    rels = stage_unit(root, scope, lake, ident, cs, stage)
    if not rels:
        sys.exit("objstage: nothing to store")
    with open(listfile, "wb") as f:
        f.write("".join(x + "\0" for x in rels).encode())
    print(ident)


def obj_restore(root, scope, cache):
    """Fetch every unit's entry that exists (HMAC + per-file SHA-256 + allowlist + symlink checks in bcache.fetch)."""
    bc = load_bcache(root)
    lake = scope_lake(root, scope)
    hit = miss = rej = 0
    try:
        bc.hmac_key()
    except bc.CacheError as ex:
        print("asl cache: C objects [%s] not usable (%s); compiling" % (scope, ex))
        return
    for ident, cs in obj_units(root, scope):
        try:
            r = bc.fetch("armobj", cache, ident, lake, want_set=cs)
        except (bc.CacheError, OSError) as ex:
            print("asl cache: the entry for the C objects [%s] %s was REJECTED (%s); compiling" % (scope, ident, ex))
            rej += 1
            continue
        if r == "miss":
            miss += 1
        else:
            hit += 1
    print("asl cache: C objects [%s]: %d restored, %d without entry, %d rejected (%s)" % (scope, hit, miss, rej, cache))


def obj_publish(root, scope, cache, sample):
    """Store every unit that has objects (per-object scopes: one entry each; entries that already verify are kept).
    `sample`: how many of the smallest objects are recompiled (an int or "all"; 0 = none)."""
    bc = load_bcache(root)
    lake = scope_lake(root, scope)
    units = obj_units(root, scope)
    sizes = sorted((sum(os.path.getsize(os.path.join(lake, c)) for c in cs), i) for i, (_, cs) in enumerate(units))
    sample = "all" if sample == "all" else int(sample)
    chosen = set(i for _, i in (sizes if sample == "all" else sizes[:sample]))
    if sample != "all" and sample != 0:  # plus a size-bounded random draw of the rest (bcache.draw_random): the swapped object is not predictable
        unit_size = {i: z for z, i in sizes}
        rest = [(unit_size[i], i, None) for _, i in sizes if i not in chosen]
        chosen |= {i for _, i, _ in bc.draw_random(rest, int(os.environ.get("ASL_OBJ_RECOMPILE_RANDOM", "2")))}
    stored = present = skipped = failed = 0
    bc.clean_stale(cache)
    for i, (ident, cs) in enumerate(units):
        try:
            st = tempfile.mkdtemp(prefix=".objstage-", dir=cache)
        except OSError as ex:
            print("asl cache: C objects [%s] %s not stored: cannot create a staging directory (%s)" % (scope, ident, ex))
            failed += 1
            continue
        try:
            try:
                rels = stage_unit(root, scope, lake, ident, cs, st)
            except SystemExit as ex:
                print("asl cache: C objects [%s] %s not stored: %s" % (scope, ident, ex))
                failed += 1
                continue
            if not rels:
                skipped += 1
                continue
            rc = (lake, "all" if scope in PER_OBJECT else str(sample)) if i in chosen and sample != 0 else None
            try:
                r = bc.store("armobj", cache, ident, st, rels, None, rc, cs)
            except (bc.CacheError, OSError) as ex:
                print("asl cache: C objects [%s] %s not stored: %s" % (scope, ident, ex))
                failed += 1
                continue
            stored += r == "stored"
            present += r == "present"
        finally:
            shutil.rmtree(st, ignore_errors=True)
    print("asl cache: C objects [%s]: stored %d, already cached %d, no object %d, refused %d (%s)" % (scope, stored, present, skipped, failed, cache))


POISONED_RETENTION_DAYS = 30


def obj_audit(root, scope, cache, dry=False):
    """The cold-side audit and eviction (run on a tree whose objects were compiled from source, the nightly's cold
    tree, which is also a full independent recompile of every object, the >1 MB ones included): for every unit of the
    scope whose entry exists in `cache`, the SHA-256 of each cached object must equal the freshly compiled one.
    A difference quarantines the entry for good: under the entry's exclusive lock (an honest republish cannot race the
    rename), a signed tombstone (bcache.write_tombstone) records the poisoned object hashes, then the entry is renamed
    to .poisoned-<id> (removed after POISONED_RETENTION_DAYS; the tombstone stays). `dry` (--dry-run) only reports.
    Exit 3: a poisoned entry. Exit 4 (fail closed): nothing compared, or the share of objects that could not be compared
    (the cache holds an entry for an id whose object the cold build did not link, or an unreadable tombstone left the entry
    unserved and untouched) is above ASL_OBJAUDIT_MAX_UNCHECKED_PCT (default 20). Every compared object that differs is
    exit 3 whatever the coverage. Prints the coverage."""
    bc = load_bcache(root)
    lake = scope_lake(root, scope)
    checked = unchecked = entries = 0
    poisoned = {}
    held = []

    def unverifiable(ident, why):
        print("objaudit: entry %s does not verify (%s)" % (ident, why))
        poisoned[ident] = None

    for ident, cs in obj_units(root, scope):
        e = bc.entry_dir("armobj", cache, ident)
        if not os.path.isdir(e):
            continue
        entries += 1
        lk = None
        if not dry:
            lk = bc.lock_path(e + ".lock", shared=False)  # held until the end: verify and rename are one step
            held.append(lk)
        try:
            man = bc.verify_entry("armobj", cache, ident, cs)
        except bc.TombstoneError as ex:
            print("objaudit: LOUD: %s" % ex)
            unchecked += 1  # not served, not touched, not compared
            continue
        except bc.CacheError as ex:
            unverifiable(ident, ex)
            continue
        for rel, h in sorted(man.items()):
            if not rel.endswith(".c.o.export"):
                continue
            fresh = os.path.join(lake, rel)
            if not os.path.isfile(fresh) or os.path.islink(fresh):
                unchecked += 1
                print("objaudit: %s of entry %s has no freshly compiled counterpart (not linked in this build?)" % (rel, ident))
                continue
            checked += 1
            if sha_file(fresh) != h:
                poisoned.setdefault(ident, {})[rel] = h
                print("objaudit: POISONED %s: %s differs from the freshly compiled object" % (ident, rel))
    for ident, objs in sorted(poisoned.items()):
        e = bc.entry_dir("armobj", cache, ident)
        q = os.path.join(os.path.dirname(e), ".poisoned-" + ident)
        if dry:
            print("objaudit: (dry run) would quarantine %s" % ident)
            continue
        if objs:
            bc.write_tombstone(cache, ident, objs)
        shutil.rmtree(q, ignore_errors=True)
        if os.path.isdir(e):
            os.rename(e, q)
        print("objaudit: quarantined %s (tombstone %s)" % (q, "written" if objs else "not possible: unverifiable entry"))
    for lk in held:
        lk.close()
    if not dry:
        import time
        d = os.path.join(cache, "armobj")
        for n in (os.listdir(d) if os.path.isdir(d) else []):
            q = os.path.join(d, n)
            if n.startswith(".poisoned-") and os.path.isdir(q) and not os.path.islink(q) \
                    and time.time() - os.lstat(q).st_mtime > POISONED_RETENTION_DAYS * 86400:
                shutil.rmtree(q, ignore_errors=True)
    total = checked + unchecked
    pct = 100.0 * unchecked / total if total else 100.0
    print("objaudit [%s]: %d entries, coverage %d of %d objects compared (%.0f%%), %d not comparable (%.0f%%), %d poisoned" % (
        scope, entries, checked, total, 100.0 - pct, unchecked, pct, len(poisoned)))
    if poisoned:
        return 3
    cap = float(os.environ.get("ASL_OBJAUDIT_MAX_UNCHECKED_PCT", "20"))
    if checked == 0 or pct > cap:  # fail closed
        print("objaudit [%s]: INCOMPLETE: %s" % (scope, "NOTHING WAS COMPARED" if checked == 0 else
              "%.0f%% of the objects could not be compared (limit %.0f%%)" % (pct, cap)))
        return 4
    return 0


def obj_main(cmd, root, scope="arm", extra=()):
    lake = scope_lake(root, scope)
    if scope not in ("arm", "jasl", "janus"):
        sys.exit("asl_mod_cache: unknown object scope %r" % scope)
    if cmd == "objstage":
        obj_stage(root, scope, extra[0], extra[1], int(extra[2]) if len(extra) > 2 else 0)
        return
    if cmd == "objrestore":
        obj_restore(root, scope, extra[0])
        return
    if cmd == "objaudit":
        sys.exit(obj_audit(root, scope, extra[0], dry="--dry-run" in extra))
    if cmd == "objpublish":
        obj_publish(root, scope, extra[0], extra[1] if len(extra) > 1 else "3")
        return
    cs = obj_c_files(lake, scope)
    if not cs:
        sys.exit(1)
    if cmd == "objkey":
        for ident, _ in obj_units(root, scope, cs):
            print(ident)
    else:
        fl = obj_files(lake, cs, partial=(scope in PER_OBJECT))
        if not fl:
            sys.exit(1)
        sys.stdout.write("".join(x + "\0" for x in fl))


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
    sail = os.path.join(cache, "sail")
    for n in sorted(os.listdir(sail)) if os.path.isdir(sail) and not os.path.islink(sail) else []:
        q = os.path.join(sail, n)
        if MOD_RE.match(n) and os.path.isdir(q) and not os.path.islink(q):
            out.append(Entry("sail", q, n))
    objs = os.path.join(cache, "armobj")
    for n in sorted(os.listdir(objs)) if os.path.isdir(objs) and not os.path.islink(objs) else []:
        q = os.path.join(objs, n)
        if MOD_RE.match(n) and os.path.isdir(q) and not os.path.islink(q):
            out.append(Entry("armobj", q, n))
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
    """The checkout's ArmASL key (asl_cache_key.py). The pre-HMAC keys are not kept: nothing reads
    their entries any more."""
    akey = load_armasl_key(root)
    return {akey.sha(akey.canonical(akey.inputs(root)).encode())[:32]}


def evict(e, cache, cutoff, dry, trash):
    """Remove entry e under its lock (exclusive, without waiting); False if it is in use or was
    used again since the scan."""
    if dry:
        return True
    try:
        lk = lock_path(e.path + ".lock", shared=False, block=False)
    except OSError:
        return False  # an unsafe lock path (a symlink, a foreign file): leave the entry alone
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
        for d in [cache, os.path.join(cache, "sail"), os.path.join(cache, "armobj"), os.path.join(cache, "mods")] + [os.path.join(cache, "mods", x) for x in
                                                          (os.listdir(os.path.join(cache, "mods")) if os.path.isdir(os.path.join(cache, "mods")) else [])]:
            if not os.path.isdir(d):
                continue
            for n in os.listdir(d):
                q = os.path.join(d, n)
                if (n.startswith((".gc-trash-", ".tmp-", ".bad-"))) and os.path.isdir(q) and q != trash[0]:
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
    if cmd in ("objkey", "objfiles", "objstage", "objrestore", "objpublish", "objaudit"):
        obj_main(cmd, root, sys.argv[3] if len(sys.argv) > 3 else "arm", sys.argv[4:])
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
        # --record FILE: the files restored (or found current) from HMAC-verified entries, with their SHA-256, for
        # scripts/lib/restamp.py (a record is written even when empty)
        if "--record" in sys.argv[4:]:
            rec = sys.argv[sys.argv.index("--record") + 1]
            # signed (HMAC, domain "restamp", bound to this tree) so restamp.py cannot be fed a forged record; written
            # with O_EXCL|O_NOFOLLOW at 0600 under a name nobody else can have planted, then renamed into place
            doc = json.dumps({"files": RESTORED, "mac": ks.bc.record_mac(root, RESTORED)}, sort_keys=True).encode()
            tmp = rec + ".tmp%d" % os.getpid()
            fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
            try:
                with os.fdopen(fd, "wb") as f:
                    f.write(doc)
                    f.flush()
                    os.fsync(f.fileno())
                os.replace(tmp, rec)
            except BaseException:
                try:
                    os.unlink(tmp)
                except OSError:
                    pass
                raise
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
