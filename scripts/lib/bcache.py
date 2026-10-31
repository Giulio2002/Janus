#!/usr/bin/env python3
"""Integrity layer of the content-addressed build caches (scripts/asl.sh, scripts/oracle-sail.sh,
JanusASL/tools/asl_mod_cache.py; docs/SOUNDNESS.md "Build caches").

A cache entry is a directory
    <entry>/tree/<relative path>      the produced files (read-only copies)
    <entry>/MANIFEST.sha256           "<sha256>  <relative path>" per file, sorted
    <entry>/MANIFEST.hmac             HMAC-SHA256 under the per-user key over (kind, id, manifest)
    <entry>/INPUTS.json               (optional) the canonical inputs of the key, for humans
next to <entry>.lock (flock) and <entry>.use (last restore, the collector's LRU stamp).

The entry's name is the content key (a hash of every input of the build). Reading an entry
(`fetch`) takes the lock shared, verifies the HMAC of the manifest, then copies each file named by
the manifest into the consumer's tree and checks the SHA-256 of the COPY against the manifest
(so a file changed in the cache at any moment before or during the copy is caught, and the cache
itself is never the consumer's working copy). Any problem (no HMAC, wrong HMAC, a missing,
altered, non-regular or extra-linked file, a path that escapes the destination) removes what was
copied and reports "rejected": the caller builds from source. Nothing in this file can turn a
rejected or missing entry into a pass.

Writing (`store`) builds the entry in a temporary directory next to it, signs it, and renames it
into place under the entry's exclusive lock, so a reader sees all of an entry or none. An existing
entry is kept only if it verifies completely (HMAC and every file); otherwise it is quarantined
and replaced.

    bcache.py fetch  KIND CACHE ID DEST [--clean-glob G ...]   0 hit/current, 2 miss, 3 rejected
    bcache.py store  KIND CACHE ID SRC [--inputs FILE] [--c-root LAKE --recompile N|all] < NUL-separated relative paths of SRC
                      (armobj: an existing valid entry is replaced if recompiling N of its objects from the C under
                      LAKE gives other bytes: a poisoned entry cannot stay)
    bcache.py verify KIND CACHE ID [--c-root LAKE --recompile N|all]   0 valid, 2 miss, 3 invalid / POISONED
    bcache.py prune-armasl LAKEDIR MODEL_ARMASL_DIR             drop built ArmASL modules the current model lacks
    bcache.py key-path                                          where the per-user key lives

KIND is armasl (CACHE/<id>), sail (CACHE/sail/<id>), mod (CACHE/mods/<id[:2]>/<id>) or armobj (CACHE/armobj/<id>;
only build/ir/**.c.o.* files are allowed in it, checked at store, fetch and verify).
The HMAC key: $JANUS_CACHE_KEY_DIR/asl-cache.key, default ~/.cache/janus/asl-cache-key/asl-cache.key (32 random
bytes, mode 0600, directory 0700, ours, not a symlink; created atomically on first use). When it
cannot be read or created safely, the cache is not used at all (exit 4: the caller builds).
"""
import errno
import fcntl
import hashlib
import hmac
import json
import shlex
import subprocess
import os
import re
import shutil
import stat
import sys
import tempfile

SCHEME = b"janus-build-cache-hmac-v1"
EX_MISS, EX_REJECT, EX_NOKEY = 2, 3, 4


class CacheError(Exception):
    pass


class Inconclusive(CacheError):
    """A recompile that could not be carried out (no C, a crash, a timeout, a missing tool): neither a match nor a
    mismatch. It never counts as a pass and never destroys an existing entry (a store that meets it stops)."""


def sha_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ---- the per-user key ----

def key_dir():
    d = os.environ.get("JANUS_CACHE_KEY_DIR")
    if d:
        return d
    return os.path.join(os.environ.get("XDG_CACHE_HOME") or os.path.join(os.path.expanduser("~"), ".cache"), "janus", "asl-cache-key")


def key_path():
    return os.path.join(key_dir(), "asl-cache.key")


def _private(path, want_dir):
    st = os.lstat(path)
    if stat.S_ISLNK(st.st_mode):
        raise CacheError("%s is a symbolic link" % path)
    if want_dir and not stat.S_ISDIR(st.st_mode):
        raise CacheError("%s is not a directory" % path)
    if not want_dir and not stat.S_ISREG(st.st_mode):
        raise CacheError("%s is not a regular file" % path)
    if st.st_uid != os.getuid():
        raise CacheError("%s is not owned by this user" % path)
    if st.st_mode & 0o077:
        raise CacheError("%s is accessible by group or others (mode %04o)" % (path, st.st_mode & 0o777))
    return st


def hmac_key():
    d, p = key_dir(), key_path()
    try:
        os.makedirs(d, mode=0o700, exist_ok=True)
        _private(d, True)
        try:
            _private(p, False)
        except FileNotFoundError:
            k = os.urandom(32)
            fd, tmp = tempfile.mkstemp(prefix=".key.tmp-", dir=d)
            try:
                os.fchmod(fd, 0o600)
                os.write(fd, k)
                os.close(fd)
                try:
                    os.link(tmp, p)  # another process may have created it meanwhile: keep the first
                except FileExistsError:
                    pass
            finally:
                try:
                    os.unlink(tmp)
                except FileNotFoundError:
                    pass
            _private(p, False)
        fd = os.open(p, os.O_RDONLY | os.O_NOFOLLOW)
        with os.fdopen(fd, "rb") as f:
            b = f.read()
    except (OSError, CacheError) as ex:
        raise CacheError("cache key unusable: %s" % ex)
    if len(b) != 32:
        raise CacheError("cache key %s has %d bytes, not 32" % (p, len(b)))
    return b


def mac(kind, ident, manifest_bytes):
    return hmac.new(hmac_key(), SCHEME + b"\0" + kind.encode() + b"\0" + ident.encode() + b"\0" + manifest_bytes,
                    hashlib.sha256).hexdigest()


def record_bytes(files):
    """Canonical bytes of a restamp record (path -> SHA-256 of the files a module-cache restore copied)."""
    import json
    return json.dumps(files, sort_keys=True, separators=(",", ":")).encode()


def record_mac(tree, files):
    """HMAC (domain "restamp", bound to the tree root) over a restamp record; same per-user key as the cache."""
    return mac("restamp", os.path.realpath(tree), record_bytes(files))


# ---- layout and locks ----

def entry_dir(kind, cache, ident):
    if not ident or any(c not in "0123456789abcdef" for c in ident):
        raise CacheError("bad cache id %r" % ident)
    if kind == "armasl":
        return os.path.join(cache, ident)
    if kind == "sail":
        return os.path.join(cache, "sail", ident)
    if kind == "mod":
        return os.path.join(cache, "mods", ident[:2], ident)
    if kind == "armobj":  # the compiled C objects (.c.o.export + .hash + .trace) of ArmASL and lean-sail
        return os.path.join(cache, "armobj", ident)
    raise CacheError("unknown kind %r" % kind)


# Per-kind path allowlist. An armobj entry may hold only the compiled C objects Lake writes under build/ir (and its
# Sail twin), each with its .hash/.trace and the .cin record of the C it was compiled from: never an .olean, a
# script or anything else (an entry is HMAC-signed by whoever publishes it, so what it may overwrite is limited here,
# at store AND at fetch AND at verify).
ARMOBJ_SET = "armobj.set"  # signed record of the id's C files {C: sha256}: the entry's file set is bound to it
ARMOBJ_RE = re.compile(r"^(build/ir|packages/Sail/\.lake/build/ir)/[A-Za-z0-9_.+\-]+(/[A-Za-z0-9_.+\-]+)*\.c\.o\.(export|noexport)(\.hash|\.trace|\.cin)?$")


def check_paths(kind, rels):
    if kind == "armobj":
        for r in rels:
            if r != ARMOBJ_SET and not ARMOBJ_RE.match(r):
                raise CacheError("path %r is not allowed in an armobj entry" % r)


def check_armobj_set(tree, man, want_set=None):
    """An armobj entry holds exactly what its id's C set allows: the signed `armobj.set` ({C: sha256}, equal to the
    caller's own C set when given, which is how the file set is bound to the id the caller derived from its tree), the
    objects `<C>.o.export` (+ .hash/.trace/.cin) of those C files and nothing else; each .cin equals the set's hash."""
    if ARMOBJ_SET not in man:
        raise CacheError("the armobj entry has no %s" % ARMOBJ_SET)
    try:
        with open(os.path.join(tree, ARMOBJ_SET), "rb") as f:
            st = json.loads(f.read().decode("utf-8"))
    except (OSError, ValueError) as ex:
        raise CacheError("unreadable %s (%s)" % (ARMOBJ_SET, ex))
    if not isinstance(st, dict) or not st or not all(isinstance(k, str) and isinstance(v, str) and len(v) == 64 for k, v in st.items()):
        raise CacheError("malformed %s" % ARMOBJ_SET)
    if want_set is not None and st != want_set:
        raise CacheError("the entry's C set is not the one of this id")
    allowed = {}
    for c in st:
        if not c.endswith(".c"):
            raise CacheError("%s lists %r, not a C file" % (ARMOBJ_SET, c))
        o = c + ".o.export"
        for x in (o, o + ".hash", o + ".trace", o + ".cin"):
            allowed[x] = c
    for r in man:
        if r != ARMOBJ_SET and r not in allowed:
            raise CacheError("path %r is not an object of the id's C set" % r)
    for r, c in allowed.items():
        if r.endswith(".cin") and r in man:
            try:
                with open(os.path.join(tree, r)) as f:
                    if f.read().strip() != st[c]:
                        raise CacheError("%s does not record the C hash of the set" % r)
            except OSError as ex:
                raise CacheError("unreadable %s (%s)" % (r, ex))
    return st


def tomb_path(cache, ident):
    return os.path.join(cache, "armobj", ".tombstone-" + ident)


def write_tombstone(cache, ident, objects):
    """A signed, durable record that an entry of this id was found poisoned: {object path: sha256}. Fetch, verify and
    store refuse any entry of the id that carries one of those object hashes, wherever the entry directory came from."""
    data = json.dumps({"id": ident, "objects": objects}, sort_keys=True, separators=(",", ":")).encode()
    doc = json.dumps({"data": data.decode(), "mac": mac("tombstone", ident, data)}).encode()
    p = tomb_path(cache, ident)
    fd, tmp = tempfile.mkstemp(prefix=".tomb.tmp-", dir=os.path.dirname(p))
    with os.fdopen(fd, "wb") as f:
        f.write(doc)
    os.replace(tmp, p)


def check_tombstone(cache, ident, man):
    p = tomb_path(cache, ident)
    if not os.path.lexists(p):
        return
    try:
        with open(p, "rb") as f:
            doc = json.loads(f.read().decode("utf-8"))
        data = doc["data"].encode()
        if not hmac.compare_digest(doc["mac"], mac("tombstone", ident, data)):
            raise ValueError("bad MAC")
        t = json.loads(data.decode())
        if t["id"] != ident:
            raise ValueError("another id")
        bad = set(t["objects"].values())
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as ex:
        raise CacheError("the quarantine tombstone of %s is unreadable or forged (%s): the id stays unusable" % (ident, ex))
    if man is not None and any(h in bad for r, h in man.items() if r.endswith(".c.o.export")):
        raise CacheError("the entry carries bytes that were quarantined as poisoned (tombstone)")


def open_lock(path):
    """Open (creating, mode 0600) a lock file without following a symlink, and refuse anything that is not a
    regular file owned by this user: a lock path that someone replaced by a symlink (to be created or truncated
    elsewhere) or by another user's file is an error, never followed."""
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
    except OSError as ex:
        raise CacheError("cannot open the lock file %s safely (%s)" % (path, "a symbolic link" if ex.errno == errno.ELOOP else ex.strerror))
    st = os.fstat(fd)
    if not stat.S_ISREG(st.st_mode) or st.st_uid != os.getuid():
        os.close(fd)
        raise CacheError("the lock file %s is not a regular file owned by this user" % path)
    return os.fdopen(fd, "r+")


def lock_path(path, shared, block=True):
    """flock `path` (created if missing). The collector removes lock files while holding them, so
    after the lock is granted the path must still name the locked file; otherwise retry."""
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


# ---- manifests ----

def parse_manifest(data):
    """{relative path: sha256}; rejects any path that is absolute, has .. or empty parts, or a
    malformed line."""
    out = {}
    for line in data.decode("utf-8").split("\n"):
        if not line:
            continue
        h, sep, path = line.partition("  ")
        if not sep or len(h) != 64 or any(c not in "0123456789abcdef" for c in h):
            raise CacheError("malformed manifest line")
        parts = path.split("/")
        if path.startswith("/") or any(p in ("", ".", "..") for p in parts) or "\0" in path:
            raise CacheError("unsafe path in manifest: %r" % path)
        if path in out:
            raise CacheError("duplicate path in manifest: %r" % path)
        out[path] = h
    return out


def read_signed_manifest(kind, ident, e, want_sha=None):  # noqa: allowlist applied below
    """The entry's manifest, if its HMAC is valid (and, when want_sha is given, its SHA-256 is exactly that: the
    pin of scripts/lib/modelpin.py binds an entry to one manifest); CacheError otherwise."""
    try:
        with open(os.path.join(e, "MANIFEST.sha256"), "rb") as f:
            data = f.read()
        with open(os.path.join(e, "MANIFEST.hmac"), "r") as f:
            tag = f.read().strip()
    except OSError as ex:
        raise CacheError("no signed manifest (%s)" % ex.strerror)
    if not hmac.compare_digest(tag, mac(kind, ident, data)):
        raise CacheError("the manifest's HMAC does not verify")
    if want_sha is not None and hashlib.sha256(data).hexdigest() != want_sha:
        raise CacheError("the manifest is not the pinned one")
    man = parse_manifest(data)
    check_paths(kind, man)
    return man


def _regular(p):
    st = os.lstat(p)
    if not stat.S_ISREG(st.st_mode):
        raise CacheError("%s is not a regular file" % p)
    return st


def verify_entry(kind, cache, ident, want_set=None):
    """Verify an entry in place (HMAC and the SHA-256 of every file). Returns the manifest."""
    e = entry_dir(kind, cache, ident)
    man = read_signed_manifest(kind, ident, e)
    if kind == "armobj":
        check_tombstone(cache, ident, man)
    for rel, h in man.items():
        p = os.path.join(e, "tree", rel)
        try:
            _regular(p)
            ok = sha_file(p) == h
        except OSError:
            raise CacheError("missing file %s" % rel)
        if not ok:
            raise CacheError("file %s does not match the manifest" % rel)
    if kind == "armobj":
        check_armobj_set(os.path.join(e, "tree"), man, want_set)
    return man


# ---- fetch ----

def _under(dest, rel):
    p = os.path.normpath(os.path.join(dest, rel))
    if not (p + os.sep).startswith(os.path.normpath(dest) + os.sep):
        raise CacheError("path escapes the destination: %r" % rel)
    return p


def _safe_dst(dest, rel):
    """dest/rel after lstat of every component below dest: a symbolic link (or a non-directory) on the way is
    refused, never followed (an entry must not write through build -> /etc). Missing components are fine."""
    p = _under(dest, rel)
    cur = os.path.normpath(dest)
    for part in os.path.relpath(p, cur).split(os.sep):
        cur = os.path.join(cur, part)
        try:
            st = os.lstat(cur)
        except FileNotFoundError:
            return p
        if stat.S_ISLNK(st.st_mode):
            raise CacheError("destination component %s is a symbolic link" % cur)
        if cur != p and not stat.S_ISDIR(st.st_mode):
            raise CacheError("destination component %s is not a directory" % cur)
    return p


def _same(dest, man):
    for rel, h in man.items():
        p = _safe_dst(dest, rel)
        try:
            st = os.lstat(p)
            if not stat.S_ISREG(st.st_mode) or sha_file(p) != h:
                return False
        except OSError:
            return False
    return True


TREE_LOCK = ".bcache-tree.lock"


def tree_lock(dest):
    """Exclusive flock on a materialisation target (a directory such as <pkg>/.lake), held for a whole
    fetch/verify/materialise sequence: lanes that share a tree (scripts/gate.sh's isolated trees) take turns, and
    a later one finds the earlier one's finished work (and verifies it) instead of racing on its files. The lock
    file is never removed. It serialises *fetchers* (this module and asl_mod_cache.py restore) only: it does not
    stop a concurrent `lake` build writing into the same tree. Callers must not run lake and a fetch on one tree
    at once; scripts/gate.sh keeps the lanes that share an isolated tree from doing so."""
    os.makedirs(dest, exist_ok=True)
    f = open_lock(os.path.join(dest, TREE_LOCK))
    fcntl.flock(f, fcntl.LOCK_EX)
    return f


def _tmp_name(dst):
    """A name no other process (or thread) can also pick: pid + random, next to dst."""
    return "%s.bcache-tmp.%d.%s" % (dst, os.getpid(), os.urandom(6).hex())


def fetch(kind, cache, ident, dest, clean_globs=(), want_sha=None, want_set=None):
    """Copy the verified entry into dest. Returns "hit", "current" (dest already holds exactly the entry's
    files), "miss", or raises CacheError (rejected).

    The whole sequence runs under dest's tree lock. It is two-phase: phase 1 copies every file to a unique
    temporary name beside its destination and checks the SHA-256 of each copy against the signed manifest;
    only when all of them verify does phase 2 rename them into place. A rejected entry therefore leaves dest
    exactly as it was (only the temporaries are removed), a fetch killed in phase 1 leaves only temporaries
    (the next fetch removes them), and one killed in phase 2 leaves a mix of old and new files that the next
    fetch sees as not 'current' and repairs. clean_globs is accepted for compatibility and unused."""
    e = entry_dir(kind, cache, ident)
    if not os.path.isfile(os.path.join(e, "MANIFEST.sha256")):
        return "miss"
    tl = tree_lock(dest)
    try:
        lk = lock_path(e + ".lock", shared=True)
        try:
            if not os.path.isfile(os.path.join(e, "MANIFEST.sha256")):
                return "miss"
            man = read_signed_manifest(kind, ident, e, want_sha)
            if kind == "armobj":  # the file set must be the id's: tombstone, then the signed C set
                check_tombstone(cache, ident, man)
                check_armobj_set(os.path.join(e, "tree"), man, want_set)
                man = {k: v for k, v in man.items() if k != ARMOBJ_SET}
            touch_use(e)
            _sweep_temps(dest, man)
            if _same(dest, man):
                prune_stale(kind, dest, man)
                return "current"
            staged = []
            try:
                for rel, h in sorted(man.items()):
                    src = os.path.join(e, "tree", rel)
                    _regular(src)
                    dst = _safe_dst(dest, rel)
                    os.makedirs(os.path.dirname(dst), exist_ok=True)
                    tmp = _tmp_name(dst)
                    staged.append((tmp, dst))
                    d = hashlib.sha256()
                    fd = os.open(src, os.O_RDONLY | os.O_NOFOLLOW)
                    with os.fdopen(fd, "rb") as fi, open(tmp, "wb") as fo:
                        for chunk in iter(lambda: fi.read(1 << 20), b""):
                            d.update(chunk)
                            fo.write(chunk)
                    if d.hexdigest() != h:
                        raise CacheError("file %s does not match the manifest" % rel)
                    shutil.copymode(src, tmp)
                    os.chmod(tmp, os.stat(tmp).st_mode | 0o200)  # the consumer's copy is writable
            except (OSError, CacheError) as ex:
                for tmp, _ in staged:
                    try:
                        os.unlink(tmp)
                    except OSError:
                        pass
                raise CacheError(str(ex))
            # phase 2: every file is verified; rename into place (a rename cannot fail on content)
            for tmp, dst in staged:
                os.replace(tmp, dst)
            prune_stale(kind, dest, man)
            return "hit"
        finally:
            lk.close()
    finally:
        tl.close()


def stale_modules(kind, dest, man):
    """Files in dest that belong to a module the entry does not contain: for an armasl entry, anything under
    build/lib/lean/ArmASL/ and build/ir/ArmASL/ whose module stem (the name up to its first dot) is not a stem of
    the entry. Such files are leftovers of an OLDER model split (more or other parts): Lake never touches a module
    nothing imports, and a replay that enumerates the directory (leanchecker) would load them next to the current
    parts and fail (J1 gate, ArmASL.Part37 vs Part20). Strictly bounded to those two directories and to whole
    modules: a file of a module the entry does have (a C object a later exe build added) is left alone."""
    if kind != "armasl":
        return []
    out = []
    for sub in ("build/lib/lean/ArmASL", "build/ir/ArmASL"):
        have = {os.path.basename(r).split(".")[0] for r in man if r.startswith(sub + "/") and r.count("/") == sub.count("/") + 1}
        root = os.path.join(dest, sub)
        try:
            names = os.listdir(root)
        except OSError:
            continue
        for n in names:
            q = os.path.join(root, n)
            if n.split(".")[0] not in have and (os.path.isfile(q) or os.path.islink(q)):
                out.append(q)
    return out


def prune_armasl(lake, model_dir):
    """Remove built ArmASL modules (build/lib/lean/ArmASL/*, build/ir/ArmASL/*) whose module is not a source file
    of the current model (model_dir holds its ArmASL/*.lean). For a seed copied from another build."""
    have = {f.split(".")[0] for f in os.listdir(model_dir) if f.endswith(".lean")}
    n = 0
    for sub in ("build/lib/lean/ArmASL", "build/ir/ArmASL"):
        root = os.path.join(lake, sub)
        try:
            names = os.listdir(root)
        except OSError:
            continue
        for x in names:
            q = os.path.join(root, x)
            if x.split(".")[0] not in have and (os.path.isfile(q) or os.path.islink(q)):
                os.unlink(q)
                n += 1
    return n


def prune_stale(kind, dest, man):
    for q in stale_modules(kind, dest, man):
        try:
            os.unlink(q)
        except OSError:
            pass


def _sweep_temps(dest, man):
    """Remove leftover temporaries of killed materialisers next to the manifest's files (under the tree lock)."""
    seen = set()
    for rel in man:
        d = os.path.dirname(_safe_dst(dest, rel))
        if d in seen:
            continue
        seen.add(d)
        try:
            names = os.listdir(d)
        except OSError:
            continue
        for n in names:
            if ".bcache-tmp." in n:
                try:
                    os.unlink(os.path.join(d, n))
                except OSError:
                    pass


# ---- compiled-object entries (armobj): the trace's compile command, and recompiling to audit an entry ----

def trace_facts(data):
    """(output hash, [(path, hash) of the traced inputs], compile argv or None) of a Lake `.c.o.*.trace`."""
    t = json.loads(data.decode("utf-8"))
    outputs = t.get("outputs")
    pairs = []

    def walk(x):
        if isinstance(x, list):
            if len(x) == 2 and isinstance(x[0], str) and isinstance(x[1], str):
                pairs.append((x[0], x[1]))
            for y in x:
                walk(y)

    walk(t.get("inputs", []))
    argv = None
    for m in t.get("log", []):
        msg = m.get("message", "") if isinstance(m, dict) else ""
        if msg.startswith(".> ") and " -c " in msg and " -o " in msg:
            argv = shlex.split(msg[3:])
            break
    return outputs, pairs, argv



# ---- Lake's own hashes, reimplemented (RTOBJ2): Hash.ofByteArray = mixHash 1723 (MurmurHash64A(bytes, seed 11)) ----
_M64 = (1 << 64) - 1


def _murmur64a(data, seed=11):
    m, r, n = 0xc6a4a7935bd1e995, 47, len(data)
    h = (seed ^ (n * m)) & _M64
    for i in range(n // 8):
        k = int.from_bytes(data[8 * i:8 * i + 8], "little")
        k = (k * m) & _M64
        k ^= k >> r
        k = (k * m) & _M64
        h ^= k
        h = (h * m) & _M64
    tail = data[n - (n & 7):]
    if tail:
        h ^= int.from_bytes(tail, "little")
        h = (h * m) & _M64
    h ^= h >> r
    h = (h * m) & _M64
    h ^= h >> r
    return h


def lake_hash(data, text=False):
    """Lake's hash of a file's bytes (16 lowercase hex digits): what `X.c.o.export.hash` holds (binary) and what
    `X.c.hash` holds (text: CRLF -> LF first). Checked against Lake's own files on a real tree."""
    if text:
        data = data.replace(b"\r\n", b"\n")
    k = _murmur64a(data)
    m = 0xc6a4a7935bd1e995
    k = (k * m) & _M64
    k ^= k >> 47
    k ^= m
    return "%016x" % (((1723 ^ k) * m) & _M64)


# ---- the logged compile command is DATA from the publisher: it must EQUAL the command built from keyed values ----
BRACKET = "-fbracket-depth=100000"  # the one extra flag JanusASL/lakefile.toml gives ArmASL and the janus-asl-check root


def keyed_toolchain(pkgdir):
    """(prefix, clang path) of the toolchain `lean` resolves to in pkgdir: `lean --print-prefix` and <prefix>/bin/clang,
    as STRINGS (the argv of a logged command must equal them, no realpath indirection). CacheError (Inconclusive) when
    LEAN_CC is set (builds with another compiler are not cacheable here), when lean does not answer, or when the
    toolchain's own directories are symlinks (toolchain_content hashes files, not what a link points to)."""
    if os.environ.get("LEAN_CC"):
        raise Inconclusive("LEAN_CC is set: objects built with another compiler are neither published nor recompiled")
    try:
        pre = subprocess.run(["lean", "--print-prefix"], cwd=pkgdir, capture_output=True, text=True, timeout=120,
                             stdin=subprocess.DEVNULL).stdout.strip()
    except (OSError, subprocess.SubprocessError) as ex:
        raise Inconclusive("lean --print-prefix did not run (%s)" % ex)
    if not pre or not os.path.isabs(pre) or os.path.realpath(pre) != pre:
        raise CacheError("toolchain prefix %r is not an absolute, symlink-free path" % pre)
    for d in ("", "bin", "include", "include/clang", "include/lean"):
        q = os.path.join(pre, d) if d else pre
        if os.path.islink(q) or not os.path.isdir(q):
            raise CacheError("toolchain directory %s is a symlink or missing" % q)
    cc = os.path.join(pre, "bin", "clang")
    if not os.path.isfile(cc):
        raise CacheError("no %s" % cc)
    return pre, cc


def expected_extra(c_rel):
    """The flags between -O3 -DNDEBUG and -DLEAN_EXPORTING for the C file c_rel (relative to JanusASL/.lake), or None
    when no such object is cacheable. ArmASL's parts and the janus-asl-check root (JanusASL/Check) carry
    -fbracket-depth=100000 (their lakefile entries); the other JanusASL modules and Sail carry nothing more. Taken from
    code, not from the lakefile: a decoy lakefile table cannot widen it (the keyed tables decide what Lake logs; a
    mismatch makes the object unpublishable, never trusted)."""
    if c_rel == "build/ir/ArmASL.c" or c_rel.startswith("build/ir/ArmASL/"):
        return [BRACKET]
    if c_rel == "build/ir/JanusASL/Check.c":
        return [BRACKET]
    if c_rel.startswith("build/ir/JanusASL/") or c_rel.startswith("packages/Sail/.lake/build/ir/"):
        return []
    if c_rel == "build/ir/Janus.c" or c_rel.startswith("build/ir/Janus/"):  # the root package's Janus library (a different tree: its own .lake)
        return []
    return None


def expected_argv(cc, prefix, c_path, out_path, c_rel):
    extra = expected_extra(c_rel)
    if extra is None:
        return None
    return [cc, "-c", "-o", out_path, c_path, "-I", prefix + "/include", "-fstack-clash-protection", "-ffp-contract=off",
            "-fdata-sections", "-ffunction-sections", "-fPIC", "-fvisibility=hidden", "-Wno-unused-command-line-argument",
            "--sysroot", prefix, "-nostdinc", "-isystem", prefix + "/include/clang", "-O3", "-DNDEBUG"] + extra + ["-DLEAN_EXPORTING"]


def argv_problem(argv, cc, prefix, c_rel):
    """None iff argv EQUALS the command Lake logs for the object of c_rel, built from the keyed compiler path and
    prefix (list equality: nothing may be added, dropped, repeated or reordered; argv[0], -I, --sysroot and -isystem are
    the keyed strings). Only the -o / C paths are free, and only in form: <C>.o.export and a path ending in /<c_rel>.
    Only .c.o.export objects are cacheable (the noexport command is not part of the table)."""
    if not isinstance(argv, list) or len(argv) < 5 or not all(isinstance(a, str) for a in argv):
        return "no compile command"
    c_path, out = argv[4], argv[3]
    if out != c_path + ".o.export":
        return "the output %r is not <C>.o.export of %r" % (out, c_path)
    if not (c_path.endswith("/" + c_rel) and c_path.startswith("/") and ".." not in c_path.split("/")):
        return "the C path %r is not .../%s" % (c_path, c_rel)
    want = expected_argv(cc, prefix, c_path, out, c_rel)
    if want is None:
        return "%s is not a cacheable object" % c_rel
    if argv != want:
        for i, (a, b) in enumerate(zip(argv, want)):
            if a != b:
                return "argument %d is %r, expected %r" % (i, a, b)
        return "the command has %d arguments, expected %d" % (len(argv), len(want))
    return None


BWRAP_CANDIDATES = ["/usr/bin/bwrap", "/usr/local/bin/bwrap", "/bin/bwrap"]  # fixed locations; never PATH (a shim there is not trusted)
UNSANDBOXED_OPTIN = "ASL_OBJ_RECOMPILE_UNSANDBOXED"


def _bwrap():
    for c in BWRAP_CANDIDATES:
        try:
            st = os.stat(c)
        except OSError:
            continue
        if stat.S_ISREG(st.st_mode) and st.st_uid == 0 and not (st.st_mode & 0o022) and os.access(c, os.X_OK):
            return c
    return None


def _sandbox_prefix(work, c_dir):
    """The command prefix that runs a recompile with no network, a read-only filesystem except `work`, TMPDIR on the
    work dir, its own pid/ipc namespaces, no capabilities and the HMAC key directory masked (bubblewrap from a FIXED
    root-owned location, as cmd/janus/sandbox.go prefers). A missing or failing bwrap is INCONCLUSIVE: the recompile
    does not run, unless ASL_OBJ_RECOMPILE_UNSANDBOXED=1 says the operator accepts an unsandboxed run (loud warning;
    the command is then only as safe as expected_argv makes it: the keyed toolchain clang with a fixed flag list)."""
    bw = _bwrap()
    probe_ok = False
    pre = []
    if bw:
        pre = [bw, "--unshare-net", "--unshare-pid", "--unshare-ipc", "--die-with-parent", "--new-session", "--cap-drop", "ALL",
               "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc"]
        try:
            kd = os.path.dirname(key_path())
            if os.path.isdir(kd):
                pre += ["--tmpfs", kd]  # the HMAC key is not readable inside
        except Exception:
            pass
        pre += ["--bind", work, work, "--chdir", c_dir, "--"]
        try:
            probe_ok = subprocess.run(pre + ["/bin/true"], capture_output=True, stdin=subprocess.DEVNULL, timeout=60).returncode == 0
        except (OSError, subprocess.SubprocessError):
            probe_ok = False
    if probe_ok:
        return pre
    if os.environ.get(UNSANDBOXED_OPTIN) == "1":
        print("cache: WARNING: no usable bubblewrap; recompiling UNSANDBOXED because %s=1" % UNSANDBOXED_OPTIN, file=sys.stderr)
        return []
    raise Inconclusive("no usable bubblewrap at %s: the recompile is not run unsandboxed (%s=1 opts in)" % (BWRAP_CANDIDATES, UNSANDBOXED_OPTIN))


def recompile_object(cc, prefix, c_path, c_rel, work):
    """Compile c_path with the command built from the keyed values (expected_argv) into a file under work; returns its
    SHA-256. Anything that stops the compile from yielding an answer (timeout, a missing tool, a crash, a sandbox that
    cannot start, a full disk) is Inconclusive, never a match and never a mismatch."""
    out = os.path.join(work, "recompiled.o")
    env = {k: v for k, v in os.environ.items() if k != "JANUS_CACHE_KEY_DIR"}
    env["TMPDIR"] = work
    cmd = expected_argv(cc, prefix, c_path, out, c_rel)
    if cmd is None:
        raise Inconclusive("%s is not a cacheable object" % c_rel)
    pre = _sandbox_prefix(work, os.path.dirname(c_path))
    try:
        r = subprocess.run(pre + cmd, cwd=os.path.dirname(c_path), capture_output=True, env=env, stdin=subprocess.DEVNULL,
                           timeout=int(os.environ.get("ASL_OBJ_RECOMPILE_TIMEOUT", "3600")))
    except (OSError, subprocess.SubprocessError, ValueError) as ex:
        raise Inconclusive("recompile did not run (%s)" % ex)
    if r.returncode != 0:
        raise Inconclusive("recompile failed (rc %d): %s" % (r.returncode, r.stderr.decode("utf-8", "replace")[-300:]))
    try:
        return sha_file(out)
    except OSError as ex:
        raise Inconclusive("recompile produced no object (%s)" % ex)


def clean_stale(d, prefixes=(".recompile-", ".objstage-"), age=3600):
    """Remove leftover private work directories of killed runs (our own prefixes, older than `age` seconds) in d."""
    import time
    try:
        names = os.listdir(d)
    except OSError:
        return
    for n in names:
        q = os.path.join(d, n)
        try:
            if n.startswith(prefixes) and os.path.isdir(q) and not os.path.islink(q) and time.time() - os.lstat(q).st_mtime > age:
                shutil.rmtree(q, ignore_errors=True)
        except OSError:
            pass


def draw_random(cands, k):
    """k random objects of cands [(size, rel, path)], among those whose C is at most ASL_OBJ_RECOMPILE_MAXC bytes
    (default 1000000, about 2.5 minutes of clang -O3): the huge ones (JanusASL.Proofs.Config, 3.7 MB, ~10 minutes) are
    covered by the nightly's full audit, not by every publish."""
    import random
    cap = int(os.environ.get("ASL_OBJ_RECOMPILE_MAXC", "1000000"))
    pool = [c for c in cands if c[0] <= cap]
    return random.SystemRandom().sample(pool, min(len(pool), k))


def recompile_entry(kind, cache, ident, c_root, sample):
    """Recompile objects of the (verified) entry from the C files under c_root with the command each trace logged,
    and compare the SHA-256 with the entry's. sample: an int (that many objects, smallest C first) or "all".
    Returns (checked, [mismatching rel paths]). A C file that does not hash to the entry's .cin record, or a trace
    without a compile command, is an error (inconclusive), never a pass."""
    if kind != "armobj":
        raise CacheError("--recompile is for armobj entries")
    e = entry_dir(kind, cache, ident)
    return recompile_dir(e, verify_entry(kind, cache, ident), c_root, sample, cache)


def recompile_dir(e, man, c_root, sample, cache):
    objs = []
    for rel in sorted(man):
        m = re.match(r"^(.*\.c)\.o\.(export|noexport)$", rel)
        if m:
            cp = os.path.join(c_root, m.group(1))
            try:
                objs.append((os.stat(cp).st_size, rel, cp))
            except OSError:
                raise Inconclusive("no C file %s under %s to recompile %s" % (m.group(1), c_root, rel))
    objs.sort()
    if sample != "all":  # the N smallest plus a size-bounded random draw of the rest (ASL_OBJ_RECOMPILE_RANDOM, default 2)
        n = int(sample)
        objs = objs[:n] + (draw_random(objs[n:], int(os.environ.get("ASL_OBJ_RECOMPILE_RANDOM", "2"))) if n > 0 else [])
    bad = []
    prefix, cc = keyed_toolchain(os.path.dirname(os.path.normpath(c_root)))
    clean_stale(cache)
    try:
        work = tempfile.mkdtemp(prefix=".recompile-", dir=cache)
    except OSError as ex:
        raise Inconclusive("cannot create a work directory in %s (%s)" % (cache, ex))
    try:
        for _, rel, cp in objs:
            try:
                with open(os.path.join(e, "tree", rel + ".cin")) as f:
                    cin = f.read().strip()
                with open(os.path.join(e, "tree", rel + ".trace"), "rb") as f:
                    _, _, argv = trace_facts(f.read())
            except Exception as ex:  # a missing .cin / unreadable trace of a signed entry: unknown, not a verdict
                raise Inconclusive("entry record of %s unreadable (%s)" % (rel, ex))
            try:
                if sha_file(cp) != cin:
                    raise Inconclusive("the C file of %s does not hash to the entry's record" % rel)
            except OSError as ex:
                raise Inconclusive("cannot read %s (%s)" % (cp, ex))
            c_rel = rel[:rel.index(".c.o.")] + ".c"
            if rel.endswith(".noexport") or argv_problem(argv, cc, prefix, c_rel):
                bad.append(rel)  # a logged command of another shape is never run: the entry is poisoned (or foreign)
                continue
            if recompile_object(cc, prefix, cp, c_rel, work) != man[rel]:
                bad.append(rel)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return len(objs), bad


# ---- store ----

def store(kind, cache, ident, src, rels, inputs=None, recompile=None, want_set=None):
    """Publish the files rels (relative to src) as the entry ident. Returns "stored" or "present"."""
    e = entry_dir(kind, cache, ident)
    os.makedirs(os.path.dirname(e), exist_ok=True)
    mac("x", "x", b"")  # fail early (before any work) if the key is unusable
    rels = sorted(set(rels))
    for r in rels:
        parse_manifest(("0" * 64 + "  " + r + "\n").encode())  # path sanity
    check_paths(kind, rels)
    lk = lock_path(e + ".lock", shared=False)
    try:
        if os.path.isdir(e):
            try:
                verify_entry(kind, cache, ident, want_set)
                if recompile:  # (c_root, sample): a recompile that disagrees proves the stored objects poisoned
                    n, bad = recompile_entry(kind, cache, ident, recompile[0], recompile[1])
                    if bad:
                        raise CacheError("recompiling %d object(s) gives other bytes than the entry holds (%s)" % (len(bad), bad[0]))
                return "present"
            except Inconclusive as ex:
                raise CacheError("recompile inconclusive, the existing entry is kept: %s" % ex)
            except CacheError as ex:
                print("cache: replacing the invalid entry %s (%s)" % (e, ex), file=sys.stderr)
                q = tempfile.mkdtemp(prefix=".bad-", dir=os.path.dirname(e))
                os.rename(e, os.path.join(q, "entry"))
                shutil.rmtree(q, ignore_errors=True)
        tmp = tempfile.mkdtemp(prefix=".tmp-", dir=os.path.dirname(e))
        try:
            lines = []
            for r in rels:
                s = os.path.join(src, r)
                _regular(s)
                d = os.path.join(tmp, "tree", r)
                os.makedirs(os.path.dirname(d), exist_ok=True)
                shutil.copyfile(s, d)
                os.chmod(d, (os.stat(s).st_mode & 0o111) | 0o444)
                lines.append("%s  %s\n" % (sha_file(d), r))
            data = "".join(lines).encode()
            if kind == "armobj":  # bound to the id's C set, and not the bytes of a quarantined forgery
                man_new = parse_manifest(data)
                check_armobj_set(os.path.join(tmp, "tree"), man_new, want_set)
                check_tombstone(cache, ident, man_new)
            if recompile and kind == "armobj":  # never publish an object that does not recompile bit-identically
                n, bad = recompile_dir(tmp, parse_manifest(data), recompile[0], recompile[1], os.path.dirname(e))
                if bad:
                    raise CacheError("refusing to store: %d recompiled object(s) differ from the files to store (%s)" % (len(bad), bad[0]))
            with open(os.path.join(tmp, "MANIFEST.sha256"), "wb") as f:
                f.write(data)
            with open(os.path.join(tmp, "MANIFEST.hmac"), "w") as f:
                f.write(mac(kind, ident, data) + "\n")
            if inputs:
                shutil.copyfile(inputs, os.path.join(tmp, "INPUTS.json"))
            os.rename(tmp, e)
        except BaseException:
            shutil.rmtree(tmp, ignore_errors=True)
            raise
        return "stored"
    finally:
        lk.close()


def main(argv):
    if not argv:
        sys.exit(__doc__)
    cmd = argv[0]
    try:
        if cmd == "key-path":
            print(key_path())
            return 0
        if cmd == "prune-armasl":  # prune-armasl LAKEDIR MODEL_SRC_DIR: drop built modules the current model lacks
            n = prune_armasl(argv[1], argv[2])
            print("pruned %d stale ArmASL files" % n)
            return 0
        kind, cache, ident = argv[1:4]
        if cmd == "fetch":
            dest = argv[4]
            globs = [argv[i + 1] for i, a in enumerate(argv) if a == "--clean-glob"]
            try:
                hmac_key()
            except CacheError as ex:
                print("cache: %s; not using the cache" % ex, file=sys.stderr)
                return EX_NOKEY
            try:
                r = fetch(kind, cache, ident, dest, globs)
            except CacheError as ex:
                print("cache: entry %s %s REJECTED (%s); building from source" % (kind, ident, ex), file=sys.stderr)
                return EX_REJECT
            print(r)
            return EX_MISS if r == "miss" else 0
        if cmd == "store":
            inputs = argv[argv.index("--inputs") + 1] if "--inputs" in argv else None
            rels = [x for x in sys.stdin.buffer.read().decode().split("\0") if x]
            try:
                hmac_key()
            except CacheError as ex:
                print("cache: %s; not storing" % ex, file=sys.stderr)
                return EX_NOKEY
            rc = None
            if "--recompile" in argv:
                rc = (argv[argv.index("--c-root") + 1], argv[argv.index("--recompile") + 1])
            print(store(kind, cache, ident, argv[4], rels, inputs, rc))
            return 0
        if cmd == "verify":
            try:
                verify_entry(kind, cache, ident)
            except CacheError as ex:
                if not os.path.isdir(entry_dir(kind, cache, ident)):
                    print("miss")
                    return EX_MISS
                print("invalid: %s" % ex)
                return EX_REJECT
            if "--recompile" in argv:
                n, bad = recompile_entry(kind, cache, ident, argv[argv.index("--c-root") + 1], argv[argv.index("--recompile") + 1])
                if bad:
                    print("POISONED: %d of %d recompiled objects differ from the entry: %s" % (len(bad), n, ", ".join(bad[:5])))
                    return EX_REJECT
                print("valid (%d objects recompiled bit-identically)" % n)
                return 0
            print("valid")
            return 0
    except Inconclusive as ex:
        print("cache: INCONCLUSIVE, no verdict (an existing entry is untouched): %s" % ex, file=sys.stderr)
        return EX_NOKEY
    except CacheError as ex:
        print("cache: %s" % ex, file=sys.stderr)
        return EX_NOKEY
    sys.exit(__doc__)


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    sys.exit(main(sys.argv[1:]))
