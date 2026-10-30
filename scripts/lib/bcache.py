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
    bcache.py store  KIND CACHE ID SRC [--inputs FILE] < NUL-separated relative paths of SRC
    bcache.py verify KIND CACHE ID                              0 valid, 2 miss, 3 invalid
    bcache.py prune-armasl LAKEDIR MODEL_ARMASL_DIR             drop built ArmASL modules the current model lacks
    bcache.py key-path                                          where the per-user key lives

KIND is armasl (CACHE/<id>), sail (CACHE/sail/<id>) or mod (CACHE/mods/<id[:2]>/<id>).
The HMAC key: $JANUS_CACHE_KEY_DIR/asl-cache.key, default ~/.cache/janus/asl-cache-key/asl-cache.key (32 random
bytes, mode 0600, directory 0700, ours, not a symlink; created atomically on first use). When it
cannot be read or created safely, the cache is not used at all (exit 4: the caller builds).
"""
import errno
import fcntl
import hashlib
import hmac
import os
import shutil
import stat
import sys
import tempfile

SCHEME = b"janus-build-cache-hmac-v1"
EX_MISS, EX_REJECT, EX_NOKEY = 2, 3, 4


class CacheError(Exception):
    pass


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
    raise CacheError("unknown kind %r" % kind)


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


def read_signed_manifest(kind, ident, e, want_sha=None):
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
    return parse_manifest(data)


def _regular(p):
    st = os.lstat(p)
    if not stat.S_ISREG(st.st_mode):
        raise CacheError("%s is not a regular file" % p)
    return st


def verify_entry(kind, cache, ident):
    """Verify an entry in place (HMAC and the SHA-256 of every file). Returns the manifest."""
    e = entry_dir(kind, cache, ident)
    man = read_signed_manifest(kind, ident, e)
    for rel, h in man.items():
        p = os.path.join(e, "tree", rel)
        try:
            _regular(p)
            ok = sha_file(p) == h
        except OSError:
            raise CacheError("missing file %s" % rel)
        if not ok:
            raise CacheError("file %s does not match the manifest" % rel)
    return man


# ---- fetch ----

def _under(dest, rel):
    p = os.path.normpath(os.path.join(dest, rel))
    if not (p + os.sep).startswith(os.path.normpath(dest) + os.sep):
        raise CacheError("path escapes the destination: %r" % rel)
    return p


def _same(dest, man):
    for rel, h in man.items():
        p = _under(dest, rel)
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


def fetch(kind, cache, ident, dest, clean_globs=(), want_sha=None):
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
                    dst = _under(dest, rel)
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
        d = os.path.dirname(_under(dest, rel))
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


# ---- store ----

def store(kind, cache, ident, src, rels, inputs=None):
    """Publish the files rels (relative to src) as the entry ident. Returns "stored" or "present"."""
    e = entry_dir(kind, cache, ident)
    os.makedirs(os.path.dirname(e), exist_ok=True)
    mac("x", "x", b"")  # fail early (before any work) if the key is unusable
    rels = sorted(set(rels))
    for r in rels:
        parse_manifest(("0" * 64 + "  " + r + "\n").encode())  # path sanity
    lk = lock_path(e + ".lock", shared=False)
    try:
        if os.path.isdir(e):
            try:
                verify_entry(kind, cache, ident)
                return "present"
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
            print(store(kind, cache, ident, argv[4], rels, inputs))
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
            print("valid")
            return 0
    except CacheError as ex:
        print("cache: %s" % ex, file=sys.stderr)
        return EX_NOKEY
    sys.exit(__doc__)


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    sys.exit(main(sys.argv[1:]))
