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


def lock_path(path, shared, block=True):
    """flock `path` (created if missing). The collector removes lock files while holding them, so
    after the lock is granted the path must still name the locked file; otherwise retry."""
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
    try:
        with open(e + ".use", "a"):
            pass
        os.utime(e + ".use", None)
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


def read_signed_manifest(kind, ident, e):
    """The entry's manifest, if its HMAC is valid; CacheError otherwise."""
    try:
        with open(os.path.join(e, "MANIFEST.sha256"), "rb") as f:
            data = f.read()
        with open(os.path.join(e, "MANIFEST.hmac"), "r") as f:
            tag = f.read().strip()
    except OSError as ex:
        raise CacheError("no signed manifest (%s)" % ex.strerror)
    if not hmac.compare_digest(tag, mac(kind, ident, data)):
        raise CacheError("the manifest's HMAC does not verify")
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


def fetch(kind, cache, ident, dest, clean_globs=()):
    """Copy the verified entry into dest. Returns "hit", "current" (dest already holds exactly the
    entry's files), "miss", or raises CacheError (rejected; dest holds none of the entry's files)."""
    e = entry_dir(kind, cache, ident)
    if not os.path.isfile(os.path.join(e, "MANIFEST.sha256")):
        return "miss"
    lk = lock_path(e + ".lock", shared=True)
    try:
        if not os.path.isfile(os.path.join(e, "MANIFEST.sha256")):
            return "miss"
        man = read_signed_manifest(kind, ident, e)
        touch_use(e)
        if _same(dest, man):
            return "current"
        written = []
        try:
            for rel, h in sorted(man.items()):
                src = os.path.join(e, "tree", rel)
                _regular(src)
                dst = _under(dest, rel)
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                tmp = dst + ".bcache-tmp"
                d = hashlib.sha256()
                fd = os.open(src, os.O_RDONLY | os.O_NOFOLLOW)
                with os.fdopen(fd, "rb") as fi, open(tmp, "wb") as fo:
                    for chunk in iter(lambda: fi.read(1 << 20), b""):
                        d.update(chunk)
                        fo.write(chunk)
                if d.hexdigest() != h:
                    os.unlink(tmp)
                    raise CacheError("file %s does not match the manifest" % rel)
                shutil.copymode(src, tmp)
                os.chmod(tmp, os.stat(tmp).st_mode | 0o200)  # the consumer's copy is writable
                os.replace(tmp, dst)
                written.append(dst)
        except (OSError, CacheError) as ex:
            for p in written + [_under(dest, r) for r in man]:
                try:
                    os.unlink(p)
                except OSError:
                    pass
            import glob
            for g in clean_globs:
                for p in glob.glob(os.path.join(dest, g)):
                    if os.path.isfile(p) or os.path.islink(p):
                        try:
                            os.unlink(p)
                        except OSError:
                            pass
            raise CacheError(str(ex))
        return "hit"
    finally:
        lk.close()


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
