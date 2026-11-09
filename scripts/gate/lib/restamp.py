#!/usr/bin/env python3
"""Re-stamp a private tree's framework build after the module cache restored Janus modules into it.

    python3 -I scripts/lib/restamp.py TREE RECORD

`scripts/asl.sh verify` restores the cached builds of the Janus and JanusASL modules into the gate's private tree (a
copy of the finished, stamped framework build). An .olean embeds the absolute path of its source file, so a restored
Janus module differs byte for byte from the one the tree was copied with, and the tree's stamp
(.lake/janus-framework.ready: the SHA-256 of every framework module-data file as built) no longer matches. `janus verify
--janus-root TREE` then (by design) removes and rebuilds each such module, and the restored JanusASL modules, whose
traces name the restored bytes, all rebuild too (79 min in the last gate).

This updates the stamp's pin of a module to the file's current SHA-256 ONLY when that file is exactly what the module
cache restored from an HMAC-verified entry (RECORD: path -> SHA-256 written by `asl_mod_cache.py restore --record`).
The record carries an HMAC (scripts/lib/bcache.py record_mac: the cache's per-user key, domain "restamp", bound to the
tree root); a missing or wrong MAC, or a record that is not exactly {"files", "mac"}, is REFUSED (exit 2, nothing pinned).
Every path component from the tree root to a module file is lstat'ed; a symbolic link anywhere on it, a '..' or '.'
component, or a record path outside the tree's lib/lean directory never matches. Anything else that differs from the stamp (a file the cache did not restore, a missing or foreign file) is left as it is:
the stamp keeps its old pin and janus rejects/rebuilds it exactly as before. The stamp's sources hash, manifest, targets
and the auditor executable's SHA-256 are never touched; with no stamp or no record nothing is done.
"""
import hashlib
import hmac
import importlib.util
import json
import os
import stat
import sys

LIBREL = (".lake", "build", "lib", "lean")


def sha(p):
    h = hashlib.sha256()
    fd = os.open(p, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def load_bcache():
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("bcache", os.path.join(os.path.dirname(os.path.abspath(__file__)), "bcache.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def safe_parts(rel):
    """The components of a relative path, or None when it has an empty, '.' or '..' component or is absolute."""
    parts = rel.split("/")
    if rel.startswith("/") or any(p in ("", ".", "..") or "\0" in p for p in parts):
        return None
    return parts


def safe_file(base, parts):
    """lstat every component below BASE: no symbolic link anywhere, directories on the way, a regular file at the end."""
    cur = base
    for i, c in enumerate(parts):
        cur = os.path.join(cur, c)
        try:
            st = os.lstat(cur)
        except OSError:
            return None
        if stat.S_ISLNK(st.st_mode):
            return None
        if i < len(parts) - 1 and not stat.S_ISDIR(st.st_mode):
            return None
        if i == len(parts) - 1 and not stat.S_ISREG(st.st_mode):
            return None
    return cur


def load_record(tree, record, bc):
    """The record's files (path -> SHA-256) iff its MAC verifies; raises ValueError otherwise."""
    st = os.lstat(record)
    if not stat.S_ISREG(st.st_mode):
        raise ValueError("record is not a regular file")
    fd = os.open(record, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, "rb") as f:
        doc = json.loads(f.read())
    if not isinstance(doc, dict) or set(doc) != {"files", "mac"} or not isinstance(doc["mac"], str):
        raise ValueError("record has no MAC")
    files = doc["files"]
    if not isinstance(files, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in files.items()):
        raise ValueError("record has an unexpected shape")
    try:
        if not os.path.exists(bc.key_path()):
            raise ValueError("no cache key")  # never create a key here: a fresh key cannot verify anything
        want = bc.record_mac(tree, files)
    except bc.CacheError as ex:
        raise ValueError(str(ex))
    if not hmac.compare_digest(doc["mac"], want):
        raise ValueError("wrong record MAC")
    return files


def main(tree, record):
    base = os.path.realpath(tree)
    stamp = os.path.join(base, ".lake", "janus-framework.ready")
    try:
        if stat.S_ISLNK(os.lstat(stamp).st_mode):
            raise OSError("stamp is a symbolic link")
        with open(stamp) as f:
            st = json.load(f)
        os.lstat(record)
    except (OSError, ValueError) as ex:
        print("restamp: nothing to do (%s)" % ex)
        return 0
    try:
        files = load_record(tree, record, load_bcache())
    except (OSError, ValueError) as ex:
        print("restamp: REFUSED, the module-cache record is not authentic (%s); nothing pinned" % ex, file=sys.stderr)
        return 2
    if not isinstance(st, dict) or not isinstance(st.get("pins"), dict):
        print("restamp: nothing to do (unexpected stamp shape)")
        return 0
    # record entries below the tree's lib/lean directory, by relative path; anything else (outside the tree, '..', '.')
    # can never match a pin
    libp = base + "/" + "/".join(LIBREL) + "/"
    recn = {}
    for k, v in files.items():
        if k.startswith(libp):
            parts = safe_parts(k[len(libp):])
            if parts is not None:
                recn["/".join(parts)] = v
    changed = refused = 0
    for rel, old in sorted(st["pins"].items()):
        parts = safe_parts(rel)
        path = safe_file(base, LIBREL + tuple(parts)) if parts is not None else None
        if path is None:
            refused += 1
            continue
        try:
            cur = sha(path)
        except OSError:
            refused += 1
            continue
        if cur == old:
            continue
        # restored from a verified cache entry, and still exactly that file
        if recn.get(rel) == cur:
            st["pins"][rel] = cur
            changed += 1
        else:
            refused += 1
    if changed:
        tmp = stamp + ".tmp%d" % os.getpid()
        fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        with os.fdopen(fd, "w") as f:
            json.dump(st, f, separators=(",", ":"))
        os.replace(tmp, stamp)
    print("restamp: %d framework module pins moved to the cache-restored (verified) files, %d differing files left for janus" % (changed, refused))
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    sys.exit(main(sys.argv[1], sys.argv[2]))
