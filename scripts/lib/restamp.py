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
Anything else that differs from the stamp (a file the cache did not restore, a missing or foreign file) is left as it is:
the stamp keeps its old pin and janus rejects/rebuilds it exactly as before. The stamp's sources hash, manifest, targets
and the auditor executable's SHA-256 are never touched; with no stamp or no record nothing is done.
"""
import hashlib
import json
import os
import sys


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def main(tree, record):
    stamp = os.path.join(tree, ".lake", "janus-framework.ready")
    lib = os.path.join(tree, ".lake", "build", "lib", "lean")
    try:
        with open(stamp) as f:
            st = json.load(f)
        with open(record) as f:
            rec = json.load(f)
    except (OSError, ValueError) as ex:
        print("restamp: nothing to do (%s)" % ex)
        return 0
    if not isinstance(st.get("pins"), dict) or not isinstance(rec, dict):
        print("restamp: nothing to do (unexpected stamp/record shape)")
        return 0
    recn = {os.path.realpath(k): v for k, v in rec.items()}
    changed = refused = 0
    for rel, old in sorted(st["pins"].items()):
        path = os.path.join(lib, *rel.split("/"))
        if os.path.islink(path) or not os.path.isfile(path):
            refused += 1
            continue
        cur = sha(path)
        if cur == old:
            continue
        # restored from a verified cache entry, and still exactly that file
        if recn.get(os.path.realpath(path)) == cur:
            st["pins"][rel] = cur
            changed += 1
        else:
            refused += 1
    if changed:
        tmp = stamp + ".tmp%d" % os.getpid()
        fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, "w") as f:
            json.dump(st, f, separators=(",", ":"))
        os.replace(tmp, stamp)
    print("restamp: %d framework module pins moved to the cache-restored (verified) files, %d differing files left for janus" % (changed, refused))
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    sys.exit(main(sys.argv[1], sys.argv[2]))
