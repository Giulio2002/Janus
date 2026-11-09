#!/usr/bin/env python3
"""Integrity records of the Sail model directories (scripts/oracle-sail.sh model_dir / split_parts).

    dir_digest.py digest PATH...                      print the SHA-256 over PATH... (see below)
    dir_digest.py record OUT PATH... [-- K=V ...]     write OUT: the digest of PATH... and the K=V pairs
    dir_digest.py check  REC PATH... [-- K=V ...]     exit 0 iff REC holds exactly the digest of PATH... and the K=V pairs

A PATH is a file, or a directory (its files, not recursive; a subdirectory, a symlink or anything that is not a regular
file is an error). The digest covers, per file, its name and its content, in sorted order, so a modified, added, removed
or renamed file changes it; the record files themselves (`.complete`, `.inst-complete`) are not part of a directory's
digest. A model that is rebuilt from a record that does not check is regenerated (or the build fails), never built
silently: the instrumented model, the parts, model.h and model_missing.cpp (about 200 MB, ~1 s) are re-hashed on every use.
"""
import hashlib
import os
import sys

RECORDS = (".complete", ".inst-complete")


def files_of(paths):
    out = []
    for i, p in enumerate(paths):
        if os.path.islink(p):
            raise ValueError("symlink: " + p)
        if os.path.isdir(p):
            for n in sorted(os.listdir(p)):
                if n in RECORDS:
                    continue
                q = os.path.join(p, n)
                if os.path.islink(q) or not os.path.isfile(q):
                    raise ValueError("not a regular file: " + q)
                out.append(("%d/%s" % (i, n), q))
        elif os.path.isfile(p):
            out.append(("%d/%s" % (i, os.path.basename(p)), p))
        else:
            raise ValueError("missing: " + p)
    return out


def digest(paths):
    h = hashlib.sha256()
    for name, q in files_of(paths):
        fh = hashlib.sha256()
        with open(q, "rb") as f:
            for c in iter(lambda: f.read(1 << 22), b""):
                fh.update(c)
        h.update(("%s %d %s\n" % (name, os.path.getsize(q), fh.hexdigest())).encode())
    return h.hexdigest()


def split_args(a):
    if "--" in a:
        i = a.index("--")
        return a[:i], a[i + 1:]
    return a, []


def main(a):
    if len(a) >= 2 and a[0] == "digest":
        print(digest(a[1:]))
        return 0
    if len(a) >= 3 and a[0] in ("record", "check"):
        paths, kv = split_args(a[2:])
        want = {"digest": digest(paths)}
        for x in kv:
            k, v = x.split("=", 1)
            want[k] = v
        if a[0] == "record":
            tmp = a[1] + ".tmp.%d" % os.getpid()
            with open(tmp, "w") as f:
                for k in sorted(want):
                    f.write("%s=%s\n" % (k, want[k]))
            os.replace(tmp, a[1])
            return 0
        try:
            got = dict(l.rstrip("\n").split("=", 1) for l in open(a[1]) if l.strip())
        except OSError as ex:
            print("dir_digest: no record %s (%s)" % (a[1], type(ex).__name__), file=sys.stderr)
            return 1
        bad = sorted(k for k in set(want) | set(got) if want.get(k) != got.get(k))
        if bad:
            print("dir_digest: %s does not match (%s)" % (a[1], ", ".join(bad)), file=sys.stderr)
            return 1
        return 0
    sys.exit(__doc__)


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except ValueError as ex:
        print("dir_digest: %s" % ex, file=sys.stderr)
        sys.exit(2)
