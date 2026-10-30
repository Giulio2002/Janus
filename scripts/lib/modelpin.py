#!/usr/bin/env python3
"""The pin of the ISA model artifacts (the ArmASL modules and the Sail driver) for the cold gate
(scripts/gate.sh --cold; docs/TESTING.md "Cold gate and the model pin").

The cold gate rebuilds everything except these artifacts, which are treated like the Lean toolchain: pinned by content
and integrity-checked on EVERY gate. This file adds no new trusted storage code: the pinned artifacts are a
bcache.py entry (scripts/lib/bcache.py: per-file SHA-256 manifest + HMAC under the per-user key, two-phase verified
copy) in a pin store of their own, and the pin RECORD binds the entry to the exact manifest by its SHA-256.

    <PIN>/<key>                       kind armasl entry (JanusASL/.lake: ArmASL build + packages/Sail)
    <PIN>/sail/<key>                  kind sail entry (the oracle driver)
    <PIN>/records/<kind>-<key>.json   {"record": {...}, "hmac": ...}: one file, replaced atomically
    <PIN>/.pin-write.lock             held by the (only) writer

The pin store is NOT the build cache (the collector of asl_mod_cache.py never sees it, a cached run never writes it).
The key is the build-cache key of the model inputs (asl_cache_key.py / oracle-sail/cache_key.py): a change of any
model input (sources, toolchain, environment, key scheme) is a different key, so the pin of the old key is not
found: STALE.

    modelpin.py dir                                     the pin store directory
    modelpin.py check   KIND PIN KEY [--shallow]        record + HMACs + (unless --shallow) every file of the entry
    modelpin.py restore KIND PIN KEY DEST               check + two-phase verified copy into DEST
    modelpin.py verify-tree KIND PIN KEY DEST           every pinned file in DEST still has its pinned hash
    modelpin.py write   KIND PIN KEY SRC --commit C [--evidence FILE] < NUL-separated relative paths
                                                        (the nightly truly-cold run only: JANUS_PIN_WRITER=nightly-cold-gate)

Exit status of check / restore / verify-tree: 0 ok; 2 STALE (no pin for this key: the inputs changed, or none was ever
written); 3 INVALID (a pin exists and is tampered, corrupt, incomplete, or does not match: never rebuilt around);
4 the HMAC key is unusable. `write`: 0 written or already identical; 1 NOT REPRODUCED (an existing valid pin differs
in a .olean/.ilean/driver byte); 2 refused (not the nightly run) or lock held; 4 key unusable.
"""
import fcntl
import hashlib
import hmac
import json
import os
import shutil
import socket
import sys
import tempfile
import time

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bcache  # noqa: E402

SCHEME = "janus-model-pin-v1"
EX_OK, EX_STALE, EX_INVALID, EX_NOKEY = 0, 2, 3, 4
KINDS = ("armasl", "sail")


def is_strict(rel):
    """A difference in these files between two builds of one key is non-reproducibility (the nightly's
    scripts/gate-cachecmp.py compares the same artifacts)."""
    return rel.endswith((".olean", ".ilean")) or os.path.basename(rel) == "janus-oracle-sail"


class Stale(Exception):
    pass


class Invalid(Exception):
    pass


def pin_dir():
    d = os.environ.get("JANUS_MODEL_PIN_DIR")
    if d:
        return d
    if os.path.isdir("/srv/janus-asl-cache"):
        return "/srv/janus-model-pin"
    return os.path.join(os.environ.get("XDG_CACHE_HOME") or os.path.join(os.path.expanduser("~"), ".cache"), "janus", "model-pin")


def canon(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def rec_path(root, kind, key):
    if kind not in KINDS:
        raise Invalid("unknown kind %r" % kind)
    bcache.entry_dir(kind, root, key)   # validates the key syntax
    return os.path.join(root, "records", "%s-%s.json" % (kind, key))


def rec_mac(kind, key, data):
    return bcache.mac("pin-record:" + kind, key, data)


def read_record(root, kind, key):
    p = rec_path(root, kind, key)
    try:
        with open(p, "rb") as f:
            raw = f.read()
    except FileNotFoundError:
        raise Stale("no pin for %s key %s in %s (a model input changed since the last nightly truly-cold run, or no pin was ever written)" % (kind, key, root))
    except OSError as ex:
        raise Invalid("the pin record %s is unreadable (%s)" % (p, ex.strerror))
    try:
        top = json.loads(raw.decode())
        rec, tag = top["record"], top["hmac"]
        if not isinstance(rec, dict) or not isinstance(tag, str) or set(top) != {"record", "hmac"}:
            raise ValueError("shape")
    except (ValueError, KeyError, TypeError, UnicodeDecodeError):
        raise Invalid("the pin record %s is corrupt (not a signed record)" % p)
    try:
        ok = hmac.compare_digest(tag, rec_mac(kind, key, canon(rec)))
    except bcache.CacheError as ex:
        raise Invalid("the HMAC key is unusable: %s" % ex)
    if not ok:
        raise Invalid("the pin record %s does not verify (HMAC): tampered or written under another key" % p)
    if rec.get("scheme") != SCHEME or rec.get("kind") != kind or rec.get("key") != key:
        raise Invalid("the pin record %s is for another scheme/kind/key" % p)
    sh = rec.get("manifestSha256")
    if not isinstance(sh, str) or len(sh) != 64 or any(c not in "0123456789abcdef" for c in sh):
        raise Invalid("the pin record %s has no manifest hash" % p)
    return rec


def entry_manifest(kind, root, key, rec):
    """The entry's manifest, accepted only if its HMAC verifies AND it is the pinned manifest (a replaced or edited
    manifest, even a re-signed one, is not the pin)."""
    e = bcache.entry_dir(kind, root, key)
    if not os.path.isdir(e):
        raise Invalid("the pinned %s artifacts are MISSING (%s)" % (kind, e))
    try:
        return bcache.read_signed_manifest(kind, key, e, rec["manifestSha256"])
    except bcache.CacheError as ex:
        raise Invalid("the pinned %s manifest is invalid: %s" % (kind, ex))


def check(kind, root, key, deep=True):
    rec = read_record(root, kind, key)
    man = entry_manifest(kind, root, key, rec)
    if len(man) != rec.get("files"):
        raise Invalid("the pinned %s manifest lists %d files, the record %s" % (kind, len(man), rec.get("files")))
    if deep:
        try:
            bcache.verify_entry(kind, root, key)
        except bcache.CacheError as ex:
            raise Invalid("the pinned %s artifacts are damaged: %s" % (kind, ex))
    return rec, man


def restore(kind, root, key, dest):
    rec, _ = check(kind, root, key, deep=False)
    try:
        r = bcache.fetch(kind, root, key, dest, want_sha=rec["manifestSha256"])
    except bcache.CacheError as ex:
        raise Invalid("the pinned %s artifacts were REJECTED: %s" % (kind, ex))
    if r == "miss":
        raise Invalid("the pinned %s artifacts are MISSING" % kind)
    return rec, r


def verify_tree(kind, root, key, dest):
    rec = read_record(root, kind, key)
    man = entry_manifest(kind, root, key, rec)
    bad = []
    for rel, h in sorted(man.items()):
        p = os.path.join(dest, rel)
        try:
            ok = os.path.isfile(p) and not os.path.islink(p) and bcache.sha_file(p) == h
        except OSError:
            ok = False
        if not ok:
            bad.append(rel)
    if bad:
        raise Invalid("%d pinned %s file(s) are missing or changed in %s after the build, e.g. %s" % (len(bad), kind, dest, ", ".join(bad[:3])))
    return rec


def lock_writer(root):
    os.makedirs(root, exist_ok=True)
    f = bcache.open_lock(os.path.join(root, ".pin-write.lock"))
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        f.close()
        return None
    return f


def atomic_write(path, data):
    d = os.path.dirname(path)
    os.makedirs(d, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=".rec.tmp-", dir=d)
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.chmod(tmp, 0o644)
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise
    dfd = os.open(d, os.O_RDONLY)
    try:
        os.fsync(dfd)
    finally:
        os.close(dfd)


def write(kind, root, key, src, rels, commit, evidence):
    if os.environ.get("JANUS_PIN_WRITER") != "nightly-cold-gate" or os.environ.get("JANUS_MODEL_PIN"):
        print("modelpin: REFUSED: only the nightly truly-cold run (scripts/nightly-cold-gate.sh) may create or update a pin", file=sys.stderr)
        return 2
    try:
        bcache.mac("x", "x", b"")
    except bcache.CacheError as ex:
        print("modelpin: %s" % ex, file=sys.stderr)
        return EX_NOKEY
    lk = lock_writer(root)
    if lk is None:
        print("modelpin: another pin write holds %s/.pin-write.lock" % root, file=sys.stderr)
        return 2
    try:
        rels = sorted(set(rels))
        new = {}
        for r in rels:
            p = os.path.join(src, r)
            bcache._regular(p)
            new[r] = bcache.sha_file(p)
        manifest = "".join("%s  %s\n" % (h, r) for r, h in sorted(new.items())).encode()
        msha = hashlib.sha256(manifest).hexdigest()
        have = None
        try:
            have = check(kind, root, key, deep=True)
        except Stale:
            pass
        except Invalid as ex:
            print("modelpin: REPLACING the invalid %s pin (%s)" % (kind, ex), file=sys.stderr)
        if have:
            rec, man = have
            diff = sorted(r for r in set(man) | set(new) if man.get(r) != new.get(r))
            if not diff:
                print("%s pin %s: reproduced, unchanged (%d files, manifest %s)" % (kind, key, len(new), msha[:16]))
                return 0
            strict = [r for r in diff if is_strict(r)]
            print("modelpin: %s %s: the truly-cold build differs from the pin in %d file(s) (%d .olean/.ilean/driver): %s" % (
                "NOT REPRODUCED" if strict else "pin kept; only non-semantic files differ", key, len(diff), len(strict), ", ".join(diff[:5])), file=sys.stderr)
            return 1 if strict else 0
        # a new pin (or the replacement of an invalid one): the entry first, then the record (the commit point)
        e = bcache.entry_dir(kind, root, key)
        if os.path.isdir(e):
            q = tempfile.mkdtemp(prefix=".bad-", dir=os.path.dirname(e))
            os.rename(e, os.path.join(q, "entry"))
            shutil.rmtree(q, ignore_errors=True)
        out = bcache.store(kind, root, key, src, rels)
        with open(os.path.join(e, "MANIFEST.sha256"), "rb") as f:
            got = hashlib.sha256(f.read()).hexdigest()
        if got != msha:
            print("modelpin: the stored manifest is not the one computed (%s vs %s)" % (got[:16], msha[:16]), file=sys.stderr)
            return 1
        rec = {"scheme": SCHEME, "kind": kind, "key": key, "manifestSha256": msha, "files": len(new), "commit": commit,
               "time": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "host": socket.gethostname(),
               "writer": "nightly-cold-gate", "evidence": evidence}
        atomic_write(rec_path(root, kind, key), json.dumps({"record": rec, "hmac": rec_mac(kind, key, canon(rec))}, sort_keys=True, indent=1).encode())
        check(kind, root, key, deep=True)
        print("%s pin %s: %s (%d files, manifest %s, commit %s)" % (kind, key, out, len(new), msha[:16], commit))
        return 0
    finally:
        lk.close()


def main(a):
    if not a:
        sys.exit(__doc__)
    cmd = a[0]
    if cmd == "dir":
        print(pin_dir())
        return 0
    try:
        kind, root, key = a[1:4]
    except ValueError:
        sys.exit(__doc__)
    try:
        if cmd == "write":
            src = a[4]
            commit = a[a.index("--commit") + 1] if "--commit" in a else "?"
            ev = {}
            if "--evidence" in a:
                f = a[a.index("--evidence") + 1]
                ev = {"file": os.path.basename(f), "sha256": bcache.sha_file(f)}
            rels = [x for x in sys.stdin.buffer.read().decode().split("\0") if x]
            return write(kind, root, key, src, rels, commit, ev)
        if cmd == "check":
            rec, man = check(kind, root, key, deep="--shallow" not in a)
            print("OK: %s pin %s: %d files, manifest %s, written %s by commit %s" % (kind, key, len(man), rec["manifestSha256"][:16], rec.get("time"), rec.get("commit")))
        elif cmd == "restore":
            rec, r = restore(kind, root, key, a[4])
            print("OK: %s pin %s restored (%s), manifest %s" % (kind, key, r, rec["manifestSha256"][:16]))
        elif cmd == "verify-tree":
            rec = verify_tree(kind, root, key, a[4])
            print("OK: every pinned %s file in %s has its pinned hash (manifest %s)" % (kind, a[4], rec["manifestSha256"][:16]))
        else:
            sys.exit(__doc__)
    except Stale as ex:
        print("STALE: %s" % ex)
        return EX_STALE
    except Invalid as ex:
        print("INVALID: %s" % ex)
        return EX_INVALID
    except bcache.CacheError as ex:
        print("INVALID: %s" % ex)
        return EX_NOKEY if "cache key" in str(ex) else EX_INVALID
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
