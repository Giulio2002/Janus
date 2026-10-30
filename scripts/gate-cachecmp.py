#!/usr/bin/env python3
"""Cache-vs-cold comparison for the nightly cold gate (scripts/nightly-cold-gate.sh; docs/TESTING.md
"Build cache policy").

    gate-cachecmp.py hashes WORKTREE OUT.json     SHA-256 of the build artifacts the ASL/Sail caches serve:
                                                  every ArmASL and JanusASL .olean (and their combined digest)
                                                  and the Sail oracle driver binary
    gate-cachecmp.py compare CACHED_OUT COLD_OUT  compare two gate output directories (timeline.jsonl and
                                                  artifact-hashes.json each)

`compare` exits 0 when the two runs agree on the commit, on the status of every prebuild step, stage, item
and lane (PASS/FAIL), and on every artifact hash; 1 with a "P0 CACHE BUG" report on any difference (the
cached run and the truly cold run of one commit must not differ: any difference means the cache served
something the inputs do not determine, or a key misses an input); 2 when a run cannot be compared (missing
or malformed files, different commits)."""
import hashlib
import json
import os
import sys


def sha_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def hashes(worktree):
    out = {}
    lib = os.path.join(worktree, "JanusASL", ".lake", "build", "lib", "lean")
    for d, dirs, files in os.walk(lib):
        dirs.sort()
        for f in sorted(files):
            if f.endswith(".olean"):
                p = os.path.join(d, f)
                out["olean:" + os.path.relpath(p, lib)] = sha_file(p)
    drv = os.path.join(worktree, "oracle-sail", "target", "release", "janus-oracle-sail")
    if os.path.isfile(drv):
        out["sail-driver"] = sha_file(drv)
    h = hashlib.sha256()
    for k in sorted(out):
        h.update(("%s %s\n" % (k, out[k])).encode())
    out["combined"] = h.hexdigest()
    return out


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


def compare(cached, cold):
    try:
        g1, s1 = load_timeline(cached)
        g2, s2 = load_timeline(cold)
        h1 = json.load(open(os.path.join(cached, "artifact-hashes.json")))
        h2 = json.load(open(os.path.join(cold, "artifact-hashes.json")))
    except (OSError, ValueError, KeyError) as ex:
        print("cachecmp: cannot compare the runs: %s" % ex)
        return 2
    if not g1 or not g2 or g1.get("commit") != g2.get("commit"):
        print("cachecmp: the runs are of different commits (%s vs %s): not comparable" % (
            (g1 or {}).get("commit"), (g2 or {}).get("commit")))
        return 2
    diffs = []
    for k in sorted(set(s1) | set(s2)):
        a, b = s1.get(k, "MISSING"), s2.get(k, "MISSING")
        if a != b:
            diffs.append("%s: cached run %s, cold run %s" % (k, a, b))
    for k in sorted(set(h1) | set(h2)):
        a, b = h1.get(k), h2.get(k)
        if a != b:
            diffs.append("artifact %s: cached %s, cold %s" % (k, (a or "MISSING")[:16], (b or "MISSING")[:16]))
    if diffs:
        print("P0 CACHE BUG: the cached gate and the cold gate of commit %s disagree (%d differences):" % (g1.get("commit"), len(diffs)))
        for d in diffs:
            print("  " + d)
        print("P0: owner is the main session (docs/TESTING.md 'Build cache policy'): treat every cached gate result since the last agreeing nightly as unproven.")
        return 1
    print("cachecmp: cached and cold runs of commit %s agree on %d prebuild steps/stages/items/lanes and %d artifact hashes" % (
        g1.get("commit"), len(s1), len(h1)))
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
