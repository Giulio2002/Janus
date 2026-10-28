#!/usr/bin/env python3
"""Speed-regression check of a gate run (on top of every other check, never instead of one).

  python3 -I scripts/gate-speedcheck.py check  TIMELINE BASELINE [LOGDIR]
  python3 -I scripts/gate-speedcheck.py update TIMELINE BASELINE [LOGDIR]   (rewrite BASELINE from a run)

TIMELINE is <gate out>/timeline.jsonl; BASELINE is the committed scripts/speed-baseline.tsv
("id<TAB>wall seconds<TAB>peak GiB", one line per item of the verify pool and per lane); LOGDIR (default
the timeline's directory + /verify) holds the items' logs, from which the peak memory is read
("memguard[...]: peak X GiB / MiB" lines, the largest).

check fails (exit 1) if
  * an item that PASSED took more than max(1.5 x baseline, baseline + 10 s)  (the absolute floor keeps
    items of a few seconds from flapping on noise; the message names the item, baseline, measured wall, ratio),
  * the total pool work (sum of the walls of the items present in both) exceeds 1.5 x the baseline's.
New items (no baseline line) are reported, not failed; they enter the baseline at the next `update`.
Items that did not pass are the pass/fail checks' business and are not judged here. The host load of the
run (timeline "gate" line) is printed with the verdict; it is information only: a slow item is never
excused by load (a real slowdown of 1.5x or more fails whatever the load), and never failed because of it
below the threshold. Memory: an item whose peak exceeds 1.5 x baseline and baseline + 1 GiB is listed as a
warning (not a failure: peaks vary with cache state).

Update procedure (docs/TESTING.md "Speed baseline"): after a passing full gate that was meant to change
speeds (a faster proof, a new item, an intended trade), run `update` on that run's timeline and commit the
new scripts/speed-baseline.tsv with the change that explains it. An update that makes items slower needs
the reason in the commit message."""
import json, os, re, sys

FACTOR, FLOOR = 1.5, 10.0

def load_tl(path):
    return [json.loads(l) for l in open(path) if l.strip()]

def peaks(logdir):
    out = {}
    if not os.path.isdir(logdir):
        return out
    pat = re.compile(r"memguard\[[^\]]*\]: peak ([0-9.]+) (GiB|MiB)")
    for f in os.listdir(logdir):
        if not f.endswith(".log"):
            continue
        best = 0.0
        for l in open(os.path.join(logdir, f), errors="replace"):
            m = pat.search(l)
            if m:
                v = float(m.group(1)) / (1024 if m.group(2) == "MiB" else 1)
                best = max(best, v)
        out[f[:-4]] = best
    return out

def filekey(i):  # pool.sh's log file name for an id
    return i.replace("/", "_").replace(":", "_")

def measured(rows, logdir):
    pk = peaks(logdir)
    res = {}
    for r in rows:
        if r.get("kind") == "item" and r.get("status") in ("PASS",):
            key = ("lane:" if r["pool"] == "gate" else "") + r["id"]
            res[key] = (r["wall"], pk.get(filekey(r["id"]), 0.0) if r["pool"] != "gate" else 0.0)
    return res

def read_base(path):
    b = {}
    for l in open(path):
        if l.strip() and not l.startswith("#"):
            k, w, m = l.rstrip("\n").split("\t")
            b[k] = (float(w), float(m))
    return b

def main():
    mode, tl, base = sys.argv[1:4]
    rows = load_tl(tl)
    logdir = sys.argv[4] if len(sys.argv) > 4 else os.path.join(os.path.dirname(tl), "verify")
    got = measured(rows, logdir)
    gate = next((r for r in rows if r["kind"] == "gate"), {})
    if mode == "update":
        with open(base, "w") as f:
            f.write("# speed baseline (scripts/gate-speedcheck.py): id, wall seconds, peak GiB; commit %s, -j %s, load %s\n" % (
                gate.get("commit"), gate.get("jobs"), gate.get("load1")))
            for k in sorted(got):
                f.write("%s\t%.1f\t%.2f\n" % (k, got[k][0], got[k][1]))
        print("speed baseline: %d items written to %s" % (len(got), base))
        return 0
    b = read_base(base)
    print("speed check: host load %s at start, -j %s, %d items measured, baseline %d items" % (
        gate.get("load1"), gate.get("jobs"), len(got), len(b)))
    bad, new, warn = [], [], []
    tw_b = tw_m = 0.0
    for k in sorted(got):
        w, m = got[k]
        if k not in b:
            new.append(k); continue
        bw, bm = b[k]
        if not k.startswith("lane:"):
            tw_b += bw; tw_m += w
        limit = max(FACTOR * bw, bw + FLOOR)
        if w > limit:
            bad.append("SLOW %s: baseline %.1fs, measured %.1fs, ratio %.2f (limit %.1fs)" % (k, bw, w, w / max(bw, 0.001), limit))
        if m > FACTOR * bm and m > bm + 1.0 and bm > 0:
            warn.append("memory %s: baseline %.2f GiB, measured %.2f GiB" % (k, bm, m))
    if tw_b > 0 and tw_m > FACTOR * tw_b:
        bad.append("SLOW total pool work: baseline %.0fs, measured %.0fs, ratio %.2f" % (tw_b, tw_m, tw_m / tw_b))
    print("total pool work: baseline %.0fs, measured %.0fs (%.2fx)" % (tw_b, tw_m, tw_m / tw_b if tw_b else 0))
    for k in new:
        print("NEW (no baseline, not failed): %s %.1fs" % (k, got[k][0]))
    for w in warn:
        print("warning: " + w)
    for x in bad:
        print(x)
    if bad:
        print("SPEED CHECK FAILED: %d regression(s)" % len(bad))
        return 1
    print("speed check ok")
    return 0

sys.exit(main())
