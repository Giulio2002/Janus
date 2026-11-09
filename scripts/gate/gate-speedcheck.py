#!/usr/bin/env python3
"""Speed-regression check of a gate run (on top of every other check, never instead of one).

  python3 -I scripts/gate-speedcheck.py check  TIMELINE BASELINE [LOGDIR]
  python3 -I scripts/gate-speedcheck.py seed   TIMES OUT   (provisional baseline from artifacts/verify-all-examples.times)
  python3 -I scripts/gate-speedcheck.py update TIMELINE BASELINE [LOGDIR]   (rewrite BASELINE from a run)

TIMELINE is <gate out>/timeline.jsonl; BASELINE is the committed scripts/speed-baseline.tsv
("id<TAB>wall seconds<TAB>peak GiB", one line per item of the verify pool and per lane); LOGDIR (default
the timeline's directory + /verify) holds the items' logs, and ARTIFACTS (the checkout's artifacts/ directory) holds the items' verified.json / verified/*.json, whose memoryGuard.peakBytes (janus's own accounting, no extra cgroup) is the item's peak, the largest over its theorems; the logs' "memguard[...]: peak" lines are the fallback for an item with no report.

check fails (exit 1) if
  * an item that PASSED took more than max(1.5 x baseline, baseline + 10 s)  (the absolute floor keeps
    items of a few seconds from flapping on noise; the message names the item, baseline, measured wall, ratio),
  * the total pool work (sum of the walls of the items present in both) exceeds 1.5 x the baseline's.
New items (no baseline line) are reported, not failed; they enter the baseline at the next `update`.
Items overlapping an external pause (<out>/pauses.txt) are excluded from both. Items that did not pass are the pass/fail checks' business and are not judged here. The host load of the
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

def report_dirs(artroot, item):
    """The artifact directory of a pool item (where janus wrote verified.json and verified/<theorem>.json)."""
    kind, _, n = item.partition(":")
    if kind == "arm64":
        return os.path.join(artroot, n)
    if kind == "amd64":
        return os.path.join(artroot, "amd64", n)
    if kind in ("asm", "rtmisc", "sys", "print", "cgo"):
        return os.path.join(artroot, kind, n)
    return None

def report_peak(artroot, item, since):
    """The item's peak memory in GiB from janus's own records: the largest memoryGuard.peakBytes over its
    verified.json and verified/*.json written since SINCE (so an old run's report is never used). No cgroup of
    its own: janus's memguard accounts every Lean job it starts. 0 when it wrote none (a failed item)."""
    d = report_dirs(artroot, item) if artroot else None
    if not d or not os.path.isdir(d):
        return 0.0
    best = 0.0
    paths = [os.path.join(d, "verified.json")]
    vd = os.path.join(d, "verified")
    if os.path.isdir(vd):
        paths += [os.path.join(vd, f) for f in os.listdir(vd) if f.endswith(".json")]
    for f in paths:
        try:
            if os.path.getmtime(f) < since:
                continue
            best = max(best, float(json.load(open(f)).get("memoryGuard", {}).get("peakBytes", 0)) / 2**30)
        except (OSError, ValueError, AttributeError):
            pass
    return best

def filekey(i):  # pool.sh's log file name for an id
    return i.replace("/", "_").replace(":", "_")

def pauses(tl):
    """Intervals in which the run was stopped externally (<out>/pauses.txt: "start end" epoch seconds, end
    may be empty = until the end): items overlapping one are timing-invalid and neither judged nor recorded."""
    f = os.path.join(os.path.dirname(tl), "pauses.txt")
    out = []
    if os.path.exists(f):
        for l in open(f):
            w = l.split()
            if w:
                out.append((float(w[0]), float(w[1]) if len(w) > 1 else 1e18))
    return out

def measured(rows, logdir, paused=(), artroot="", since=0.0):
    pk = peaks(logdir)
    res = {}
    for r in rows:
        if r.get("kind") == "item" and r.get("status") in ("PASS",):
            if any(r["start"] < pe and r["end"] > ps for ps, pe in paused):
                print("timing-invalid (overlaps a pause, excluded): %s/%s" % (r["pool"], r["id"]))
                continue
            if r["pool"] == "gate" and (r["id"].startswith("pre-") or r["id"].startswith("tree-")):
                continue   # prebuild stages and tree copies are scheduling steps, not lanes: not a baseline row
            key = ("lane:" if r["pool"] == "gate" else "") + r["id"]
            m = 0.0
            if r["pool"] != "gate":
                m = max(pk.get(filekey(r["id"]), 0.0), report_peak(artroot, r["id"], since))
            res[key] = (r["wall"], m)
    return res

def read_base(path):
    b = {}
    for l in open(path):
        if l.strip() and not l.startswith("#"):
            k, w, m = l.rstrip("\n").split("\t")
            b[k] = (float(w), float(m))
    return b

def seed(times, out):
    """Provisional baseline from a verify-all-examples.times file ("id<TAB>seconds"); peak memory unknown (0)."""
    with open(out, "w") as f:
        f.write("# PROVISIONAL speed baseline derived from %s (not recorded by a gate run; do not enforce)\n" % times)
        for l in sorted(open(times)):
            k, w = l.rstrip("\n").split("\t")[:2]
            f.write("%s\t%.1f\t0.00\n" % (k, float(w)))
    print("provisional baseline written to %s" % out)
    return 0

def main():
    if sys.argv[1] == "seed":
        return seed(sys.argv[2], sys.argv[3])
    mode, tl, base = sys.argv[1:4]
    rows = load_tl(tl)
    logdir = sys.argv[4] if len(sys.argv) > 4 else os.path.join(os.path.dirname(tl), "verify")
    artroot = sys.argv[5] if len(sys.argv) > 5 else ""
    gate0 = next((r for r in rows if r["kind"] == "gate"), {}).get("start", 0) - 60
    got = measured(rows, logdir, pauses(tl), artroot, gate0)
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
