#!/usr/bin/env python3
"""Report of a gate run: python3 -I scripts/gate-report.py artifacts/gate/<run>/timeline.jsonl [--json]

Reads the machine-readable timeline written by scripts/gate.sh (one JSON object per line):
  {"kind":"gate",...}                     the run (commit, jobs, lanes, host load)
  {"kind":"prebuild"|"stage",...}         prebuild steps and stages (start/end epoch seconds, wall, rc)
  {"kind":"item","pool":P,"id":I,...}     one finished item or lane of pool P (status PASS/FAIL/TIMEOUT/...)
  {"kind":"pool","pool":P,...}            one pool (items, failures, jobs, start, end)
Prints the stages, each pool's wall and its busy time (the sum of the item walls) and slot utilisation,
the lanes with their start offsets and walls, the longest items and the critical path (the lane that
ends last)."""
import json, sys

def main():
    path = sys.argv[1]
    rows = [json.loads(l) for l in open(path) if l.strip()]
    gate = next((r for r in rows if r["kind"] == "gate"), {})
    t0 = gate.get("start", min((r.get("start", 1e18) for r in rows), default=0))
    print("---- gate timeline (%s) ----" % path)
    print("run: commit %s, -j %s, %s lanes, load %s, %s GiB free, %s cores" % (
        gate.get("commit"), gate.get("jobs"), gate.get("lanes"), gate.get("load1"), gate.get("memAvailGiB"), gate.get("cores")))
    print("%-34s %9s %9s %9s  %s" % ("stage", "start", "end", "wall", "rc"))
    for r in rows:
        if r["kind"] in ("prebuild", "stage"):
            print("%-34s %8.0fs %8.0fs %8.0fs  %s" % (r["kind"] + ":" + r["name"], r["start"] - t0, r["end"] - t0, r["wall"], r["rc"]))
    pools = [r for r in rows if r["kind"] == "pool"]
    for p in pools:
        items = [r for r in rows if r["kind"] == "item" and r["pool"] == p["pool"]]
        busy = sum(r["wall"] for r in items)
        wall = p["end"] - p["start"]
        util = busy / (wall * p["jobs"]) if wall > 0 else 0
        print("pool %-10s %4d items, %d failed, -j %s: wall %.0fs, busy %.0fs, slot utilisation %.0f%%" % (
            p["pool"], p["items"], p["failed"], p["jobs"], wall, busy, util * 100))
    lanes = sorted((r for r in rows if r["kind"] == "item" and r["pool"] == "gate"), key=lambda r: r["start"])
    if lanes:
        print("%-16s %9s %9s %9s  %s" % ("lane", "start", "end", "wall", "status"))
        for r in lanes:
            print("%-16s %8.0fs %8.0fs %8.0fs  %s" % (r["id"], r["start"] - t0, r["end"] - t0, r["wall"], r["status"]))
        last = max(lanes, key=lambda r: r["end"])
        print("critical path: lane %s (ends at %.0fs)" % (last["id"], last["end"] - t0))
    items = sorted((r for r in rows if r["kind"] == "item" and r["pool"] != "gate"), key=lambda r: -r["wall"])[:12]
    if items:
        print("longest items:")
        for r in items:
            print("  %-34s %8.0fs  %s" % (r["id"], r["wall"], r["status"]))
    # RAN or SKIPPED, for every item and lane (a skip replays a recorded PASS of identical inputs)
    allitems = [r for r in rows if r["kind"] == "item"]
    skipped = [r for r in allitems if r["status"] == "SKIP"]
    ran = [r for r in allitems if r["status"] != "SKIP"]
    print("---- RAN / SKIPPED ----")
    if not skipped:
        print("full run: all %d items and lanes RAN, none skipped" % len(allitems))
    else:
        for r in sorted(allitems, key=lambda r: (r["pool"], r["id"])):
            if r["status"] == "SKIP":
                print("SKIPPED %-8s %-34s replays: %s" % (r["pool"], r["id"], r.get("note", "?")))
            else:
                print("RAN     %-8s %-34s %8.1fs  %s" % (r["pool"], r["id"], r["wall"], r["status"]))
        print("totals: %d items and lanes, %d RAN (%.0fs of work), %d SKIPPED (replaying PASS records of %.0fs of work)" % (
            len(allitems), len(ran), sum(r["wall"] for r in ran), len(skipped), sum(float(x) for x in
            [__import__("re").sub(r".*?, ([0-9.]+)s then.*", r"\1", r.get("note", "")) if "s then" in r.get("note", "") else "0" for r in skipped])))
    bad = [r for r in rows if r["kind"] == "item" and r["status"] not in ("PASS", "SKIP")]
    if bad:
        print("not passed: " + ", ".join("%s/%s=%s" % (r["pool"], r["id"], r["status"]) for r in bad))

main()
