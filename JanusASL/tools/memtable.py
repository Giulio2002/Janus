#!/usr/bin/env python3
"""Summarise a memprof.py JSON file: one row per Lean/clang process (module, peak MiB, wall s).

    memtable.py RUN.json [MIN_MIB]
"""
import json, re, sys
d = json.load(open(sys.argv[1]))
lo = int(sys.argv[2]) if len(sys.argv) > 2 else 0
rows = []
for p in d["procs"]:
    a = p["argv"]
    m = re.search(r"/bin/(lean|clang|leanchecker|janus-asl-check)\b", a)
    if not m:
        continue
    tool = m.group(1)
    f = re.search(r"/JanusASL/((?:ArmASL|JanusASL)/[^ ]*?)\.(lean|c)\b", a) or re.search(r" (\S+\.lean)", a)
    mod = f.group(1).replace("/", ".") if f else a[:80]
    if tool == "clang":
        mod += ":c.o"
    rows.append((p["hwm"] // 1024, int(p["last"] - p["first"]), tool, mod))
rows.sort(key=lambda r: -r[0])
print("run: %s  wall %.0f s  tree peak RSS %d MiB  anon %d MiB  scope %s MiB" % (
    " ".join(d["cmd"][-3:]), d["wall_s"], d["tree_peak_kib"] // 1024, d.get("tree_anon_peak_kib", 0) // 1024,
    (d.get("scope_peak_kib") or 0) // 1024))
for r in rows:
    if r[0] >= lo:
        print("%7d MiB %6d s  %-6s %s" % r)
