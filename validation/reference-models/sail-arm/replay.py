#!/usr/bin/env python3
"""Serve precomputed results as an `oracle run -model` (or -runner) executable.

usage: replay.py RESULTS.jsonl < cases.jsonl > results-for-those-cases.jsonl

Prints, for every case on stdin (in order), the line of RESULTS.jsonl with the same "id"
(or a status=error line if there is none). Lets the qemu agent's comparator
(`oracle run -reuse-native`) diff qemu against Sail without re-running the Sail model.
"""
import json
import sys

by_id = {}
with open(sys.argv[1]) as f:
    for line in f:
        line = line.strip()
        if line:
            by_id[json.loads(line).get("id")] = line
out = sys.stdout
for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    cid = json.loads(line).get("id")
    out.write(by_id.get(cid) or json.dumps({"id": cid, "status": "error", "nzcv": 0}))
    out.write("\n")
