#!/usr/bin/env python3
"""Compare the Lean model's FSQRT results with Sail's C backend (audit/rt-asl/run.sh, A5 fsqrt).

    compare.py CASES LEAN_JSONL C_JSONL

LEAN_JSONL: `janus-asl-check --dump-asl CASES` (JanusASL's generated Lean model, with the
`sqrt_real` replacement of JanusASL/sail/fakereal_sqrt.py). C_JSONL: oracle-sail's driver on the
same cases (sail-arm compiled by Sail's C backend, whose `sqrt_real` is GMP Newton iteration).
Both must complete every case with the same V0-V31 and FPSR. Prints one summary line, and the
first differences; exits 1 on any difference.
"""
import json, sys
from collections import Counter

def h(s): return int(s, 16)

cases = {}
for l in open(sys.argv[1]):
    if l.strip():
        c = json.loads(l); cases[c["id"]] = c
lean = {json.loads(l)["id"]: json.loads(l) for l in open(sys.argv[2]) if l.strip()}
csail = {json.loads(l)["id"]: json.loads(l) for l in open(sys.argv[3]) if l.strip()}
bad = []
kinds = Counter()
for i, c in cases.items():
    a, b = lean.get(i), csail.get(i)
    if a is None or b is None:
        bad.append((i, "missing result")); continue
    if a["status"] != "ok" or b["status"] != "ok":
        bad.append((i, f"status lean {a['status']} c {b['status']}")); continue
    va, vb = [h(x) for x in a["v"]], [h(x) for x in b["v"]]
    if va != vb:
        bad.append((i, f"V differ: lean V0 {hex(va[0])} c V0 {hex(vb[0])} (operand {c['v'][1]}, fpcr {c['fpcr']})")); continue
    if h(a["fpsr"]) != h(b["fpsr"]):
        bad.append((i, f"FPSR differ: lean {a['fpsr']} c {b['fpsr']} (operand {c['v'][1]}, fpcr {c['fpcr']})")); continue
    kinds[c["class"]] += 1
print(f"fsqrt: {len(cases)} cases, {sum(kinds.values())} equal ({dict(kinds)}), {len(bad)} differ")
for i, w in bad[:10]:
    print(f"  case {i}: {w}")
sys.exit(1 if bad or not cases else 0)
