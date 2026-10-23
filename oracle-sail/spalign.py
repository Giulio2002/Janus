#!/usr/bin/env python3
"""Sail-only corpus: SP-based loads/stores with a misaligned SP.

usage: spalign.py CASES.jsonl > spalign.jsonl

qemu user mode does not check SP alignment (docs/ORACLE.md), so the qemu oracle can only show
that Janus's spMisaligned rule is conservative. The Sail model implements SCTLR_EL1.SA0 = 1
(Linux), so it can confirm or refute it. Takes every load/store case of the corpus whose base
register field is 31 (SP) and re-emits it with SP + k (k = 1..15, k = 8 included: 8-aligned
is still misaligned for SA0). Ids are offset by 50,000,000.
"""
import json
import sys

out = sys.stdout
n = 0
for line in open(sys.argv[1]):
    c = json.loads(line)
    cls = c.get("class", "").split("/")[-1]
    if not cls.startswith("ls.") or cls.startswith("ls.literal"):
        continue
    w = int(c["word"], 16)
    if (w >> 5) & 31 != 31:
        continue
    sp = int(c["sp"], 16)
    for k in (1, 4, 8, 12, 15):
        d = dict(c)
        d["id"] = 50_000_000 + n
        d["class"] = "spalign/" + cls
        d["sp"] = hex(((sp & ~15) + k) & (2**64 - 1))
        out.write(json.dumps(d) + "\n")
        n += 1
print(f"{n} spalign cases", file=sys.stderr)
