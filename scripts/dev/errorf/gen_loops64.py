#!/usr/bin/env python3
"""Generate Janus/Contracts/ErrorfRealLoops64.lean (amd64 loop lemmas) from scripts/errorf/loop_templates64.py. Run from the repo root."""
import sys
sys.path.insert(0, "scripts/errorf")
import gen_amd64
from loop_templates64 import HDR, DIG, CPY
_, lab = gen_amd64.build()
pc = lambda k: hex(gen_amd64.E0 + lab[k])
out = HDR
for n in ("n1", "n2"):
    out += DIG.replace("@N@", n).replace("@H@", pc(n + "d")).replace("@X@", pc(n + "s")) + "\n"
for n in ("c1", "c2", "c3"):
    out += CPY.replace("@N@", n).replace("@H@", pc(n)).replace("@X@", pc(n + "e")) + "\n"
out += "end Janus.Contracts.ErrorfRealLoops64\n"
open("Janus/Contracts/ErrorfRealLoops64.lean", "w").write(out)
