#!/usr/bin/env python3
"""Generate Janus/Contracts/ErrorfRealLoops.lean: the loop lemmas of the arm64 real-format stub, instantiated at the
label addresses of scripts/dev/errorf/gen_arm64.py. Run from the repo root."""
import sys
sys.path.insert(0, "scripts/dev/errorf")
import gen_arm64
from loop_templates import HDR, DIG, CPY
_, lab = gen_arm64.build()
pc = lambda k: hex(gen_arm64.E0 + 4 * lab[k])
out = HDR
for n, head, exit_ in (("n1", "n1d", "n1s"), ("n2", "n2d", "n2s")):
    out += DIG.replace("@N@", n).replace("@H@", pc(head)).replace("@X@", pc(exit_)) + "\n"
for n, head, exit_ in (("c1", "c1", "c1e"), ("c2", "c2", "c2e"), ("c3", "c3", "c3e")):
    out += CPY.replace("@N@", n).replace("@H@", pc(head)).replace("@X@", pc(exit_)) + "\n"
out += "end Janus.Contracts.ErrorfRealLoops\n"
open("Janus/Contracts/ErrorfRealLoops.lean", "w").write(out)
