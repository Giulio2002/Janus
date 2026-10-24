#!/usr/bin/env python3
"""Split Sail's single-file Lean output into a chain of modules (docs/ASL.md).

    split_lean.py ArmASL.lean OUTDIR [N]           N parts of about equally many declarations
    split_lean.py ArmASL.lean OUTDIR --bytes B     parts of at most B bytes of declarations

Sail's `--lean-single-file` writes one ~50k-line `ArmASL.lean`. Elaborating it is one
sequential job of tens of minutes that reports nothing until it ends. This script cuts it, at
top-level declaration boundaries only, into consecutive modules `ArmASL/Part<k>.lean`; part
k imports part k-1 and repeats the file header (options, `namespace ArmASL`, `namespace
Functions`, the `open`s), and `ArmASL.lean` becomes `import ArmASL.Part<last>`. The declarations,
their order and their text are unchanged (each part ends with `end ArmASL.Functions`, so the
namespaces are the same). Lake then caches and reports per part.

With `--bytes B` (what `scripts/asl.sh gen` uses) the parts are filled greedily in order up to B
bytes, and a declaration larger than B gets a part of its own: the memory of elaborating a part
grows with its size (docs/ASL.md, "Memory"), so the few huge decode and system-register
functions are isolated and the rest is cut into many small parts.
"""
import os
import re
import sys

src, outdir = sys.argv[1], sys.argv[2]
nbytes = None
if len(sys.argv) > 4 and sys.argv[3] == "--bytes":
    nbytes = int(sys.argv[4])
    n = None
else:
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 16
L = open(src).read().split("\n")

# header: everything before the first declaration (imports, options, namespaces, opens)
first = next(i for i, l in enumerate(L) if re.match(r"(def|abbrev|/--|@\[|theorem|instance|mutual|noncomputable|partial) ", l) or l == "mutual")
header, body = L[:first], L[first:]
imports = [l for l in header if l.startswith("import ")]
rest = [l for l in header if not l.startswith("import ")]
assert body[-1] == "" or True
# trailing `end ArmASL.Functions` (and possibly blank lines)
while body and body[-1].strip() == "":
    body.pop()
assert body[-1].startswith("end "), body[-1]
tail = body.pop()

# declaration starts at column 0, outside `mutual ... end` blocks
starts, depth = [], 0
for i, l in enumerate(body):
    if l == "mutual":
        if depth == 0:
            starts.append(i)
        depth += 1
        continue
    if depth and l == "end":
        depth -= 1
        continue
    if depth == 0 and re.match(r"(def|abbrev|theorem|instance|noncomputable|partial|/--|@\[)", l):
        if i > 0 and (body[i - 1].startswith("/--") or body[i - 1].startswith("@[")):
            continue  # attached to the doc comment / attribute line above
        starts.append(i)
assert depth == 0
if nbytes is None:
    per = max(1, len(starts) // n)
    cuts = [0] + [starts[k * per] for k in range(1, n) if k * per < len(starts)]
else:
    size = [len(l) + 1 for l in body]
    ends = starts[1:] + [len(body)]
    assert starts[0] == 0
    cuts, cur = [0], 0
    for a, b in zip(starts, ends):
        d = sum(size[a:b])
        if cur and cur + d > nbytes:
            cuts.append(a)
            cur = 0
        cur += d
cuts.append(len(body))
os.makedirs(os.path.join(outdir, "ArmASL"), exist_ok=True)
parts = []
for k in range(len(cuts) - 1):
    name = ("Part%02d" if len(cuts) <= 100 else "Part%03d") % (k + 1)
    imp = imports if k == 0 else ["import ArmASL.%s" % parts[-1]]
    text = imp + rest + body[cuts[k]:cuts[k + 1]] + ["", tail, ""]
    open(os.path.join(outdir, "ArmASL", name + ".lean"), "w").write("\n".join(text))
    parts.append(name)
open(os.path.join(outdir, "ArmASL.lean"), "w").write(
    "-- Sail-generated model, split by JanusASL/sail/split_lean.py\nimport ArmASL.%s\n" % parts[-1])
print(len(parts), "parts")
