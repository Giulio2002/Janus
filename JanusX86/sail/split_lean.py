#!/usr/bin/env python3
"""Split Sail's single-file Lean output into a chain of modules (docs/X86FORMAL.md (copied from JanusASL/sail/split_lean.py with the module name changed)).

    split_lean.py X86Sail.lean OUTDIR [N]

Sail's `--lean-single-file` writes one ~50k-line `X86Sail.lean`. Elaborating it is one
sequential job of tens of minutes that reports nothing until it ends. This script cuts it, at
top-level declaration boundaries only, into N consecutive modules of about equally many declarations, `X86Sail/Part<k>.lean`; part
k imports part k-1 and repeats the file header (options, `namespace X86Sail`, `namespace
Functions`, the `open`s), and `X86Sail.lean` becomes `import X86Sail.Part<N>`. The declarations,
their order and their text are unchanged (each part ends with `end X86Sail.Functions`, so the
namespaces are the same). Lake then caches and reports per part.
"""
import os
import re
import sys

src, outdir = sys.argv[1], sys.argv[2]
n = int(sys.argv[3]) if len(sys.argv) > 3 else 16
L = open(src).read().split("\n")

# header: everything before the first declaration (imports, options, namespaces, opens)
first = next(i for i, l in enumerate(L) if re.match(r"(def|abbrev|/--|@\[|theorem|instance|mutual|noncomputable|partial) ", l) or l == "mutual")
header, body = L[:first], L[first:]
imports = [l for l in header if l.startswith("import ")]
rest = [l for l in header if not l.startswith("import ")]
assert body[-1] == "" or True
# trailing `end X86Sail.Functions` (and possibly blank lines)
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
per = max(1, len(starts) // n)
cuts = [0] + [starts[k * per] for k in range(1, n) if k * per < len(starts)]
cuts.append(len(body))
os.makedirs(os.path.join(outdir, "X86Sail"), exist_ok=True)
parts = []
for k in range(len(cuts) - 1):
    name = "Part%02d" % (k + 1)
    imp = imports if k == 0 else ["import X86Sail.%s" % parts[-1]]
    text = imp + rest + body[cuts[k]:cuts[k + 1]] + ["", tail, ""]
    open(os.path.join(outdir, "X86Sail", name + ".lean"), "w").write("\n".join(text))
    parts.append(name)
open(os.path.join(outdir, "X86Sail.lean"), "w").write(
    "-- Sail-generated model, split by JanusASL/sail/split_lean.py\nimport X86Sail.%s\n" % parts[-1])
print(len(parts), "parts")
