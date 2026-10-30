#!/usr/bin/env python3
"""Split the (instrumented) Sail model.cpp into N translation units, byte-for-byte same semantics.

usage: split_model.py IN/model.cpp OUTDIR N

The generated model.cpp is one 170 MB translation unit; g++ compiles it serially (~24 min).
Its layout is (checked below, every assumption is asserted, a surprise aborts the split):

  PREAMBLE   extern "C" counters, includes, `namespace sail_aarch64 {`, then ~2.7k `static`
             helper functions for the Sail types (CREATE/COPY/KILL/EQUAL ...)
  BODY       top-level items at namespace scope: `Model::` member function definitions
             (declared in model.h) and the ghost temporaries `T zghzN;` (namespace-scope
             globals, each used only by the functions that follow it)
  TAIL       closing `}` of the namespace, then extern "C"/free functions (model_main ...)

Every part_NN.cpp is: the preamble (statics are internal-linkage, so every unit gets its own
copy; the two process-global definitions are kept in part 0 and become declarations elsewhere),
then a consecutive run of BODY items, then (last part only) the TAIL. Items are never cut, a
ghost temporary stays in the same part as every use (asserted), so the union of the parts
defines exactly the functions and globals of the original, each once. Parts are balanced by
size. Output is deterministic (no timestamps, no randomness).
"""
import re
import sys

src, outdir, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
lines = open(src, encoding="utf-8", errors="surrogateescape").read().split("\n")
assert lines[-1] == ""  # file ends with a newline
lines.pop()

STR = re.compile(r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])+\'')
CMT = re.compile(r'//.*$')

def delta(line):
    t = CMT.sub("", STR.sub('""', line))
    return t.count("{") - t.count("}")

# ---- preamble: everything before the first `Model::` member definition -------------------
hdr = re.compile(r'^[A-Za-z_][A-Za-z_0-9:<>\s\*&,]* Model::[A-Za-z_0-9]+\(.*\)\s*(\{)?$')
first = next(i for i, l in enumerate(lines) if hdr.match(l))
# the namespace opens in the preamble; the model's first member sits after the statics
assert any(l == "namespace sail_aarch64 {" for l in lines[:first])
pre = lines[:first]
exp_head = ['extern "C" { unsigned long long janus_sail_unpredictable = 0; unsigned long long janus_sail_uncaught = 0; }',
            '#include "sail.h"', '#include "sail_config.h"', '#include "rts.h"', '#include "elf.h"',
            'void (*sail_rts_set_coverage_file)(const char *) = NULL;', '#include "model.h"']
assert pre[:7] == exp_head, pre[:7]
pre_other = pre[7:]
pre_head0 = pre[:7]
pre_head_k = ['extern "C" { extern unsigned long long janus_sail_unpredictable; extern unsigned long long janus_sail_uncaught; }'] + pre[1:5] + [pre[6]]
# no other process-global definitions in the preamble (statics only), no static state
depth = 0
for l in pre_other:
    d = delta(l)
    if depth == 0 and l.startswith("namespace sail_aarch64 {"):
        depth = 1
        continue
    if depth == 1 and d == 0 and l.strip() and not l.startswith("static ") and not l.startswith(" ") and not l.startswith("}") and not l.startswith("//"):
        assert l.endswith(";") or l.startswith("#") , l   # prototypes only
    depth += d
assert depth == 1, depth
assert not re.search(r'^[ \t]+static\s', "\n".join(pre_other), re.M), "static local state in preamble"

# ---- body items --------------------------------------------------------------------------
items = []   # (kind, text_lines)
i = first
depth = 1  # inside namespace
cur = []
tail_at = None
ghost = re.compile(r'^(?:static )?(?:[A-Za-z_][A-Za-z_0-9 \*]*?) (zghz\d+|sail_scratch_refs)(?: = 0)?;(?: /\* fix_cpp_model.py \*/)?$')
while i < len(lines):
    l = lines[i]
    if depth == 1 and l == "} // namespace sail_aarch64" and not cur:
        # end of namespace
        tail_at = i
        break
    cur.append(l)
    depth += delta(l)
    i += 1
    if depth == 1:
        if len(cur) == 1 and ghost.match(cur[0]):
            items.append(("ghost", cur)); cur = []
        elif len(cur) == 1 and re.match(r'^Model::~?Model\(\) \{ \}$', cur[0]):
            items.append(("fn", cur)); cur = []
        elif cur[-1] == "}" and hdr.match(cur[0]):
            items.append(("fn", cur)); cur = []
        elif not any(x.strip() for x in cur):
            items.append(("blank", cur)); cur = []
        elif hdr.match(cur[0]) and cur[0].endswith(")") is False:
            pass
        elif cur[0].startswith("{") is False and len(cur) >= 1 and hdr.match(cur[0]) is None and not ghost.match(cur[0]) and cur[0].strip():
            raise SystemExit("unclassified top-level item at line %d: %r" % (i, cur[0][:100]))
assert tail_at is not None and not cur, "namespace close not found"
tail = lines[tail_at:]
kinds = {}
for k, t in items:
    kinds[k] = kinds.get(k, 0) + 1
assert set(kinds) <= {"ghost", "fn", "blank"}, kinds
# function items must be balanced single definitions
for k, t in items:
    if k == "fn":
        assert sum(delta(x) for x in t) == 0

# ---- ghost temporaries: each used only in the part that defines it ----------------------
ghost_def = {}
for idx, (k, t) in enumerate(items):
    if k == "ghost":
        ghost_def[ghost.match(t[0]).group(1)] = idx
use = re.compile(r'\b(?:zghz\d+|sail_scratch_refs)\b')
# group consecutive items so a ghost and all its users are one atomic group
owner = {}      # ghost name -> item index of a user (first), must be after def
groups = []     # list of lists of item indices; atomic units
user_item = {}
for idx, (k, t) in enumerate(items):
    if k == "ghost":
        continue
    for name in set(use.findall("\n".join(t))):
        user_item.setdefault(name, []).append(idx)
# union-find over items: ghost def ~ its users
par = list(range(len(items)))
def find(a):
    while par[a] != a:
        par[a] = par[par[a]]; a = par[a]
    return a
def union(a, b):
    a, b = find(a), find(b)
    if a != b: par[max(a, b)] = min(a, b)
for name, d in ghost_def.items():
    for u in user_item.get(name, []):
        assert u > d, "use before definition: " + name
        union(d, u)
for name in user_item:
    assert name in ghost_def, "undefined ghost " + name
# merge atomic groups: any group must be contiguous range; otherwise glue the span between
changed = True
while changed:
    changed = False
    spans = {}
    for idx in range(len(items)):
        r = find(idx)
        lo, hi = spans.get(r, (idx, idx)); spans[r] = (min(lo, idx), max(hi, idx))
    for r, (lo, hi) in spans.items():
        for j in range(lo, hi + 1):
            if find(j) != find(lo):
                union(lo, j); changed = True
units = []
for idx in range(len(items)):
    if find(idx) == idx:
        units.append([])
    # attach to its root's unit (root is smallest index of its group; contiguous)
    units[-1].append(idx)
sizes = [sum(len("\n".join(items[j][1])) + 1 for j in u) for u in units]
total = sum(sizes)
# greedy balanced cut into n consecutive parts
parts, cur_p, acc = [], [], 0
for u, sz in zip(units, sizes):
    cur_p.append(u); acc += sz
    if len(parts) < n - 1 and acc >= total * (len(parts) + 1) / n:
        parts.append(cur_p); cur_p = []
if cur_p:
    parts.append(cur_p)
psize = [sum(sizes[units.index(u)] for u in p) if False else 0 for p in parts]
import os
os.makedirs(outdir, exist_ok=True)
for pi, p in enumerate(parts):
    body = []
    for u in p:
        for j in u:
            body.extend(items[j][1])
    head = pre_head0 if pi == 0 else pre_head_k
    out = head + pre_other + body
    if pi == len(parts) - 1:
        out += tail
    else:
        out += ["} // namespace sail_aarch64"]
    with open(os.path.join(outdir, "model_part_%02d.cpp" % pi), "w", encoding="utf-8", errors="surrogateescape", newline="\n") as f:
        f.write("\n".join(out) + "\n")
print("split %d items (%d fn, %d ghost) in %d units into %d parts; largest unit %d bytes of %d" % (
    len(items), kinds.get("fn", 0), kinds.get("ghost", 0), len(units), len(parts), max(sizes), total))
