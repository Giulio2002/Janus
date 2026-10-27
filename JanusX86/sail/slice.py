#!/usr/bin/env python3
"""Slice sail-x86-from-acl2's model to the opcodes Janus' amd64 decoder accepts (docs/X86FORMAL.md).

    slice.py MODEL_DIR OUT_DIR KEEP_FILE

MODEL_DIR is sail-x86-from-acl2/model at the pinned commit; OUT_DIR receives a copy of every
`.sail` file with these source edits (each one listed in the JSON statistics printed on stdout):

* **Dispatch arms.** In `one_byte_opcode_execute` (step.sail) and `two_byte_opcode_execute`
  (two_byte_opcodes_dispatch.sail), the arm of every opcode that is not listed in KEEP_FILE
  becomes `N => x86_model_error("janus-excluded: ...")`. The arms that are kept are verbatim
  (decode checks, mode checks, `#UD` conditions and the call into the semantic function).
  The prefix, ModRM and SIB decoders (`get_prefixes`, `x86_fetch_decode_execute`,
  `two_byte_opcode_decode_and_execute`) are untouched, so every byte of an instruction is
  still decoded by the model.
* **VEX/EVEX.** `vex_decode_and_execute` and `evex_decode_and_execute` become one
  `x86_model_error("janus-excluded: VEX/EVEX ...")`: the model implements no VEX or EVEX
  instruction (every arm of its VEX/EVEX maps is "Opcode Unimplemented in x86isa!" or a
  fault), and the maps are about 4 MB of Lean. Janus' VEX instructions are tested by the
  native oracle only.
* **Faults.** `x86_fault(msg)` throws a new exception constructor `Efault(msg)` instead of
  `Emsg("Fault: " ^ msg)`, so that the harness tells architectural faults (`#UD`, `#GP`,
  `#DE`, alignment) from model errors (unimplemented, janus-excluded) without string
  matching. Nothing in the model catches either.
* **get_prefixes.** Its recursive calls pass `cnt - 1` instead of `check_range(0, 15, cnt - 1)`
  (the same value; the range is implied by the types), so that the recursion argument is pure
  and Lean can check the termination measure (termination_measures.sail).
* **Undefined values.** `undef_read_logic()` (the source of every undefined flag and of the
  undefined rotate results) returns the register `janus_undef` instead of Sail's
  `undefined`, as oracle-amd64-formal/build.sh does with `undef_val`: the check runs each
  case with 0 and with 1 and treats a flag that differs as undefined.
"""
import json
import os
import re
import shutil
import sys

src, out, keepf = sys.argv[1], sys.argv[2], sys.argv[3]
keep = {"one": set(), "two": set()}
for line in open(keepf):
    line = line.split("#")[0].strip()
    if not line:
        continue
    m, rng = line.split()
    lo, _, hi = rng.partition("-")
    for v in range(int(lo, 16), int(hi or lo, 16) + 1):
        keep[m].add(v)

os.makedirs(out, exist_ok=True)
for f in os.listdir(src):
    if f.endswith(".sail"):
        shutil.copy(os.path.join(src, f), os.path.join(out, f))
stats = {}


def edit(fname, fn, noop_ok=False):
    p = os.path.join(out, fname)
    s = open(p).read()
    s2 = fn(s)
    assert noop_ok or s2 != s, fname
    open(p, "w").write(s2)


def slice_dispatch(s, func, which, label):
    """Replace the excluded arms of `match opcode { ... }` in `func`."""
    start = s.index("function %s (" % func)
    mstart = s.index("(match opcode {\n", start)
    mend = s.index("\n          _ => ", mstart)
    body = s[mstart:mend]
    lines = body.split("\n")
    head, arms, cur = [lines[0]], [], None
    for l in lines[1:]:
        m = re.match(r"^          (\d+) => ", l)
        if m:
            cur = [int(m.group(1)), [l]]
            arms.append(cur)
        else:
            assert cur is not None, l
            cur[1].append(l)
    kept = dropped = 0
    new = []
    for op, ls in arms:
        txt = "\n".join(ls)
        assert txt.endswith(","), (func, op, txt[-40:])
        if op in keep[which]:
            new.append(txt)
            kept += 1
        else:
            new.append('          %d => x86_model_error("janus-excluded: %s opcode 0x%02x"),' % (op, label, op))
            dropped += 1
    stats[func] = {"kept": kept, "excluded": dropped}
    return s[:mstart] + "\n".join(head + new) + s[mend:]


# noop_ok: with a keep list that covers a whole map nothing is replaced (keep.txt)
edit("step.sail", lambda s: slice_dispatch(s, "one_byte_opcode_execute", "one", "one-byte"), noop_ok=True)
edit("two_byte_opcodes_dispatch.sail",
     lambda s: slice_dispatch(s, "two_byte_opcode_execute", "two", "two-byte 0F"), noop_ok=True)


def stub_function(s, func, msg):
    start = s.index("function %s (" % func)
    brace = s.index(") = {\n", start) + len(") = ")
    # the function body ends at the first line that is exactly "}"
    end = s.index("\n}\n", brace) + 2
    stats[func] = "stubbed"
    return s[:brace] + '{\n    x86_model_error("%s")\n}' % msg + s[end:]


edit("vex_opcodes_dispatch.sail", lambda s: stub_function(
    s, "vex_decode_and_execute", "janus-excluded: VEX (no VEX instruction is implemented in x86isa)"))
edit("evex_opcodes_dispatch.sail", lambda s: stub_function(
    s, "evex_decode_and_execute", "janus-excluded: EVEX (no EVEX instruction is implemented in x86isa)"))


def prelude(s):
    s = s.replace("union exception = {\n\tEmsg : string,",
                  "union exception = {\n\tEmsg : string,\n\tEfault : string,")
    s = s.replace('function x86_fault(msg) = throw(Emsg("Fault: " + msg))',
                  'function x86_fault(msg) = throw(Efault(msg))')
    s = s.replace("val undef_read_logic : unit -> nat\nfunction undef_read_logic () = undefined",
                  "register janus_undef : nat\nval undef_read_logic : unit -> nat\n"
                  "function undef_read_logic () = janus_undef")
    assert "Efault(msg)" in s and "janus_undef" in s and "Efault : string" in s
    return s


edit("prelude.sail", prelude)


def get_prefixes(s):
    start = s.index("function get_prefixes (")
    end = s.index("\n}\n", start)
    body = s[start:end]
    n = body.count("check_range(0, 15, cnt - 1)")
    assert n == 7, n
    stats["get_prefixes"] = {"check_range removed": n}
    return s[:start] + body.replace("check_range(0, 15, cnt - 1)", "cnt - 1") + s[end:]


# get_prefixes recurses on `check_range(0, 15, cnt - 1)`, an assertion (monadic in Lean) whose
# result is its argument. Its range already follows from the type check (cnt : range(0, 15) and
# cnt != 0 in the else branch), so the call passes `cnt - 1` directly. That makes the recursion
# argument pure, and Lean can check termination_measures.sail's measure `cnt`.
edit("step.sail", get_prefixes)
# the dispatch maps that the stubs no longer reach are left in the files; the slicing plugin
# drops everything not reachable from the harness roots.
print(json.dumps(stats, indent=1, sort_keys=True))
