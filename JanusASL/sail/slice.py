#!/usr/bin/env python3
"""Slice the sail-arm arm-v9.4-a A64 decoder to the Janus subset (docs/ASL.md).

    slice.py SRC_DIR OUT_DIR KEEP_FILE

SRC_DIR is sail-arm's arm-v9.4-a/src. Every file is copied unchanged to OUT_DIR except the
instruction files:

* instrs64.sail: every `function clause __DecodeA64_<class>` of the five classes Janus
  decodes (DataProcImm, BranchExcSys, LoadStore, DataProcReg, DataProcFPSIMD) is KEPT IN PLACE, pattern and
  guard unchanged. A clause whose decode function is not listed in KEEP_FILE keeps its
  `SEE = n;` line, and its body is replaced by
  `throw(Error_ImplementationDefined("janus-excluded <decode function>"))`. Clauses are tried
  in order, so keeping every pattern means a word decodes to exactly the clause it decodes to
  in the full model; if that clause is excluded, the sliced model says so (it never falls
  through to a later clause). Clauses of the other A64 classes (SVE, SME, reserved)
  are dropped: their class function then throws `janus-excluded` too (decode_end.sail).
* instrs64_sve.sail, instrs64_sme.sail, instrs32.sail: emptied (only a comment remains). No
  Janus word reaches their decode classes (the top-level `__DecodeA64` dispatch is
  unchanged), and nothing outside them refers to their definitions.
* decode_end.sail: the catch-all clauses of the excluded A64 classes throw `janus-excluded`
  instead of `Error_Undefined` (so "not in the slice" is never mistaken for UNDEFINED); the
  four Janus classes keep their `Error_Undefined` catch-all.

* A clause whose pattern is a 32-bit literal, `(0b... as __opcode)` (22 system/hint clauses
  of BranchExcSys), is written with the equivalent bit-list pattern used by every other clause,
  `([bitone, bitzero, ...] as __opcode)` (most significant bit first). Sail 0.20.3's Lean
  pattern compilation duplicates the remaining clauses below every literal-pattern clause, so
  the 22 literals made `__DecodeA64_BranchExcSys` 207 MB of Lean; the bit-list form compiles to
  one `extractLsb ... == ...` test per clause like the others. The match semantics are equal.

* `janus_pac_splice.sail` (written to OUT_DIR, passed to `sail --splice`): copies of the
  pointer-authentication helpers PACInvSub, PACSub and PACSub1 from v8_base.sail with one
  change each: `match Tinput[4 * i + 3 .. 4 * i] {` becomes
  `let nibble : bits(4) = Slice(Tinput, 4 * i, 4); match nibble {`. The slice is the same
  4 bits; Lean cannot pattern-match on the original, whose width `4*i+3 - 4*i + 1` is not
  syntactically 4 ("dependent elimination failed"). They are reachable only through the PAC
  branches (BRAA, RETAA, ...) that share their execute function with BR/BLR/RET.

* `janus_sysreg_splice.sail` (OUT_DIR, `--splice`): the generated system-register dispatchers
  `AArch64_AutoGen_SysRegRead` (MRS) and `AArch64_AutoGen_SysOpsWrite` (SYS) of
  sysregs_autogen.sail reduced to the encodings Janus decodes. Each is a list of
  `if <op0, op1, CRn, CRm, op2 == constants> then { <Reg>_SysRegRead_<hash>(...); return() };`
  blocks tried in order. Every condition is kept; the blocks for DCZID_EL0 and TPIDR_EL0 (MRS) and DC ZVA
  (SYS) are kept verbatim, every other block body and the final fallback
  (`AArch64_UnallocatedSysRegAccess`) become `throw(Error_ImplementationDefined("janus-excluded
  ..."))`. An encoding thus reaches the same block as in the full model, and every other system
  register or operation is reported as outside the slice (its ~1,500 accessors would otherwise
  all be in it).

Everything else (the execute/decode functions, the pseudocode library, system registers) is
left as is; Sail's callgraph slice (`:slice`) then drops what the harness cannot reach.
Prints a JSON summary (kept / stubbed / dropped clause counts) on stdout.
"""
import json, os, re, shutil, sys

JANUS_CLASSES = ("DataProcImm", "BranchExcSys", "LoadStore", "DataProcReg", "DataProcFPSIMD")
INSTR_FILES = ("instrs64.sail", "instrs64_sve.sail", "instrs64_sme.sail", "instrs32.sail")


def items(lines):
    """Yield (kind, start, end) for decode clauses (end inclusive) and plain lines."""
    i = 0
    while i < len(lines):
        if lines[i].startswith("function clause __Decode"):
            j = i
            while lines[j] != "}":
                j += 1
            yield ("clause", i, j)
            i = j + 1
        else:
            yield ("line", i, i)
            i += 1


def clause_class(header):
    m = re.match(r"function clause (__Decode[A-Za-z0-9]+_?[A-Za-z0-9]*) ", header)
    return m.group(1)


LIT = re.compile(r"^(function clause __DecodeA64_[A-Za-z0-9]+ \(\(pc, \()0b([01]{32})( as __opcode\)\).*)$")


def unliteral(header):
    m = LIT.match(header)
    if not m:
        return header, False
    bits = ", ".join("bitone" if c == "1" else "bitzero" for c in m.group(2))
    return m.group(1) + "[" + bits + "]" + m.group(3), True


def decode_call(body):
    for l in body:
        m = re.match(r"\s+(decode_[A-Za-z0-9_]+)\(", l)
        if m:
            return m.group(1)
    raise SystemExit("no decode call in clause: " + body[0][:80])


def main():
    src, out, keepf = sys.argv[1:4]
    keep = {l.split("#")[0].strip() for l in open(keepf)} - {""}
    os.makedirs(out, exist_ok=True)
    stats = {"kept": 0, "stubbed": 0, "dropped": 0, "unliteraled": 0, "kept_names": []}
    seen = set()
    for f in sorted(os.listdir(src)):
        p = os.path.join(src, f)
        if not f.endswith(".sail"):
            continue
        if f not in INSTR_FILES and f != "decode_end.sail":
            shutil.copyfile(p, os.path.join(out, f))
            continue
        lines = open(p).read().split("\n")
        res = []
        if f == "decode_end.sail":
            for l in lines:
                m = re.match(r"function clause (__DecodeA64_[A-Za-z0-9]+)\(_, _\) = throw \(Error_Undefined\(\)\)$", l)
                if m and m.group(1)[len("__DecodeA64_"):] not in JANUS_CLASSES:
                    l = 'function clause %s(_, _) = throw(Error_ImplementationDefined("janus-excluded %s"))' % (
                        m.group(1), m.group(1))
                res.append(l)
            open(os.path.join(out, f), "w").write("\n".join(res))
            continue
        if f != "instrs64.sail":
            stats["dropped"] += sum(1 for k, _, _ in items(lines) if k == "clause")
            open(os.path.join(out, f), "w").write("/* emptied by JanusASL/sail/slice.py */\n")
            continue
        for kind, a, b in items(lines):
            if kind == "line":
                res.append(lines[a])
                continue
            item = lines[a:b + 1]
            cls = clause_class(item[0])
            if f == "instrs64.sail" and cls[len("__DecodeA64_"):] in JANUS_CLASSES:
                dec = decode_call(item)
                item = list(item)
                item[0], lit = unliteral(item[0])
                stats["unliteraled"] += lit
                if dec in keep:
                    res.extend(item)
                    stats["kept"] += 1
                    seen.add(dec)
                    stats["kept_names"].append(dec)
                else:
                    k = next(i for i, l in enumerate(item) if l.startswith("    SEE = "))
                    res.extend(item[:k + 1])
                    res.append('    throw(Error_ImplementationDefined("janus-excluded %s"))' % dec)
                    res.append("}")
                    stats["stubbed"] += 1
            else:
                stats["dropped"] += 1
        open(os.path.join(out, f), "w").write("\n".join(res))
    v8 = open(os.path.join(src, "v8_base.sail")).read().split("\n")
    pac = []
    for name in ("PACInvSub", "PACSub", "PACSub1"):
        i = v8.index("function %s Tinput = {" % name)
        j = v8.index("}", i)
        txt = "\n".join(v8[i:j + 1])
        old = "        match Tinput[4 * i + 3 .. 4 * i] {"
        assert txt.count(old) == 1, name
        pac.append(txt.replace(old, "        let nibble : bits(4) = Slice(Tinput, 4 * i, 4);\n        match nibble {"))
    open(os.path.join(out, "janus_pac_splice.sail"), "w").write(
        "/* generated by JanusASL/sail/slice.py from v8_base.sail (see there) */\n" + "\n\n".join(pac) + "\n")
    auto = open(os.path.join(src, "sysregs_autogen.sail")).read().split("\n")
    red = []
    for fn, keepcalls in (("AArch64_AutoGen_SysRegRead", ("DCZID_EL0_SysRegRead_", "TPIDR_EL0_SysRegRead_")),
                          ("AArch64_AutoGen_SysOpsWrite", ("DC_ZVA_SysOpsWrite_",))):
        i = next(k for k, l in enumerate(auto) if l.startswith("function %s (" % fn))
        j = auto.index("}", i)
        body = auto[i + 1:j]
        out_lines, k, nkept = [auto[i]], 0, 0
        while k < len(body):
            if body[k].startswith("    if "):
                e = body.index("    };", k)
                blk = body[k:e + 1]
                t = next(n for n, l in enumerate(blk) if l.endswith(" then {"))
                call = blk[t + 1].strip()
                assert blk[t + 2:] == ["        return()", "    };"], blk
                if any(call.startswith(c) for c in keepcalls):
                    out_lines += blk
                    nkept += 1
                else:  # same condition (blocks are tried in order), body excluded
                    out_lines += blk[:t + 1] + [
                        '        throw(Error_ImplementationDefined("janus-excluded %s"))' % call.split("(")[0],
                        "    };"]
                k = e + 1
            else:
                assert body[k].strip().startswith("AArch64_UnallocatedSysRegAccess(") and k == len(body) - 1, body[k]
                out_lines.append('    throw(Error_ImplementationDefined("janus-excluded %s"))' % fn)
                k += 1
        assert nkept == len(keepcalls), (fn, nkept)
        out_lines.append("}")
        red.append("\n".join(out_lines))
    open(os.path.join(out, "janus_sysreg_splice.sail"), "w").write(
        "/* generated by JanusASL/sail/slice.py from sysregs_autogen.sail (see there) */\n" + "\n\n".join(red) + "\n")
    missing = sorted(keep - seen)
    if missing:
        raise SystemExit("KEEP_FILE names not found as decode clauses: " + ", ".join(missing))
    stats["kept_names"] = sorted(set(stats["kept_names"]))
    json.dump(stats, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
