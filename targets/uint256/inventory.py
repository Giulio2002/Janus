#!/usr/bin/env python3
"""Generate inventory.json: per-function facts about holiman/uint256 methods in bin/uint256-arm64.

Usage: python3 -I inventory.py [bin/uint256-arm64] > inventory.json

Scouting aid only (not part of the trusted base). Uses aarch64-linux-gnu-objdump/nm.
Memory provenance is a small forward dataflow over the function's CFG: each register
holds a set of origins {arg:<name>, sp, g, global, data}; `mov`/`add #imm`/`sub #imm`
propagate pointer origins, loads and other ALU results yield `data`, `bl` clobbers all
registers except x28 (g) and x29. Every load/store is then attributed to the origins
of its base register.
"""
import json
import re
import subprocess
import sys

BIN = sys.argv[1] if len(sys.argv) > 1 else "bin/uint256-arm64"
PKG = "github.com/holiman/uint256."

# Go ABIInternal integer argument registers per function (x0 = receiver for methods).
SIGS = {
    "(*Int).Add": ["z", "x", "y"], "(*Int).Sub": ["z", "x", "y"], "(*Int).Mul": ["z", "x", "y"],
    "(*Int).AddOverflow": ["z", "x", "y"], "(*Int).SubOverflow": ["z", "x", "y"],
    "(*Int).MulOverflow": ["z", "x", "y"], "(*Int).And": ["z", "x", "y"],
    "(*Int).Or": ["z", "x", "y"], "(*Int).Xor": ["z", "x", "y"], "(*Int).Exp": ["z", "base", "exponent"],
    "(*Int).Div": ["z", "x", "y"], "(*Int).Mod": ["z", "x", "y"], "(*Int).SDiv": ["z", "n", "d"],
    "(*Int).SMod": ["z", "x", "y"], "(*Int).ExtendSign": ["z", "x", "byteNum"],
    "(*Int).AddMod": ["z", "x", "y", "m"], "(*Int).MulMod": ["z", "x", "y", "m"],
    "(*Int).Not": ["z", "x"], "(*Int).Neg": ["z", "x"], "(*Int).Byte": ["z", "n"],
    "(*Int).Sqrt": ["z", "x"], "(*Int).Set": ["z", "x"], "(*Int).Lt": ["z", "x"],
    "(*Int).Gt": ["z", "x"], "(*Int).Slt": ["z", "x"], "(*Int).Sgt": ["z", "x"],
    "(*Int).Eq": ["z", "x"], "(*Int).Cmp": ["z", "x"], "(*Int).IsZero": ["z"],
    "(*Int).IsUint64": ["z"], "(*Int).BitLen": ["z"], "(*Int).Clone": ["z"],
    "(*Int).Clear": ["z"], "(*Int).Bytes32": ["z"], "(*Int).SetUint64": ["z", "#val"],
    "(*Int).SetBytes32": ["z", "in.ptr", "#in.len", "#in.cap"],
    "(*Int).Lsh": ["z", "x", "#n"], "(*Int).Rsh": ["z", "x", "#n"], "(*Int).SRsh": ["z", "x", "#n"],
    "(*Int).squared": ["z"], "(*Int).reduce4": ["z", "x", "m", "mu"],
    "umul": ["x", "y", "res"], "Reciprocal": ["m"],
    "udivrem": ["quot.ptr", "#quot.len", "#quot.cap", "u.ptr", "#u.len", "#u.cap", "d", "rem"],
    "udivremKnuth": ["quot.ptr", "#quot.len", "#quot.cap", "u.ptr", "#u.len", "#u.cap",
                     "d.ptr", "#d.len", "#d.cap"],
    "udivremBy1": ["quot.ptr", "#quot.len", "#quot.cap", "u.ptr", "#u.len", "#u.cap", "#d"],
}

# The integer subset the Janus ISA model is expected to cover (objdump mnemonics/aliases).
SUBSET = set("""
add adds sub subs cmp cmn neg negs adc adcs sbc sbcs ngc ngcs
and ands orr eor bic bics orn eon tst mov mvn movz movn movk
ubfm sbfm bfm ubfx sbfx ubfiz sbfiz bfi bfxil lsl lsr asr ror sxtb sxth sxtw uxtb uxth uxtw extr
csel csinc csinv csneg cset csetm cinc cinv cneg ccmp ccmn
madd msub mul mneg umulh smulh umaddl smaddl umull smull umsubl smsubl
udiv sdiv lslv lsrv asrv rorv clz cls rbit rev rev16 rev32
adr adrp b bl br blr ret cbz cbnz tbz tbnz
ldr ldrb ldrh ldrsb ldrsh ldrsw ldur ldurb ldurh ldursb ldursh ldursw
str strb strh stur sturb sturh ldp stp ldpsw
nop dmb udf
""".split())
COND = re.compile(r"^b\.[a-z]{2}$")
SIMD = re.compile(r"\b([vqdsh]\d{1,2}|fp[a-z]*)\b")
LOAD = re.compile(r"^(ldr|ldur|ldp)")
STORE = re.compile(r"^(str|stur|stp)")


def run(*a):
    return subprocess.run(a, check=True, capture_output=True, text=True).stdout


def symbols():
    out = {}
    for line in run("aarch64-linux-gnu-nm", "-S", BIN).splitlines():
        p = line.split(None, 3)
        if len(p) == 4 and p[2] in "Tt":
            out[p[3]] = (int(p[0], 16), int(p[1], 16))
    return out


def disasm(start, size):
    txt = run("aarch64-linux-gnu-objdump", "-d", "--no-show-raw-insn",
              f"--start-address={start:#x}", f"--stop-address={start + size:#x}", BIN)
    ins = []
    for line in txt.splitlines():
        m = re.match(r"^\s+([0-9a-f]+):\s+(\S+)\s*(.*)$", line)
        if m:
            ops = m.group(3).split("//")[0].strip()
            ins.append((int(m.group(1), 16), m.group(2), ops))
    return ins


def target(ops):
    m = re.match(r"^(?:[xw]\d+,\s*)?(?:#\d+,\s*)?([0-9a-f]+)\s*<([^>]+)>", ops)
    return (int(m.group(1), 16), m.group(2)) if m else (None, None)


def regs_of(ops):
    return re.findall(r"\b(x\d+|w\d+|sp|xzr|wzr)\b", ops)


def rnum(r):
    if r in ("sp",):
        return "sp"
    if r in ("xzr", "wzr"):
        return None
    return int(r[1:])


def analyze(name, start, size, symtab):
    short = name[len(PKG):] if name.startswith(PKG) else name
    ins = disasm(start, size)
    # Drop trailing alignment padding (udf #0) after the last real instruction.
    while ins and ins[-1][1] == "udf":
        ins.pop()
    idx = {a: i for i, (a, _, _) in enumerate(ins)}
    end = start + size
    mnems = sorted({("b.cond" if COND.match(m) else m) for _, m, _ in ins})
    outside = sorted({m for _, m, o in ins if not (m in SUBSET or COND.match(m))} |
                     {f"{m} {o}" for _, m, o in ins if SIMD.search(o)})
    callees, loops = {}, []
    for a, m, o in ins:
        if m == "bl":
            t, tn = target(o)
            tn = tn.split("+")[0] if tn else hex(t)
            kind = ("morestack" if tn.startswith("runtime.morestack") else
                    "panic" if re.match(r"runtime\.(panic|goPanic|gopanic)", tn) else
                    "uint256" if tn.startswith(PKG) else "runtime" if tn.startswith("runtime.") else "other")
            callees.setdefault(tn, {"kind": kind, "sites": []})["sites"].append(hex(a))
        if m in ("b", "cbz", "cbnz", "tbz", "tbnz") or COND.match(m):
            t, _ = target(o)
            if t is not None and t < a and start <= t < end:
                # Back edge to the entry from the morestack tail is the stack-growth retry, not a loop.
                if not (t == start and any(mm == "bl" and "morestack" in oo for _, mm, oo in ins[max(0, idx[a] - 4):idx[a]])):
                    loops.append({"from": hex(a), "to": hex(t)})
    prologue = len(ins) >= 3 and ins[0][1] == "ldr" and ins[0][2] == "x16, [x28, #16]"
    frame = 0
    for a, m, o in ins[:8]:
        mm = re.match(r"^(?:x30|x29, x30), \[sp, #-(\d+)\]!$", o)
        if m in ("str", "stp") and mm:
            frame = int(mm.group(1))
        mm = re.match(r"^(?:sp, sp|x20, sp), #(0x[0-9a-f]+|\d+)$", o)
        if m == "sub" and mm:
            frame = int(mm.group(1), 0)

    # ---- provenance dataflow ----
    args = SIGS.get(short, [])
    ptr_args = [n for n in args if not n.startswith("#")]
    init_regs = {i: frozenset([(n, 0)]) for i, n in enumerate(args) if not n.startswith("#")}
    for i, n in enumerate(args):
        if n.startswith("#"):
            init_regs[i] = frozenset([("data", None)])
    init_regs[28] = frozenset([("g", 0)])
    init_regs[30] = frozenset([("retaddr", None)])
    init_regs[31] = frozenset([("sp", 0)])  # 31 = SP in this table
    states = {0: (init_regs, {})}
    work = [0]
    accesses = {}
    call_args = {}
    DATA = frozenset([("data", None)])

    def rd(regs, r):
        if r in ("xzr", "wzr"):
            return frozenset([("zero", None)])
        n = 31 if r in ("sp", "wsp") else int(r[1:])
        return regs.get(n, DATA)

    def wr(regs, r, v):
        if r in ("xzr", "wzr"):
            return
        n = 31 if r in ("sp", "wsp") else int(r[1:])
        regs[n] = v

    def shift(v, d):
        return frozenset((o, None if (k is None or o in ("data", "zero", "retaddr")) else k + d) for o, k in v)

    def widen(v):
        by = {}
        for o, k in v:
            by.setdefault(o, set()).add(k)
        out = set()
        for o, ks in by.items():
            out |= {(o, None)} if len(ks) > 4 else {(o, k) for k in ks}
        return frozenset(out)

    def size_of(m, r0):
        unit = 8 if r0.startswith("x") else 4 if r0.startswith("w") else 16 if r0.startswith("q") else 8
        if m in ("ldrb", "strb", "ldurb", "sturb", "ldrsb", "ldursb"):
            unit = 1
        elif m in ("ldrh", "strh", "ldurh", "sturh", "ldrsh", "ldursh"):
            unit = 2
        elif m in ("ldrsw", "ldursw"):
            unit = 4
        return unit * (2 if m in ("ldp", "stp", "ldpsw") else 1)

    while work:
        i = work.pop()
        regs, slots = dict(states[i][0]), dict(states[i][1])
        a, m, o = ins[i]
        rs = regs_of(o)
        succ = [i + 1] if i + 1 < len(ins) else []
        mem = re.search(r"\[(\w+)(?:,\s*#(-?(?:0x[0-9a-f]+|\d+)))?(?:,\s*([xw]\d+)[^\]]*)?\](!)?(?:,\s*#(-?(?:0x[0-9a-f]+|\d+)))?", o)
        if mem and (LOAD.match(m) or STORE.match(m)):
            basev = rd(regs, mem.group(1))
            imm = int(mem.group(2), 0) if mem.group(2) else 0
            post = int(mem.group(5), 0) if mem.group(5) else None
            addr = basev if post is not None else shift(basev, imm)
            if mem.group(3):
                addr = frozenset((ob, None) for ob, _ in addr)
            datar = re.findall(r"\b([xwq]\d+|xzr|wzr)\b", o.split("[")[0])
            sz = size_of(m, datar[0] if datar else "x")
            acc = accesses.setdefault(a, set())
            for ob, k in addr:
                acc.add(("W" if STORE.match(m) else "R", ob, k, sz))
            known_sp = [k for ob, k in addr if ob == "sp" and k is not None]
            single = len(addr) == 1 and len(known_sp) == 1
            step = sz // len(datar) if datar else 8
            if LOAD.match(m):
                for j, r in enumerate(datar):
                    v = DATA
                    if single and step == 8 and (known_sp[0] + 8 * j) in slots:
                        v = slots[known_sp[0] + 8 * j]
                    if r.startswith("x"):
                        wr(regs, r, v)
            else:
                for j, r in enumerate(datar):
                    if single:
                        slots[known_sp[0] + step * j] = rd(regs, r) if r[0] in "xz" else DATA
                    else:
                        for k in known_sp:  # weak update
                            slots[k + step * j] = slots.get(k + step * j, DATA) | (rd(regs, r) if r[0] in "xz" else DATA)
            if mem.group(4) or post is not None:
                wr(regs, mem.group(1), shift(basev, imm if mem.group(4) else post))
        elif m == "bl":
            t, tn = target(o)
            call_args.setdefault(tn.split("+")[0] if tn else hex(t), {})[hex(a)] = {
                f"x{j}": sorted(f"{ob}@{k}" for ob, k in rd(regs, f"x{j}") if ob not in ("data", "zero"))
                for j in range(8)}
            regs = {k: v for k, v in regs.items() if k in (28, 29, 31)}
            if tn and re.match(r"runtime\.(panic|gopanic|goPanic)", tn):
                succ = []  # panic stubs never return
            if tn and tn.startswith("runtime.newobject"):
                regs[0] = frozenset([("heap", 0)])
        elif m in ("ret", "br"):
            succ = []
        elif m == "b":
            succ = [idx.get(target(o)[0])]
        elif m in ("cbz", "cbnz", "tbz", "tbnz") or COND.match(m):
            succ = succ + [idx.get(target(o)[0])]
        elif m in ("cmp", "cmn", "tst", "ccmp", "ccmn", "nop", "dmb", "udf", "blr"):
            if m == "blr":
                regs = {k: v for k, v in regs.items() if k in (28, 29, 31)}
        elif m == "mov" and len(rs) == 2:
            wr(regs, rs[0], rd(regs, rs[1]))
        elif m in ("add", "sub") and len(rs) == 2 and re.search(r",\s*#(0x[0-9a-f]+|\d+)$", o):
            imm = int(re.search(r"#(0x[0-9a-f]+|\d+)$", o).group(1), 0)
            wr(regs, rs[0], shift(rd(regs, rs[1]), imm if m == "add" else -imm))
        elif m == "add" and len(rs) >= 3:
            p = {(ob, None) for ob, _ in rd(regs, rs[1]) | rd(regs, rs[2]) if ob not in ("data", "zero")}
            wr(regs, rs[0], frozenset(p) if p else DATA)
        elif m in ("adrp", "adr"):
            wr(regs, rs[0], frozenset([("global", None)]))
        elif rs and rs[0][0] == "x":
            wr(regs, rs[0], DATA)
        for sidx in succ:
            if sidx is None:
                continue
            old = states.get(sidx)
            if old is None:
                new = (regs, slots)
            else:
                nr = {k: widen(old[0].get(k, DATA) | regs.get(k, DATA)) for k in set(old[0]) | set(regs)}
                ns = {k: widen(old[1].get(k, DATA) | slots.get(k, DATA)) for k in set(old[1]) | set(slots)}
                new = (nr, ns)
            if old is None or old != new:
                states[sidx] = new
                work.append(sidx)

    # ---- aliasing: on every acyclic path, is some input limb read after the same
    # offset of an output argument was already written? (Only for loop-free functions;
    # reads/writes inside callees are not followed.)
    def succs(i):
        a, m, o = ins[i]
        nx = [i + 1] if i + 1 < len(ins) else []
        if m in ("ret", "br"):
            return []
        if m == "bl":
            tn = target(o)[1] or ""
            return [] if re.match(r"runtime\.(panic|gopanic|goPanic|morestack)", tn) else nx
        if m == "b":
            return [idx[target(o)[0]]] if target(o)[0] in idx else []
        if m in ("cbz", "cbnz", "tbz", "tbnz") or COND.match(m):
            t = target(o)[0]
            return nx + ([idx[t]] if t in idx else [])
        return nx

    hazards = set()
    if not loops:
        stack = [(0, frozenset())]
        seen = set()
        while stack:
            i, written = stack.pop()
            if (i, written) in seen:
                continue
            seen.add((i, written))
            acc = accesses.get(ins[i][0], set())
            w = set(written)
            for rw, ob, k, sz in acc:
                if rw == "R" and ob in ptr_args:
                    for (wo, wk, wsz) in written:
                        if wo != ob and wo in ptr_args and (wk is None or k is None or (wk < k + sz and k < wk + wsz)):
                            hazards.add(f"{wo}=={ob}: read {ob}@{k} at {ins[i][0]:#x} after write {wo}@{wk}")
            for rw, ob, k, sz in acc:
                if rw == "W" and ob in ptr_args:
                    w.add((ob, k, sz))
            for sn in succs(i):
                stack.append((sn, frozenset(w)))

    # ---- summarise memory footprint per origin ----
    foot = {}
    for a, acc in accesses.items():
        for rw, ob, k, sz in acc:
            f = foot.setdefault(ob, {"read": False, "write": False, "min": None, "max": None, "unknown_offset_at": []})
            f["read" if rw == "R" else "write"] = True
            if k is None:
                f["unknown_offset_at"].append(hex(a))
            else:
                f["min"] = k if f["min"] is None else min(f["min"], k)
                f["max"] = k + sz if f["max"] is None else max(f["max"], k + sz)
    for f in foot.values():
        f["unknown_offset_at"] = sorted(set(f["unknown_offset_at"]))
        if f["min"] is not None:
            f["range"] = f"[{f['min']}, {f['max']})"
    g_reads = sorted(hex(a) for a, acc in accesses.items() if any(ob == "g" for _, ob, _, _ in acc))
    allowed = set(ptr_args) | {"sp"}
    stray = sorted(set(foot) - allowed - {"g"})
    int_args = [n for n in ptr_args if not n.endswith(".ptr") and n not in ("res", "mu")]
    in_bounds = all(foot[n]["min"] is not None and 0 <= foot[n]["min"] and foot[n]["max"] <= 32
                    and not foot[n]["unknown_offset_at"] for n in int_args if n in foot)
    return {
        "symbol": name, "addr": hex(start), "size": size, "instructions": len(ins),
        "reachable_instructions": len(states),
        "mnemonics": mnems, "outside_integer_subset": outside,
        "callees": callees, "call_arg_pointers": call_args,
        "stack_frame_bytes": frame, "stack_growth_prologue": prologue,
        "args": args,
        "memory_footprint": foot,
        "g_reads": g_reads,
        "memory_outside_args_and_stack": stray,
        "memory_only_via_pointer_args_and_stack": not stray,
        "int_arg_accesses_within_32_bytes": in_bounds,
        "loops": loops,
        "alias_hazards": sorted(hazards) if not loops else "not analysed (has loops)",
    }


def main():
    syms = symbols()
    out = {"binary": BIN, "sha256": run("sha256sum", BIN).split()[0],
           "go": run("/usr/local/go/bin/go", "version", BIN).split(": ", 1)[1].strip(),
           "functions": {}}
    pkg = sorted((n for n in syms if n.startswith(PKG)), key=lambda n: syms[n][0])
    for name in pkg:
        out["functions"][name[len(PKG):]] = analyze(name, *syms[name], syms)
    # Non-stub callees outside the package (math/bits, runtime helpers) that a proof
    # would also have to extract: analyse them too, under their full names.
    todo = [c for f in out["functions"].values() for c, v in f["callees"].items()
            if v["kind"] in ("other", "runtime")]
    while todo:
        c = todo.pop()
        if c in out["functions"] or c not in syms:
            continue
        f = analyze(c, *syms[c], syms)
        out["functions"][c] = f
        todo += [cc for cc, v in f["callees"].items() if v["kind"] in ("other",)]
    # Transitive closure of non-stub callees for every package function.
    def closure(n, seen):
        f = out["functions"].get(n[len(PKG):] if n.startswith(PKG) else n)
        if f is None:
            return
        for c, v in f["callees"].items():
            if v["kind"] in ("panic", "morestack") or c in seen:
                continue
            seen.add(c)
            closure(c, seen)
    for name in pkg:
        seen = set()
        closure(name, seen)
        f = out["functions"][name[len(PKG):]]
        f["transitive_callees"] = sorted(seen)
        f["transitive_stubs"] = sorted({c for n in [name] + sorted(seen)
                                        for c, v in out["functions"].get(n[len(PKG):] if n.startswith(PKG) else n, {"callees": {}})["callees"].items()
                                        if v["kind"] in ("panic", "morestack")})
    json.dump(out, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
