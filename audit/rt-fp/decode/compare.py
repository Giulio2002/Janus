#!/usr/bin/env python3
"""Compare janus-decode's verdicts with GNU objdump's disassembly of the same words
(docs/AUDIT-FP.md, row DEC-A64). Usage: compare.py LEAN_OUT OBJDUMP_OUT
Fails (exit 1) when the model accepts a word objdump calls undefined, or decodes a floating-point
word as a different instruction or precision than objdump, or a non-FP constructor covers an FP
mnemonic. The Advanced SIMD floating-point classes of `NeonInstr` (vector, scalar, by-element,
across-lanes and pairwise FP, the FP<->fixed-point conversions; decoded only by `decodeNeon`,
which `decodeAll` consults after `decode` rejects a word) are checked the same way: the
mnemonic from an independent table of the A64 encoding tables, plus precision / arrangement and
the fraction bits. Prints counts, and the words objdump accepts as scalar FP that the model
rejects (gaps)."""
import collections, re, sys

DP1 = {0: "fmov", 1: "fabs", 2: "fneg", 3: "fsqrt", 4: "fcvt", 5: "fcvt", 8: "frintn", 9: "frintp",
       10: "frintm", 11: "frintz", 12: "frinta", 14: "frintx", 15: "frinti"}
DP2 = ["fmul", "fdiv", "fadd", "fsub", "fmax", "fmin", "fmaxnm", "fminnm", "fnmul"]
DP3 = ["fmadd", "fmsub", "fnmadd", "fnmsub"]
CVT = {(0, 0): "fcvtns", (0, 1): "fcvtnu", (1, 0): "fcvtps", (1, 1): "fcvtpu", (2, 0): "fcvtms",
       (2, 1): "fcvtmu", (3, 0): "fcvtzs", (3, 1): "fcvtzu", (0, 2): "scvtf", (0, 3): "ucvtf",
       (0, 4): "fcvtas", (0, 5): "fcvtau"}

# Advanced SIMD FP, keyed (U, a = size<1>, opcode) (three same: opcode = w<15:11>; two-register
# miscellaneous: opcode = w<16:12>), from the A64 "Advanced SIMD three same" / "two-register
# miscellaneous" encoding tables. Integer opcodes are absent (None: not FP).
FP3 = {(0, 0, 24): "fmaxnm", (0, 0, 25): "fmla", (0, 0, 26): "fadd", (0, 0, 27): "fmulx",
       (0, 0, 28): "fcmeq", (0, 0, 30): "fmax", (0, 0, 31): "frecps",
       (0, 1, 24): "fminnm", (0, 1, 25): "fmls", (0, 1, 26): "fsub", (0, 1, 30): "fmin",
       (0, 1, 31): "frsqrts",
       (1, 0, 24): "fmaxnmp", (1, 0, 26): "faddp", (1, 0, 27): "fmul", (1, 0, 28): "fcmge",
       (1, 0, 29): "facge", (1, 0, 30): "fmaxp", (1, 0, 31): "fdiv",
       (1, 1, 24): "fminnmp", (1, 1, 26): "fabd", (1, 1, 28): "fcmgt", (1, 1, 29): "facgt",
       (1, 1, 30): "fminp"}
FP2 = {(0, 0, 22): "fcvtn", (0, 0, 23): "fcvtl", (0, 0, 24): "frintn", (0, 0, 25): "frintm",
       (0, 0, 26): "fcvtns", (0, 0, 27): "fcvtms", (0, 0, 28): "fcvtas", (0, 0, 29): "scvtf",
       (0, 1, 12): "fcmgt", (0, 1, 13): "fcmeq", (0, 1, 14): "fcmlt", (0, 1, 15): "fabs",
       (0, 1, 24): "frintp", (0, 1, 25): "frintz", (0, 1, 26): "fcvtps", (0, 1, 27): "fcvtzs",
       (0, 1, 29): "frecpe", (0, 1, 31): "frecpx",
       (1, 0, 22): "fcvtxn", (1, 0, 24): "frinta", (1, 0, 25): "frintx", (1, 0, 26): "fcvtnu",
       (1, 0, 27): "fcvtmu", (1, 0, 28): "fcvtau", (1, 0, 29): "ucvtf",
       (1, 1, 12): "fcmge", (1, 1, 13): "fcmle", (1, 1, 15): "fneg", (1, 1, 25): "frinti",
       (1, 1, 26): "fcvtpu", (1, 1, 27): "fcvtzu", (1, 1, 29): "frsqrte", (1, 1, 31): "fsqrt"}
ACROSS = {(1, 0, 12): "fmaxnmv", (1, 1, 12): "fminnmv", (1, 0, 15): "fmaxv", (1, 1, 15): "fminv"}
SPAIR = {(1, 0, 12): "fmaxnmp", (1, 1, 12): "fminnmp", (1, 0, 13): "faddp", (1, 0, 15): "fmaxp",
         (1, 1, 15): "fminp"}
ELEM = {(0, 1): "fmla", (0, 5): "fmls", (0, 9): "fmul", (1, 9): "fmulx"}   # (U, opcode), size >= 2
SHIFT = {(0, 28): "scvtf", (1, 28): "ucvtf", (0, 31): "fcvtzs", (1, 31): "fcvtzu"}
FIXED = {(0, 2): "scvtf", (0, 3): "ucvtf", (3, 0): "fcvtzs", (3, 1): "fcvtzu"}  # (rmode, opcode)

def neon_check(nctor, a, mn, ops):
    """The expected mnemonic of a NeonInstr FP word (None: not an FP form) and a list of
    operand problems."""
    B = lambda x: 1 if x == "true" else 0 if x == "false" else int(x)
    v = [B(x) for x in a]
    regs = [o.strip() for o in ops.split(",")]
    probs = []
    def arr(sz, Q):            # vector arrangement of an FP lane format
        return ".2d" if sz else (".4s" if Q else ".2s")
    def want_first(suffix=None, letter=None):
        r = regs[0] if regs else ""
        if suffix and not r.endswith(suffix):
            probs.append(f"arrangement {suffix} expected")
        if letter and r[:1] != letter:
            probs.append(f"register {letter} expected")
    exp = None
    if nctor == "threeSame":
        Q, U, size, opc = v[0], v[1], v[2], v[4]
        exp = FP3.get((U, size >> 1, opc))
        if exp: want_first(suffix=arr(size & 1, Q))
    elif nctor == "sThreeSame":
        U, size, opc = v[0], v[1], v[3]
        exp = FP3.get((U, size >> 1, opc))
        if exp: want_first(letter="d" if size & 1 else "s")
    elif nctor == "twoMisc":
        Q, U, size, opc = v[0], v[1], v[2], v[3]
        exp = FP2.get((U, size >> 1, opc))
        if exp == "frecpx": exp = None
        if exp in ("fcvtn", "fcvtl", "fcvtxn"):
            if Q: exp += "2"
            want_first(suffix=(".2d" if exp.startswith("fcvtl") else (".4s" if Q else ".2s")))
        elif exp: want_first(suffix=arr(size & 1, Q))
    elif nctor == "sTwoMisc":
        U, size, opc = v[0], v[1], v[2]
        exp = FP2.get((U, size >> 1, opc))
        # vector-only forms (no scalar encoding): FABS, FNEG, FSQRT, FRINT*, FCVTN/FCVTL
        if exp in ("fabs", "fneg", "fsqrt", "fcvtn", "fcvtl") or (exp or "").startswith("frint"):
            exp = None
        if exp == "fcvtxn": want_first(letter="s")
        elif exp: want_first(letter="d" if size & 1 else "s")
    elif nctor == "across":
        Q, U, size, opc = v[0], v[1], v[2], v[3]
        exp = ACROSS.get((U, size >> 1, opc))
        if exp: want_first(letter="s")
    elif nctor == "sPairwise":
        U, size, opc = v[0], v[1], v[2]
        exp = SPAIR.get((U, size >> 1, opc))
        if exp: want_first(letter="d" if size & 1 else "s")
    elif nctor in ("byElem", "sByElem"):
        if nctor == "byElem": Q, U, size, opc = v[0], v[1], v[2], v[6]
        else: Q, U, size, opc = 0, v[0], v[1], v[5]
        exp = ELEM.get((U, opc)) if size >= 2 else None
        if exp:
            if nctor == "byElem": want_first(suffix=arr(size & 1, Q))
            else: want_first(letter="d" if size & 1 else "s")
            if not ops.endswith("]") or (".d[" if size & 1 else ".s[") not in ops:
                probs.append("element index operand")
    elif nctor in ("shiftImm", "sShiftImm"):
        if nctor == "shiftImm": Q, U, immh, immb, opc = v[0], v[1], v[2], v[3], v[4]
        else: Q, U, immh, immb, opc = 0, v[0], v[1], v[2], v[3]
        exp = SHIFT.get((U, opc))
        if exp:
            sz = 1 if immh >= 8 else 0
            fbits = (128 if sz else 64) - (immh * 8 + immb)
            if nctor == "shiftImm": want_first(suffix=arr(sz, Q))
            else: want_first(letter="d" if sz else "s")
            if regs[-1] != f"#{fbits}": probs.append(f"fbits {fbits} expected")
    elif nctor == "fpCvtFixed":
        sf, ft, rmode, opc, scale = v[0], v[1], v[2], v[3], v[4]
        exp = FIXED.get((rmode, opc))
        if exp:
            fpr, gpr = ("d" if ft else "s"), ("x" if sf else "w")
            dst, src = (fpr, gpr) if rmode == 0 else (gpr, fpr)
            if regs[0][:1] != dst or (len(regs) < 2 or regs[1][:1] not in (src, "x" if src == "x" else src)):
                if not (len(regs) > 1 and regs[1] in ("wzr", "xzr") and regs[1][:1] == src):
                    probs.append(f"registers {dst},{src} expected")
            if regs[-1] != f"#{64 - scale}": probs.append(f"fbits {64 - scale} expected")
    return exp, probs

FPM = re.compile(r"^(f[a-z0-9]*|bf[a-z0-9]*|[su]cvtf)$")

def objd(path):
    out = {}
    for line in open(path):
        p = line.rstrip("\n").split("\t")
        if len(p) < 3:
            continue
        w = int(p[1].strip(), 16)
        mn = p[2].strip()
        ops = p[3].strip() if len(p) > 3 else ""
        out[w] = (mn, ops)
    return out

def prec_ok(ftype, ops, which=0):
    regs = [o.strip() for o in ops.split(",")]
    r = regs[which] if which < len(regs) else ""
    return r[:1] == ("s" if ftype == 0 else "d")

def main():
    od = objd(sys.argv[2])
    bad, n_ok, gaps = [], collections.Counter(), collections.Counter()
    for line in open(sys.argv[1]):
        p = line.split()
        w = int(p[0], 16)
        mn, ops = od[w]
        undef = mn == ".inst"
        if p[1] != "ok":
            if not undef and FPM.match(mn) and (w >> 24) & 0x5E == 0x1E:
                gaps[mn] += 1
            continue
        ctor = p[2].split(".")[-1]
        args = [a for a in p[3:]]
        n_ok[ctor] += 1
        if undef:
            bad.append((w, "model accepts, objdump undefined", line.strip()))
            continue
        def num(i):
            a = args[i]
            return 1 if a == "true" else 0 if a == "false" else int(a)
        exp, prec = None, None
        if ctor == "fpDP3":
            exp, prec = DP3[num(1) * 2 + num(3)], (num(0), 0)
        elif ctor == "fpDP2":
            exp, prec = DP2[num(2)], (num(0), 0)
        elif ctor == "fpDP1":
            exp = DP1.get(num(1))
            # FCVT: destination precision is the opcode's, the source is ftype
            prec = (num(0), 1) if num(1) in (4, 5) else (num(0), 0)
        elif ctor == "fpCmp":
            exp, prec = ("fcmpe" if num(2) >= 2 else "fcmp"), (num(0), 0)
            if num(2) % 2 == 1 and "#0.0" not in ops:
                bad.append((w, "fcmp #0.0 expected", mn + " " + ops))
        elif ctor == "fpCcmp":
            exp, prec = ("fccmpe" if args[3] == "true" else "fccmp"), (num(0), 0)
        elif ctor == "fpCsel":
            exp, prec = "fcsel", (num(0), 0)
        elif ctor == "fpImm":
            exp, prec = "fmov", (num(0), 0)
        elif ctor == "fpCvtInt":
            sf, ft, rm, op = num(0), num(1), num(2), num(3)
            exp = CVT.get((rm, op))
            dst = ops.split(",")[0].strip()
            want = ("x" if sf else "w") if op not in (2, 3) else ("s" if ft == 0 else "d")
            if dst[:1] != want:
                bad.append((w, "conversion register size", mn + " " + ops))
        elif ctor == "fmovGen":
            exp = "fmov"
        elif ctor == "neon":
            nctor = args[0].lstrip("(").split(".")[-1]
            nargs = [x.rstrip(")") for x in args[1:]]
            exp, probs = neon_check(nctor, nargs, mn, ops)
            n_ok["neon." + nctor + (".fp" if exp else "")] += 1
            if exp is None:
                if FPM.match(mn):
                    bad.append((w, f"neon.{nctor} (not an FP form) covers FP mnemonic", mn + " " + ops))
                continue
            if mn != exp:
                bad.append((w, f"neon.{nctor}: model {exp}, objdump {mn}", ops))
            for pr in probs:
                bad.append((w, f"neon.{nctor}: {pr}", mn + " " + ops))
            continue
        else:
            if FPM.match(mn) and not (ctor == "vModImm" and mn == "fmov"):
                bad.append((w, f"{ctor} covers FP mnemonic", mn + " " + ops))
            continue
        if mn != exp:
            bad.append((w, f"{ctor}: model {exp}, objdump {mn}", ops))
        elif prec and not prec_ok(prec[0], ops, 0 if ctor != "fpDP1" or prec[1] == 0 else 1):
            bad.append((w, f"{ctor}: precision ftype={prec[0]}", mn + " " + ops))
    print("accepted by the model:", dict(n_ok))
    print("objdump-accepted scalar FP words the model rejects (gaps):", dict(gaps.most_common(20)))
    for b in bad[:40]:
        print("BAD 0x%08x %s | %s" % b)
    print("disagreements:", len(bad))
    sys.exit(1 if bad else 0)

main()
