#!/usr/bin/env python3
"""Compare janus-decode's verdicts with GNU objdump's disassembly of the same words
(docs/AUDIT-FP.md, row DEC-A64). Usage: compare.py LEAN_OUT OBJDUMP_OUT
Fails (exit 1) when the model accepts a word objdump calls undefined, or decodes a floating-point
word as a different instruction or precision than objdump, or a non-FP constructor covers an FP
mnemonic. Prints counts, and the words objdump accepts as scalar FP that the model rejects (gaps)."""
import collections, re, sys

DP1 = {0: "fmov", 1: "fabs", 2: "fneg", 3: "fsqrt", 4: "fcvt", 5: "fcvt", 8: "frintn", 9: "frintp",
       10: "frintm", 11: "frintz", 12: "frinta", 14: "frintx", 15: "frinti"}
DP2 = ["fmul", "fdiv", "fadd", "fsub", "fmax", "fmin", "fmaxnm", "fminnm", "fnmul"]
DP3 = ["fmadd", "fmsub", "fnmadd", "fnmsub"]
CVT = {(0, 0): "fcvtns", (0, 1): "fcvtnu", (1, 0): "fcvtps", (1, 1): "fcvtpu", (2, 0): "fcvtms",
       (2, 1): "fcvtmu", (3, 0): "fcvtzs", (3, 1): "fcvtzu", (0, 2): "scvtf", (0, 3): "ucvtf",
       (0, 4): "fcvtas", (0, 5): "fcvtau"}
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
