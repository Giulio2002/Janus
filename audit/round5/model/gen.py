#!/usr/bin/env python3
"""Round-5 targeted oracle cases (docs/AUDIT-ROUND5.md, item 6: model level).

Six instruction families picked for few oracle cases relative to their encoding space.
The words and states below are derived from the Arm ARM (DDI 0487) / Intel SDM pseudocode;
the derivations are in the comments of each family. The oracle compares the Lean model with
the hardware (qemu-aarch64 for arm64, the host CPU for amd64), so the expected values are
the hardware's; the comments say which edge each group targets.

Usage: gen.py OUTDIR DCZID      (writes a64.jsonl and x64.jsonl)
"""
import json, os, random, sys

out, dczid = sys.argv[1], int(sys.argv[2])
rng = random.Random(5)

# ---------------------------------------------------------------- arm64 layout (oracle/layout)
TEST_PC = 0x10_0000_0800
DATA = 0x10_0004_0000
EDGE64 = [0, 1, 2, 0x7f, 0x80, 0xff, 0x7fff, 0x8000, 0xffff, 0x7fffffff, 0x80000000,
          0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000,
          0xffffffffffffffff, 0xfffffffffffffffe, 0xffffffff80000000, 0x8000000000000001]

def r64():
    c = rng.random()
    if c < 0.5: return rng.choice(EDGE64)
    if c < 0.75: return rng.getrandbits(64)
    if c < 0.9: return rng.getrandbits(32)
    return (-rng.randint(1, 300)) & (2**64 - 1)

VBYTES = [0x00, 0x01, 0x7f, 0x80, 0xff, 0xfe, 0x81]
def v128():
    c = rng.random()
    if c < 0.3: return rng.getrandbits(128)
    if c < 0.6: return int.from_bytes(bytes(rng.choice(VBYTES) for _ in range(16)), "little")
    if c < 0.8:  # lanes at signed/unsigned extremes of one element size
        e = rng.choice([1, 2, 4, 8])
        lanes = [rng.choice([0, 1, (1 << (8*e-1)) - 1, 1 << (8*e-1), (1 << 8*e) - 1, (1 << (8*e-1)) + 1])
                 for _ in range(16 // e)]
        return sum(l << (8*e*i) for i, l in enumerate(lanes))
    return rng.choice([0, (1 << 128) - 1, 0x80808080808080808080808080808080,
                       0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f])

a64 = []
def a64case(cls, word, x=None, sp=None, nzcv=None, v=None):
    x = x or [r64() for _ in range(31)]
    a64.append({"id": 5_000_000 + len(a64), "class": cls, "word": "0x%08x" % word,
                "pc": hex(TEST_PC), "x": [hex(t) for t in x],
                "sp": hex(DATA + 0xa00 if sp is None else sp),
                "nzcv": rng.randrange(16) if nzcv is None else nzcv,
                "seed": rng.randrange(1 << 20), "dczid": dczid,
                "v": [hex(t) for t in (v or [v128() for _ in range(32)])]})

# A1. ADD/SUB (extended register): sf op S 01011 opt(2) 1 Rm option(3) imm3 Rn Rd.
# ASL (AddSubExtendedRegister): if imm3 > 4 -> UNDEFINED; opt != 00 -> unallocated;
#   operand1 = if n == 31 then SP[] else X[n]   (Rn = 31 is SP, always)
#   operand2 = ExtendReg(m, extend_type, shift, datasize) (Rm = 31 is ZR)
#     = LSL(Extend(X[m]<len-1:0>, N, unsigned), shift), len = Min(len, N - shift)
#     so for N = 32, UXTX/SXTX read W[m] (len capped at 32); SXTW in 64-bit sign-extends bit 31
#   if d == 31 && !setflags then SP[] = result else X[d] = result  (Rd = 31: SP for ADD/SUB,
#     ZR for ADDS/SUBS, i.e. CMP/CMN)
#   SUB: operand2 = NOT(operand2), carry_in = 1 (AddWithCarry), so SUB x, 0 sets C = 1.
#   32-bit results write W[d] zero-extended, and to SP as well (SP<63:32> = 0).
for sf in (0, 1):
    for op in (0, 1):
        for S in (0, 1):
            for option in range(8):
                for imm3 in range(8):
                    for rn in (31, 3):
                        for rd in (31, 5):
                            for rm in (31, 7):
                                w = (sf << 31) | (op << 30) | (S << 29) | (0b01011 << 24) | (1 << 21) \
                                    | (rm << 16) | (option << 13) | (imm3 << 10) | (rn << 5) | rd
                                for k in range(2 if imm3 <= 4 else 1):
                                    sp = rng.choice([DATA + 0xa00, 0, 0xfffffffffffffff0,
                                                     0x80000000, 0xfffffff0, 0x7ffffffffffffff0])
                                    a64case("r5/a64.addsubext", w, sp=sp)
# opt != 00 (bits 23:22) is unallocated: must fault (or be a gap), never succeed in the model
for opt in (1, 2, 3):
    for _ in range(40):
        w = (rng.getrandbits(3) << 29) | (0b01011 << 24) | (opt << 22) | (1 << 21) \
            | (rng.getrandbits(5) << 16) | (rng.getrandbits(3) << 13) | (rng.randrange(5) << 10) \
            | (rng.getrandbits(5) << 5) | rng.getrandbits(5)
        a64case("r5/a64.addsubext.opt", w)

# A2. Advanced SIMD shift by immediate: 0 Q U 011110 immh immb opcode(5) 1 Rn Rd, immh != 0.
# ASL: esize = 8 << HighestSetBit(immh); immh<3> = 1 && Q = 0 -> reserved (all vector forms);
#   right shifts (SSHR/USHR/SSRA/USRA/SRSHR.., SRI, SHRN): shift = (2*esize) - UInt(immh:immb),
#     so shift ranges 1..esize: SSHR #esize gives all sign bits, USHR #esize gives 0,
#     USRA #esize adds 0, SRI #esize leaves Vd unchanged (mask = 0);
#   left shifts (SHL, SLI, SSHLL/USHLL): shift = UInt(immh:immb) - esize, 0..esize-1:
#     SLI #0 replaces Vd; SHL #0 copies; SSHLL #0 = SXTL;
#   SHRN/SSHLL: immh<3> = 1 reserved (no 128-bit elements); SHRN2/SSHLL2 use the upper half.
#   SSRA/USRA/SRI/SLI read Vd; 64-bit (Q = 0) forms zero Vd<127:64>.
# Every opcode (32) x U x Q x immh (1..15) x immb (8) is enumerated, so the unmodelled
# opcodes (rounding/saturating shifts, conversions) also run and must not succeed wrongly.
for Q in (0, 1):
    for U in (0, 1):
        for immh in range(1, 16):
            for immb in range(8):
                for opcode in range(32):
                  for _ in range(4):
                    rn, rd = rng.choice([(1, 2), (3, 3), (31, 0), (4, 31)])
                    w = (Q << 30) | (U << 29) | (0b011110 << 23) | (immh << 19) | (immb << 16) \
                        | (opcode << 11) | (1 << 10) | (rn << 5) | rd
                    a64case("r5/a64.simd.shift", w)
# the scalar forms (01 U 111110 immh immb opcode 1 Rn Rd), immh<3> = 0 is reserved for most
for U in (0, 1):
    for immh in range(1, 16):
        for opcode in range(32):
            w = (1 << 30) | (U << 29) | (0b111110 << 23) | (immh << 19) | (rng.getrandbits(3) << 16) \
                | (opcode << 11) | (1 << 10) | (1 << 5) | 2
            a64case("r5/a64.simd.shift.scalar", w)

# A3. Advanced SIMD across lanes: 0 Q U 01110 size 11000 opcode(5) 10 Rn Rd.
# ASL: size = 11 reserved; size = 10 && Q = 0 reserved (no 2S across); ADDV is U = 0 only;
#   SADDLV/UADDLV: result is 2*esize wide (sum of all lanes, no wrap at esize);
#   SMAXV/SMINV signed, UMAXV/UMINV unsigned; result written to the low element, rest of V[d]
#   zeroed (V[d] = result, a scalar write). Lanes equal to the extremes check signedness.
for Q in (0, 1):
    for U in (0, 1):
        for size in range(4):
            for opcode in range(32):
                for _ in range(40):
                    rn, rd = rng.choice([(1, 2), (3, 3), (31, 0)])
                    w = (Q << 30) | (U << 29) | (0b01110 << 24) | (size << 22) | (0b11000 << 17) \
                        | (opcode << 12) | (0b10 << 10) | (rn << 5) | rd
                    a64case("r5/a64.simd.across", w)

# ---------------------------------------------------------------- amd64 layout (oracle-amd64/layout)
XDATA = 0x10_0004_0000
CF, PF, AF, ZF, SF, OF = 1, 4, 16, 64, 128, 2048
x64 = []
def x64case(cls, bs, regs, flags=None):
    x64.append({"id": 6_000_000 + len(x64), "class": cls, "bytes": bs.hex(),
                "regs": [hex(r) for r in regs],
                "rflags": rng.choice([0, CF | ZF, CF | PF | AF | ZF | SF | OF, OF | SF]) if flags is None else flags,
                "xmm": ["0x0"] * 16, "seed": rng.randrange(1 << 20)})

def regs_with(**kw):
    names = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"]
    r = [r64() for _ in range(16)]
    r[4] = XDATA + 0x800  # RSP inside the buffer, 8-aligned
    for k, v in kw.items():
        r[names.index(k)] = v & (2**64 - 1)
    return r

def pfx(w):  # operand-size prefix bytes
    return {16: b"\x66", 32: b"", 64: b"\x48"}[w]

# X1. BT/BTS/BTR/BTC.
# SDM Vol. 2A "BT": register bit base: bit offset = offset operand MOD operand size (16/32/64)
#   for both a register and an imm8 offset. Memory bit base with an imm8 offset: the imm8 is
#   taken modulo the operand size as well (the byte accessed is within the operand).
#   Memory bit base with a REGISTER offset: the offset is a signed integer (-2^(w-1)..2^(w-1)-1)
#   and selects a bit anywhere in memory: the access is at EA + (w/8) * (offset SAR log2 w)
#   ("bit-string" addressing). The model does not implement this form (decoder: register
#   destination only); every such case must be a model gap, never a success.
#   CF = selected bit; OF SF AF PF undefined; ZF unaffected (Intel) / undefined (AMD).
#   BTS/BTR/BTC write back; LOCK allowed only with a memory destination (else #UD).
offsets = [0, 1, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 255, 2**31 - 1, 2**31, 2**32 + 3,
           2**63 - 1, 2**63, -1, -2, -8, -9, -16, -17, -32, -33, -64, -65, -0x4000, -0x4001, 0x3fff]
for w in (16, 32, 64):
    for opc, ext in ((0xA3, 4), (0xAB, 5), (0xB3, 6), (0xBB, 7)):
        # BT r/m, r with register base (ModRM 11 reg=ECX(1) rm=EDX(2)): offset mod w
        for off in offsets * 3:
            x64case("r5/x64.bt.reg", pfx(w) + bytes([0x0F, opc, 0xCA]), regs_with(rcx=off))
        # BT [rbx], ecx (ModRM 00 001 011): bit-string addressing, model gap expected
        for off in offsets:
            for base in (XDATA + 0x800, XDATA, XDATA + 0xff8):
                x64case("r5/x64.bt.mem-regoff", pfx(w) + bytes([0x0F, opc, 0x0B]), regs_with(rcx=off, rbx=base))
        # BT r/m, imm8 (0F BA /ext ib): register and memory base, imm8 >= w masked
        for imm in (0, 1, 15, 16, 31, 32, 63, 64, 65, 127, 128, 200, 255):
            for _ in range(3):
                x64case("r5/x64.bt.reg-imm", pfx(w) + bytes([0x0F, 0xBA, 0xC0 | (ext << 3) | 2, imm]), regs_with())
            for base in (XDATA + 0x800, XDATA + 0x1000 - w // 8, XDATA + 0x1000 - w // 8 + 1, XDATA - 1):
                x64case("r5/x64.bt.mem-imm", pfx(w) + bytes([0x0F, 0xBA, (ext << 3) | 3, imm]), regs_with(rbx=base))
                if ext != 4:  # LOCK BTS/BTR/BTC m, imm8 is lockable; LOCK BT is #UD
                    x64case("r5/x64.bt.lock-mem-imm", b"\xf0" + pfx(w) + bytes([0x0F, 0xBA, (ext << 3) | 3, imm]),
                            regs_with(rbx=base))
            x64case("r5/x64.bt.lock-reg-imm", b"\xf0" + pfx(w) + bytes([0x0F, 0xBA, 0xC0 | (ext << 3) | 2, imm]), regs_with())
        x64case("r5/x64.bt.lock-reg", b"\xf0" + pfx(w) + bytes([0x0F, opc, 0xCA]), regs_with(rcx=3))

# X2. SHLD/SHRD r/m, r, imm8 | CL (0F A4/A5 left, 0F AC/AD right).
# SDM "SHLD": COUNT = count MOD 32 (MOD 64 with REX.W); 16-bit operand uses MOD 32 too.
#   COUNT = 0: no operation on flags or destination value (but a 32-bit register destination
#   is still written, so bits 63:32 are cleared: the earlier round's oracle-found bug).
#   COUNT > operand size (only possible at 16 bits: 17..31): result and flags undefined.
#   COUNT = 16 at 16 bits: dest = src, CF = last bit shifted out = DEST[0] (left) / DEST[15] (right).
#   CF = last bit shifted out; SF ZF PF from the result; AF undefined; OF defined only for
#   COUNT = 1 (sign change), undefined otherwise.
counts = [0, 1, 2, 7, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 255]
for w in (16, 32, 64):
    for left in (True, False):
        ib, cl = (0xA4, 0xA5) if left else (0xAC, 0xAD)
        for c in counts:
            for dst in (0x8000000000000001, 0xffffffffffffffff, 0x123456789abcdef0, 0, 0x8000):
                for src in (0, 0xffffffffffffffff, 0x8000000000000001, 0xfedcba9876543210):
                    # SHLD edx, eax, imm8: ModRM 11 000(eax) 010(edx) = 0xC2
                    x64case("r5/x64.shld.imm", pfx(w) + bytes([0x0F, ib, 0xC2, c]), regs_with(rdx=dst, rax=src))
                    x64case("r5/x64.shld.cl", pfx(w) + bytes([0x0F, cl, 0xC2]), regs_with(rdx=dst, rax=src, rcx=c | (rng.getrandbits(56) << 8)))
            # memory destination [rbx]
            x64case("r5/x64.shld.mem", pfx(w) + bytes([0x0F, ib, 0x03, c]), regs_with(rbx=XDATA + 0x400, rax=r64()))
            x64case("r5/x64.shld.mem-edge", pfx(w) + bytes([0x0F, cl, 0x03]),
                    regs_with(rbx=XDATA + 0x1000 - w // 8 + rng.choice([0, 1]), rcx=c))

# X3. BSF/BSR/TZCNT/LZCNT/POPCNT r, r/m (0F BC / 0F BD; F3 0F BC/BD/B8).
# SDM: BSF/BSR: source 0 -> ZF = 1, destination undefined (AMD: unchanged); else ZF = 0 and
#   dest = index of lowest/highest set bit; CF OF SF AF PF undefined.
#   TZCNT/LZCNT: CF = (source = 0), ZF = (result = 0); result = operand size for a zero source;
#   OF SF AF PF undefined. POPCNT: ZF = (source = 0), OF SF AF CF PF cleared.
#   32-bit destinations are zero-extended; 16-bit ones merge into the register.
srcs = [0, 1, 2, 0x8000, 0xffff, 0x10000, 0x80000000, 0xffffffff, 0x100000000,
        0x8000000000000000, 0xffffffffffffffff, 0x0001000000010000, 0xffff0000, 0xffff00000000]
for w in (16, 32, 64):
    for name, bs in (("bsf", b"\x0f\xbc"), ("bsr", b"\x0f\xbd"), ("tzcnt", b"\xf3\x0f\xbc"),
                     ("lzcnt", b"\xf3\x0f\xbd"), ("popcnt", b"\xf3\x0f\xb8")):
        pre = bs[:-2] if len(bs) == 3 else b""
        op = bs[-2:]
        enc = pre + pfx(w) + op  # mandatory F3 before REX
        for s in srcs:
            for _ in range(3):
                # dst EDX(2), src EAX(0): ModRM 11 010 000 = 0xD0
                x64case("r5/x64.cnt." + name, enc + b"\xd0", regs_with(rax=s, rdx=r64()))
            # memory source [rbx]
            x64case("r5/x64.cnt.mem", enc + b"\x13", regs_with(rbx=XDATA + rng.randrange(0, 4096 - 8)))
        # 66 and F3 together (operand-size override with the mandatory prefix), REX.B source
        x64case("r5/x64.cnt.prefix", b"\x66" + bs[:-2] + op + b"\xd0" if len(bs) == 3 else b"\x66" + bs + b"\xd0",
                regs_with(rax=0x8000))

# ---------------------------------------------------------------- the HandDerived.lean states
# The exact words and states of HandDerived.lean (whose expected values are derived by hand and
# checked against the model by the kernel), run on hardware too, so the hand values are also
# confirmed by the reference (model == hardware here, model == hand there).
def a64hand(word, xs, sp, vs):
    a64case("r5/a64.hand", word, x=[xs.get(i, 0) for i in range(31)], sp=sp, nzcv=0,
            v=[vs.get(i, 0) for i in range(32)])
a64hand(0x8b27d07f, {3: 0x1000, 7: 0x80000000}, 0x40, {})
a64hand(0x6b2763ff, {7: 0x100000010}, 0x100000010, {})
a64hand(0x8b271465, {}, 0, {})
a64hand(0x4f400420, {}, 0, {1: 0x7fffffffffffffff8000000000000000})
a64hand(0x6f400420, {}, 0, {0: 5, 1: 2**128 - 1})
a64hand(0x2f084422, {}, 0, {1: 0x1234, 2: 2**128 - 1})
a64hand(0x6f085422, {}, 0, {1: 0x0123456789abcdeffedcba9876543210, 2: 7})
a64hand(0x0f400420, {}, 0, {})
a64hand(0x6e303820, {}, 0, {i: (2**128 - 1 if i == 1 else 9) for i in range(32)})
a64hand(0x4e30a820, {}, 0, {1: 0x807f807f807f807f807f807f807f807f})
a64hand(0x6e30a820, {}, 0, {1: 0x807f807f807f807f807f807f807f807f})
a64hand(0x0eb1b820, {}, 0, {})
def x64hand(bs, r):
    regs = [r.get(i, 0) for i in range(16)]
    regs[4] = XDATA + 0x800  # RSP is not read by these instructions
    x64case("r5/x64.hand", bytes(bs), regs, flags=0)
x64hand([0x0f, 0xa3, 0xca], {1: 33, 2: 2})
x64hand([0x48, 0x0f, 0xba, 0xea, 0xc8], {})
x64hand([0x66, 0x0f, 0xa4, 0xc2, 0x10], {0: 0xabcd, 2: 0x777700001235})
x64hand([0x66, 0x0f, 0xa4, 0xc2, 0x11], {i: 1 for i in range(16)})
x64hand([0x0f, 0xac, 0xc2, 0x20], {2: 0xffffffff00000005})
x64hand([0xf3, 0x0f, 0xbc, 0xd0], {2: 2**64 - 1})
x64hand([0xf3, 0x48, 0x0f, 0xbd, 0xd0], {0: 1})
x64hand([0xf3, 0x48, 0x0f, 0xb8, 0xd0], {0: 2**64 - 1})
x64hand([0x0f, 0xbc, 0xd0], {})
x64hand([0x0f, 0xbd, 0xd0], {0: 0x80000000, 2: 2**64 - 1})

os.makedirs(out, exist_ok=True)
for name, cs in (("a64.jsonl", a64), ("x64.jsonl", x64)):
    with open(os.path.join(out, name), "w") as f:
        for c in cs:
            f.write(json.dumps(c) + "\n")
print("arm64 cases:", len(a64), " amd64 cases:", len(x64))
