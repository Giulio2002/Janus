#!/usr/bin/env python3
"""Words for the A64 floating-point decoder sweep (docs/AUDIT-FP.md, row DEC-A64): every value of
bits 31:24 in the scalar FP space (M, S, 11110/11111) and the Advanced SIMD (vector and scalar)
FP neighbours, every value of bits 23:10 (ftype, Rm/opcode/rmode/cond/imm8 fields), and eight
patterns of bits 9:0 (Rn/Rd, including the should-be-zero imm5 and opcode2<2:0> fields).
Writes little-endian words to argv[1] (raw, for objdump -b binary) and hex lines to argv[2]."""
import random, struct, sys
r = random.Random(7)
tops = [0x1E, 0x1F, 0x9E, 0x9F, 0x3E, 0x3F, 0xBE, 0xBF,
        0x0E, 0x2E, 0x4E, 0x6E, 0x0F, 0x2F, 0x4F, 0x6F, 0x5E, 0x7E, 0x5F, 0x7F]
lows = [0x000, 0x3FF, 0x001, 0x020, 0x008, 0x3E0, 0x0E7, 0x118]
with open(sys.argv[1], "wb") as raw, open(sys.argv[2], "w") as hx:
    for top in tops:
        for mid in range(1 << 14):
            for lo in lows + [r.getrandbits(10)]:
                w = top << 24 | mid << 10 | lo
                raw.write(struct.pack("<I", w))
                hx.write("0x%08x\n" % w)
