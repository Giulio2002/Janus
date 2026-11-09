import Janus.Arm64.Decode

/-!
# Decoder tests

Words are taken from `go build` (Go 1.26, `GOARCH=arm64`) output and from `aarch64-linux-gnu-as`;
the comment above each test is the `objdump` disassembly. All are checked by `decide`
(kernel evaluation of `decode` on the literal), some also by `rfl`.
-/

namespace JanusTests.Decode
open Janus.Arm64

/-! ## Real Go output (`main.Sum`, `main.Mix`, `main.Div`, `main.Idx` of a test program) -/

-- str x0, [sp, #8]
example : decode 0xf90007e0 = some (.ldstUImm 3 0 1 31 0) := by decide
-- mov x2, xzr
example : decode 0xaa1f03e2 = some (.logicalShifted true .orr .lsl false 31 0 31 2) := by decide
-- b <label>
example : decode 0x14000004 = some (.b false 4) := by decide
-- ldr x4, [x0, x2, lsl #3]
example : decode 0xf8627804 = some (.ldstReg 3 1 2 .uxtx true 0 4) := by decide
-- add x3, x3, x4
example : decode 0x8b040063 = some (.addSubShifted true false false .lsl 4 0 3 3) := by decide
-- add x2, x2, #0x1
example : decode 0x91000442 = some (.addSubImm true false false false 1 2 2) := by decide
-- cmp x1, x2
example : decode 0xeb02003f = some (.addSubShifted true true true .lsl 2 0 1 31) := by decide
-- b.gt <label>
example : decode 0x54ffff8c = some (.bcond 524284 12) := by decide
-- ret
example : decode 0xd65f03c0 = some (.ret 30) := by decide
-- sbfiz x4, x2, #3, #32
example : decode 0x937d7c44 = some (.bitfield true .sbfm true 61 31 2 4) := by decide
-- madd x4, x1, x0, x4
example : decode 0x9b001024 = some (.madd true false 0 4 1 4) := by decide
-- add x4, x4, x3, asr #63
example : decode 0x8b83fc84 = some (.addSubShifted true false false .asr 3 63 4 4) := by decide
-- mov x5, #0x4925
example : decode 0xd28924a5 = some (.moveWide true .movz 0 18725 5) := by decide
-- movk x5, #0x2492, lsl #16
example : decode 0xf2a49245 = some (.moveWide true .movk 1 9362 5) := by decide
-- smulh x5, x3, x5
example : decode 0x9b457c65 = some (.mulh false 5 3 5) := by decide
-- sub x4, x4, x5, asr #1
example : decode 0xcb850484 = some (.addSubShifted true true false .asr 5 1 4 4) := by decide
-- eor x4, x4, x4, ror #51
example : decode 0xcac4cc84 = some (.logicalShifted true .eor .ror false 4 51 4 4) := by decide
-- umulh x5, x0, x1
example : decode 0x9bc17c05 = some (.mulh true 1 0 5) := by decide
-- rev w1, w1
example : decode 0x5ac00821 = some (.rev false 2 1 1) := by decide
-- sxtb x2, w2
example : decode 0x93401c42 = some (.bitfield true .sbfm true 0 7 2 2) := by decide
-- clz x7, x0
example : decode 0xdac01007 = some (.clz true 0 7) := by decide
-- csel x3, x5, x6, gt
example : decode 0x9a86c0a3 = some (.condSel true false 6 12 false 5 3) := by decide
-- sub x3, x3, #0x40
example : decode 0xd1010063 = some (.addSubImm true true false false 64 3 3) := by decide
-- ldr x16, [x28, #16]
example : decode 0xf9400b90 = some (.ldstUImm 3 1 2 28 16) := by decide
-- cmp sp, x16
example : decode 0xeb3063ff = some (.addSubExt true true true 16 .uxtx 0 31 31) := by decide
-- b.ls <label>
example : decode 0x54000169 = some (.bcond 11 9) := by decide
-- str x30, [sp, #-16]!
example : decode 0xf81f0ffe = some (.ldstImm9 3 0 .pre 496 31 30) := by decide
-- stur x29, [sp, #-8]
example : decode 0xf81f83fd = some (.ldstImm9 3 0 .unscaled 504 31 29) := by decide
-- sub x29, sp, #0x8
example : decode 0xd10023fd = some (.addSubImm true true false false 8 31 29) := by decide
-- cbz x1, <label>
example : decode 0xb40000a1 = some (.cb true false 5 1) := by decide
-- sdiv x0, x0, x1
example : decode 0x9ac10c00 = some (.div true true 1 0 0) := by decide
-- ldur x29, [sp, #-8]
example : decode 0xf85f83fd = some (.ldstImm9 3 1 .unscaled 504 31 29) := by decide
-- ldr x30, [sp], #16
example : decode 0xf84107fe = some (.ldstImm9 3 1 .post 16 31 30) := by decide
-- bl <label>
example : decode 0x97ff1ae5 = some (.b true 67050213) := by decide
-- nop
example : decode 0xd503201f = some (.hint 0 0) := by decide
-- stp x0, x1, [sp, #8]
example : decode 0xa90087e0 = some (.ldstPair 2 .offset false 1 1 31 0) := by decide
-- mov x3, x30
example : decode 0xaa1e03e3 = some (.logicalShifted true .orr .lsl false 30 0 31 3) := by decide
-- ldp x0, x1, [sp, #8]
example : decode 0xa94087e0 = some (.ldstPair 2 .offset true 1 1 31 0) := by decide
-- b <label>
example : decode 0x17ffffef = some (.b false 67108847) := by decide
-- ldrb w0, [x0, x3]
example : decode 0x38636800 = some (.ldstReg 0 1 3 .uxtx false 0 0) := by decide
-- b.cs <label>
example : decode 0x540000a2 = some (.bcond 5 2) := by decide

example : decode 0x8b010000 = some (.addSubShifted true false false .lsl 1 0 0 0) := rfl

/-! ## Other supported encodings (assembled with `aarch64-linux-gnu-as`) -/

-- add x0, sp, #0x10
example : decode 0x910043e0 = some (.addSubImm true false false false 16 31 0) := by decide
-- sub x0, x0, #0x1, lsl #12
example : decode 0xd1400400 = some (.addSubImm true true false true 1 0 0) := by decide
-- sub x0, x0, w1, sxtw #2
example : decode 0xcb21c800 = some (.addSubExt true true false 1 .sxtw 2 0 0) := by decide
-- adc x0, x0, x1 / sbcs w0, w0, w1
example : decode 0x9a010000 = some (.addSubCarry true false false 1 0 0) := by decide
example : decode 0x7a010000 = some (.addSubCarry false true true 1 0 0) := by decide
-- and x0, x0, #0xff
example : decode 0x92401c00 = some (.logicalImm true .and true 0 7 0 0) := by decide
-- mov w0, #0x55555555 (orr w0, wzr, #0x55555555)
example : decode 0x3200f3e0 = some (.logicalImm false .orr false 0 60 31 0) := by decide
-- bic x0, x0, x1 / eon x0, x0, x1, ror #8
example : decode 0x8a210000 = some (.logicalShifted true .and .lsl true 1 0 0 0) := by decide
example : decode 0xcae12000 = some (.logicalShifted true .eor .ror true 1 8 0 0) := by decide
-- mov w0, #0x12340000 / movn w0, #0
example : decode 0x52a24680 = some (.moveWide false .movz 1 0x1234 0) := by decide
example : decode 0x12800000 = some (.moveWide false .movn 0 0 0) := by decide
-- lsl x0, x1, #4 (ubfm x0, x1, #60, #59)
example : decode 0xd37cec20 = some (.bitfield true .ubfm true 60 59 1 0) := by decide
-- bfi x0, x1, #8, #16
example : decode 0xb3783c20 = some (.bitfield true .bfm true 56 15 1 0) := by decide
-- extr x0, x1, x2, #12 / ror w0, w1, #5
example : decode 0x93c23020 = some (.extr true true 2 12 1 0) := by decide
example : decode 0x13811420 = some (.extr false false 1 5 1 0) := by decide
-- csneg x0, x1, x2, ge
example : decode 0xda82a420 = some (.condSel true true 2 10 true 1 0) := by decide
-- ccmp x1, x2, #0x4, ne / ccmn w1, #0x5, #0x2, eq
example : decode 0xfa421024 = some (.condCmpReg true true 2 1 1 4) := by decide
example : decode 0x3a450822 = some (.condCmpImm false false 5 0 1 2) := by decide
-- smull x0, w1, w2 / umsubl x0, w1, w2, x3
example : decode 0x9b227c20 = some (.maddl false false 2 31 1 0) := by decide
example : decode 0x9ba28c20 = some (.maddl true true 2 3 1 0) := by decide
-- udiv x0, x1, x2 / lsr w0, w1, w2 / ror x0, x1, x2
example : decode 0x9ac20820 = some (.div true false 2 1 0) := by decide
example : decode 0x1ac22420 = some (.shiftV false .lsr 2 1 0) := by decide
example : decode 0x9ac22c20 = some (.shiftV true .ror 2 1 0) := by decide
-- cls x0, x1 / rbit w0, w1 / rev x0, x1 / rev16 w0, w1 / rev32 x0, x1
example : decode 0xdac01420 = some (.cls true 1 0) := by decide
example : decode 0x5ac00020 = some (.rbit false 1 0) := by decide
example : decode 0xdac00c20 = some (.rev true 3 1 0) := by decide
example : decode 0x5ac00420 = some (.rev false 1 1 0) := by decide
example : decode 0xdac00820 = some (.rev true 2 1 0) := by decide
-- adr x0, .+8 / adrp x0, .+0x5000
example : decode 0x10000040 = some (.adr false 0 2 0) := by decide
example : decode 0xb0000020 = some (.adr true 1 1 0) := by decide
-- tbz x1, #33, .+12 / tbnz w1, #3, .+12
example : decode 0xb6080061 = some (.tb true false 1 3 1) := by decide
example : decode 0x37180061 = some (.tb false true 3 3 1) := by decide
-- br x1 / blr x1
example : decode 0xd61f0020 = some (.br 1) := by decide
example : decode 0xd63f0020 = some (.blr 1) := by decide
-- yield / dmb ish / dsb sy / isb
example : decode 0xd503203f = some (.hint 0 1) := by decide
example : decode 0xd5033bbf = some (.barrier 11 5) := by decide
example : decode 0xd5033f9f = some (.barrier 15 4) := by decide
example : decode 0xd5033fdf = some (.barrier 15 6) := by decide
-- ldrsb w0, [x1] / ldrsw x0, [x1, #4] / strh w0, [x1, #2]
example : decode 0x39c00020 = some (.ldstUImm 0 3 0 1 0) := by decide
example : decode 0xb9800420 = some (.ldstUImm 2 2 1 1 0) := by decide
example : decode 0x79000420 = some (.ldstUImm 1 0 1 1 0) := by decide
-- ldr w0, [x1, w2, sxtw]
example : decode 0xb862c820 = some (.ldstReg 2 1 2 .sxtw false 1 0) := by decide
-- ldpsw x0, x2, [x1, #-8] / stp x29, x30, [sp, #-32]! / ldp x29, x30, [sp], #32
example : decode 0x697f0820 = some (.ldstPair 1 .offset true 0x7e 2 1 0) := by decide
example : decode 0xa9be7bfd = some (.ldstPair 2 .pre false 0x7c 30 31 29) := by decide
example : decode 0xa8c27bfd = some (.ldstPair 2 .post true 4 30 31 29) := by decide
-- ldr x0, .+16 / ldrsw x0, .-16
example : decode 0x58000080 = some (.ldrLit 1 4 0) := by decide
example : decode 0x98ffff80 = some (.ldrLit 2 0x7fffc 0) := by decide

/-! ## Rejected: outside the subset -/

-- WP-C: kernel, trap and environment encodings (Janus.Arm64.DecodeSys)
example : decode 0x00000000 = some (.udf 0) := by decide   -- udf #0
example : decode 0x0000beef = some (.udf 0xbeef) := by decide
example : decode 0xd4000001 = some (.svc 0) := by decide   -- svc #0
example : decode 0xd4000021 = none := by decide   -- svc #1: only #0
example : decode 0xd4200000 = some (.brk 0) := by decide   -- brk #0
example : decode 0xd43e0000 = some (.brk 0xf000) := by decide   -- brk #0xf000
example : decode 0xd4400000 = none := by decide   -- hlt #0
example : decode 0xd4000002 = none := by decide   -- hvc #0
example : decode 0xd53be040 = some (.mrsEnv .cntvct 0) := by decide   -- mrs x0, cntvct_el0
example : decode 0xd53be003 = some (.mrsEnv .cntfrq 3) := by decide   -- mrs x3, cntfrq_el0
example : decode 0xd5380001 = some (.mrsEnv .midr 1) := by decide   -- mrs x1, midr_el1
example : decode 0xd53b42a0 = some (.mrsEnv .dit 0) := by decide   -- mrs x0, dit
-- the feature-ID registers (N5): Linux traps and emulates them at EL0; the value is arbitrary
example : decode 0xd5380600 = some (.mrsEnv (.idreg 6 0) 0) := by decide   -- mrs x0, id_aa64isar0_el1
example : decode 0xd5380625 = some (.mrsEnv (.idreg 6 1) 5) := by decide   -- mrs x5, id_aa64isar1_el1
example : decode 0xd5380640 = some (.mrsEnv (.idreg 6 2) 0) := by decide   -- mrs x0, id_aa64isar2_el1
example : decode 0xd5380400 = some (.mrsEnv (.idreg 4 0) 0) := by decide   -- mrs x0, id_aa64pfr0_el1
example : decode 0xd5380420 = some (.mrsEnv (.idreg 4 1) 0) := by decide   -- mrs x0, id_aa64pfr1_el1
example : decode 0xd5380480 = some (.mrsEnv (.idreg 4 4) 0) := by decide   -- mrs x0, id_aa64zfr0_el1
example : decode 0xd5380700 = some (.mrsEnv (.idreg 7 0) 0) := by decide   -- mrs x0, id_aa64mmfr0_el1
example : decode 0xd53807e3 = some (.mrsEnv (.idreg 7 7) 3) := by decide   -- mrs x3, s3_0_c0_c7_7 (reserved, RAZ)
example : decode 0xd5380100 = none := by decide   -- mrs x0, id_pfr0_el1 (AArch32 ID, CRm = 1): not exposed
example : decode 0xd53800a0 = none := by decide   -- mrs x0, mpidr_el1: not emulated at EL0
example : decode 0xd5380800 = none := by decide   -- CRm = 8: not the ID space
example : decode 0xd5390600 = none := by decide   -- op1 = 1
example : decode 0xd5381600 = none := by decide   -- CRn = 1
example : decode 0xd5180600 = none := by decide   -- msr id_aa64isar0_el1: not writable
example : decode 0xd51b42a0 = some (.msrDitReg 0) := by decide   -- msr dit, x0
example : decode 0xd503415f = some (.msrDitImm 1) := by decide   -- msr dit, #1
example : decode 0xd503405f = some (.msrDitImm 0) := by decide   -- msr dit, #0
example : decode 0xd503425f = none := by decide   -- msr dit, #2: reserved
example : decode 0xd53be020 = none := by decide   -- mrs x0, cntpct_el0: not accepted
example : decode 0xd53b4200 = some (.mrsNzcv 0) := by decide   -- mrs x0, nzcv
example : decode 0xd51b4200 = some (.msrNzcv 0) := by decide   -- msr nzcv, x0
example : decode 0xd53b4420 = some (.mrsFpsr 0) := by decide   -- mrs x0, fpsr
example : decode 0xd51b4420 = some (.msrFpsr 0) := by decide   -- msr fpsr, x0
example : decode 0xc85ffc01 = some (.ldExcl 3 true 0 1) := by decide   -- ldaxr x1, [x0]
example : decode 0xc81ffc01 = some (.stExcl 3 true 31 0 1) := by decide   -- stlxr wzr, x1, [x0]
example : decode 0xc81bfc02 = some (.stExcl 3 true 27 0 2) := by decide   -- stlxr w27, x2, [x0]
example : decode 0xc8027fe1 = some (.stExcl 3 false 2 31 1) := by decide   -- stxr w2, x1, [sp]
example : decode 0x08037ca4 = some (.stExcl 0 false 3 5 4) := by decide   -- stxrb w3, w4, [x5]
example : decode 0x4803fca4 = some (.stExcl 1 true 3 5 4) := by decide   -- stlxrh w3, w4, [x5]
example : decode 0x88037ca4 = some (.stExcl 2 false 3 5 4) := by decide   -- stxr w3, w4, [x5]
example : decode 0xc87f0440 = some (.ldExclPair true false 1 2 0) := by decide   -- ldxp x0, x1, [x2]
example : decode 0x887f8440 = some (.ldExclPair false true 1 2 0) := by decide   -- ldaxp w0, w1, [x2]
example : decode 0xc8230440 = some (.stExclPair true false 3 1 2 0) := by decide   -- stxp w3, x0, x1, [x2]
example : decode 0x882387e0 = some (.stExclPair false true 3 1 31 0) := by decide   -- stlxp w3, w0, w1, [sp]
example : decode 0x085f7c41 = some (.ldExcl 0 false 2 1) := by decide   -- ldxrb w1, [x2]
-- CONSTRAINED UNPREDICTABLE overlaps and should-be-one fields: rejected
example : decode 0xc801fc01 = none := by decide   -- stlxr w1, x1, [x0] (s = t)
example : decode 0xc800fc01 = none := by decide   -- stlxr w0, x1, [x0] (s = n)
example : decode 0xc81bf802 = none := by decide   -- stlxr with Rt2 != 11111
example : decode 0xc87f0040 = none := by decide   -- ldxp x0, x0, [x2] (t = t2)
example : decode 0xc87e0440 = none := by decide   -- ldxp with Rs != 11111
example : decode 0xc8200440 = none := by decide   -- stxp w0, x0, x1, [x2] (s = t)
example : decode 0xc8210440 = none := by decide   -- stxp w1, x0, x1, [x2] (s = t2)
example : decode 0xc8220440 = none := by decide   -- stxp w2, x0, x1, [x2] (s = n)
example : decode 0xc89ffc01 = some (.ldstOrdered 3 false false 0 1) := by decide   -- stlr x1, [x0]
example : decode 0xc89f7c01 = none := by decide   -- stllr x1, [x0] (FEAT_LOR)
example : decode 0xc89efc01 = none := by decide   -- stlr with Rs != 11111 (CONSTRAINED UNPREDICTABLE)
example : decode 0xf8e00001 = some (.atomic 3 true true 0 .add 0 1) := by decide   -- ldaddal x0, x1, [x0]
example : decode 0xc8fbfc01 = some (.cas 3 true true 27 0 1) := by decide   -- casal x27, x1, [x0]
example : decode 0x48207c82 = some (.casp true false false 0 4 2) := by decide   -- casp x0, x1, x2, x3, [x4]
example : decode 0x48217c82 = none := by decide   -- casp with odd Rs
example : decode 0xf8bfc020 = some (.ldstOrdered 3 true true 1 0) := by decide   -- ldapr x0, [x1]
example : decode 0xb8e18002 = some (.atomic 2 true true 1 .swp 0 2) := by decide   -- swpal w1, w2, [x0]
example : decode 0xd53b00e3 = some (.mrsDczid 3) := by decide   -- mrs x3, dczid_el0
example : decode 0xd50b7420 = some (.dcZva 0) := by decide   -- dc zva, x0
example : decode 0xd50b7520 = none := by decide   -- ic ivau, x0
example : decode 0x1e602000 = some (.fpCmp 1 0 0 0) := by decide   -- fcmp d0, d0
example : decode 0xfd400400 = some (.vldstUImm 3 1 1 0 0) := by decide   -- ldr d0, [x0, #8]
example : decode 0xf9800000 = some (.prefetch 0) := by decide   -- prfm pldl1keep, [x0]
example : decode 0xd8000000 = some (.prefetch 0) := by decide   -- prfm (literal)
example : decode 0xa8400000 = none := by decide   -- ldnp x0, x0, [x0]: LDNP not supported
example : decode 0xd503305f = some (.clrex 0) := by decide   -- clrex
example : decode 0xd503233f = none := by decide   -- paciasp
example : decode 0xd50323bf = none := by decide   -- autiasp
example : decode 0xd503207f = none := by decide   -- wfi
example : decode 0xd503271f = none := by decide   -- hint #0x38 (unallocated hint)
example : decode 0xd65f0bff = none := by decide   -- retaa
example : decode 0x54000010 = none := by decide   -- bc.eq (FEAT_HBC)
example : decode 0x9ac04c00 = some (.crypto (.crc32 true 0 false 3 0 0)) := by decide   -- crc32x w0, w0, x0 (Janus.Arm64.DecodeCrypto)
example : decode (2 ^ 32 + 0x8b010000) = none := by decide   -- not a 32-bit word

/-! ## Rejected: reserved / unallocated / UNDEFINED / CONSTRAINED UNPREDICTABLE -/

example : decode 0x8bc00000 = none := by decide   -- add x0, x0, x0, ROR #0 (shift = 11 reserved)
example : decode 0x0b008000 = none := by decide   -- add w0, w0, w0, lsl #32 (imm6<5> = 1, sf = 0)
example : decode 0x2a008000 = none := by decide   -- orr w0, w0, w0, lsl #32
example : decode 0x8b201400 = none := by decide   -- add x0, x0, w0, uxtb #5 (imm3 > 4)
example : decode 0x8b600000 = none := by decide   -- add extended with opt = 01
example : decode 0x12400000 = none := by decide   -- and w0 (logical imm) with N = 1, sf = 0
example : decode 0x9240fc00 = none := by decide   -- and x0, #imm with all-ones imms (reserved)
example : decode 0x9200f400 = none := by decide   -- N = 0, imms = 111101: element size 2, S = all ones
example : decode 0x9200f000 = some (.logicalImm true .and false 0 60 0 0) := by decide  -- #0x5555555555555555
example : decode 0x9203fc00 = none := by decide   -- N = 0, imms = 111111: len < 1
example : decode 0x52c00000 = none := by decide   -- movz w0, #0, lsl #32 (hw<1> = 1, sf = 0)
example : decode 0x92a00000 = some (.moveWide true .movn 1 0 0) := by decide  -- (valid, X form)
example : decode 0xb2800000 = none := by decide   -- move wide opc = 01
example : decode 0x93000000 = none := by decide   -- sbfm x0 with N = 0 (sf = 1)
example : decode 0x13400000 = none := by decide   -- sbfm w0 with N = 1 (sf = 0)
example : decode 0x13200000 = none := by decide   -- sbfm w0 with immr<5> = 1
example : decode 0x13008000 = none := by decide   -- sbfm w0 with imms<5> = 1
example : decode 0xf3400000 = none := by decide   -- bitfield opc = 11
example : decode 0x13808000 = none := by decide   -- extr w0 with imms<5> = 1
example : decode 0x93800000 = none := by decide   -- extr x0 with N = 0
example : decode 0x93a00000 = none := by decide   -- extract with o0 = 1
example : decode 0x1a800800 = none := by decide   -- csel with op2 = 10
example : decode 0x3a800000 = none := by decide   -- conditional select with S = 1
example : decode 0x7a400400 = none := by decide   -- ccmn with o2 = 1
example : decode 0x7a400010 = none := by decide   -- ccmn with o3 = 1
example : decode 0x1a400000 = none := by decide   -- conditional compare with S = 0
example : decode 0x9a000400 = none := by decide   -- adc with bits 15:10 ≠ 0 (rmif space)
example : decode 0x1b200000 = none := by decide   -- smaddl with sf = 0
example : decode 0x9b407c00 = some (.mulh false 0 0 0) := by decide  -- smulh x0, x0, x0 (Ra = 11111)
example : decode 0x9b400000 = none := by decide   -- ... but Ra ≠ 11111 is rejected
example : decode 0xdac00c00 = some (.rev true 3 0 0) := by decide
example : decode 0x5ac00c00 = none := by decide   -- rev (64-bit container) with sf = 0
example : decode 0xb9c00000 = none := by decide   -- size = 10, opc = 11 (unallocated)
example : decode 0xf9c00000 = none := by decide   -- size = 11, opc = 11 (unallocated)
example : decode 0xf8606800 = some (.ldstReg 3 1 0 .uxtx false 0 0) := by decide
example : decode 0xf8602800 = none := by decide   -- register offset with option<1> = 0
example : decode 0xf8400c00 = none := by decide   -- ldr x0, [x0, #0]! (writeback, Rn = Rt)
example : decode 0xf8008400 = none := by decide   -- str x0, [x0], #8 (writeback, Rn = Rt)
example : decode 0xf8400800 = none := by decide   -- ldtr x0, [x0] (unprivileged): not supported
example : decode 0xf84087ff = some (.ldstImm9 3 1 .post 8 31 31) := by decide  -- Rn = Rt = 31 ok
example : decode 0xa9400400 = some (.ldstPair 2 .offset true 0 1 0 0) := by decide  -- ldp x0, x1, [x0]
example : decode 0xa9c00400 = none := by decide   -- ldp x0, x1, [x0, #0]! (writeback, Rt = Rn)
example : decode 0xa9c08020 = none := by decide   -- ldp x0, x0, [x1, #8]! has Rt = Rt2
example : decode 0xa9400000 = none := by decide   -- ldp x0, x0, [x0] (Rt = Rt2)
example : decode 0x29000000 = some (.ldstPair 0 .offset false 0 0 0 0) := by decide  -- stp w0, w0 ok
example : decode 0x69000000 = none := by decide   -- stgp (opc = 01, L = 0)
example : decode 0xe9400000 = none := by decide   -- pair opc = 11
example : decode 0xd8000000 = some (.prefetch 0) := by decide   -- literal opc = 11 (PRFM)

end JanusTests.Decode
