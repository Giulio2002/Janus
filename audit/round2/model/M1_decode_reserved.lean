import Janus
/-! M1: reserved / UNALLOCATED / CONSTRAINED UNPREDICTABLE encodings next to the instructions
added on agent/ee280a4 (atomics) and agent/arm64cov2 accb078 (Advanced SIMD). Every `none`
below is an encoding GNU objdump 2.46 reports as `undefined` (or, for LDLAR/DC CIVAC/MSR/
LD2 multiple/LD2R, a valid instruction outside the subset) and the ARM ARM decode pseudocode
marks UNDEFINED/reserved; every `some` is its allocated neighbour. All are kernel-checked
(`decide`), so this file failing to compile means the decoder changed.
Result: BLOCKED (decoder correct) for every case.
Run: lake env lean audit/round2/model/M1_decode_reserved.lean -/
open Janus.Arm64

-- Ordered / exclusive / CAS (`size 001000 o2 L o1 Rs o0 Rt2 Rn Rt`)
example : decode 0xc8c0fc02 = none := by decide   -- LDAR, Rs != 11111 (SBO)
example : decode 0xc8dff802 = none := by decide   -- LDAR, Rt2 != 11111 (SBO)
example : decode 0xc8df7c02 = none := by decide   -- LDLAR (o0 = 0, FEAT_LOR)
example : (decode 0xc8dffc02).isSome := by decide -- LDAR x2, [x0]
example : decode 0x48217c02 = none := by decide   -- CASP, Rs odd: UNDEFINED
example : decode 0x48227c03 = none := by decide   -- CASP, Rt odd: UNDEFINED
example : decode 0x48207802 = none := by decide   -- CASP, Rt2 field != 11111
example : (decode 0x48207c02).isSome := by decide -- CASP x0, x1, x2, x3, [x0]
example : decode 0xc85f7c1b = .some (.ldExcl 3 false 0 27) := by decide  -- LDXR x27, [x0]
example : decode 0xc81bfc01 = none := by decide   -- STLXR (store-exclusive: rejected by design)
-- LDAPR (`size 111000 1 0 1 11111 1100 00 Rn Rt`)
example : (decode 0xf8bfc002).isSome := by decide -- LDAPR x2, [x0]
example : decode 0xf8ffc000 = none := by decide   -- R = 1
example : decode 0xf8a0c000 = none := by decide   -- Rs != 11111
example : decode 0xf83fc000 = none := by decide   -- A = 0
-- AES (`01001110 size 10100 opcode 10 Rn Rd`, size must be 00)
example : (decode 0x4e284820).isSome := by decide -- AESE v0.16b, v1.16b
example : decode 0x4e684820 = none := by decide   -- size = 01
example : decode 0x4ea84820 = none := by decide   -- size = 10
example : (decode 0x4e285820).isSome := by decide -- AESD v0.16b, v1.16b
example : decode 0x4e288820 = none := by decide   -- AES group, opcode 01000: unallocated
-- Three same: size:Q = 110 reserved for arithmetic/compares
example : decode 0x0ee08400 = none := by decide   -- ADD .1D
example : (decode 0x4ee08400).isSome := by decide -- ADD v0.2d
example : decode 0x0ec08400 = none := by decide
-- EXT Q = 0, imm4<3> = 1
example : decode 0x2e004000 = none := by decide
-- Copy: DUP .1D, UMOV W<-D, SMOV W<-S, INS with Q = 0, imm5 = x0000
example : decode 0x0e080c20 = none := by decide
example : decode 0x0e083c20 = none := by decide
example : decode 0x0e042c20 = none := by decide
example : decode 0x0e011c20 = none := by decide
example : decode 0x4e100420 = none := by decide   -- DUP element, imm5 = 10000
-- Modified immediate: op = 1, cmode = 1111, Q = 0 unallocated; Q = 1 is FMOV .2D
example : decode 0x2f00f400 = none := by decide
example : (decode 0x6f00f400).isSome := by decide
example : decode 0x0f00fc00 = none := by decide   -- o2 = 1 (FMOV half precision, FEAT_FP16)
-- Shift by immediate: immh<3> = 1 with Q = 0, SHRN/SSHLL with immh<3> = 1
example : decode 0x0f400400 = none := by decide
example : decode 0x0f408400 = none := by decide
example : decode 0x0f40a400 = none := by decide
-- Across lanes: size:Q = 100 (ADDV .2S) reserved
example : decode 0x0eb1b800 = none := by decide
-- SIMD&FP loads/stores
example : decode 0x0c408000 = none := by decide   -- LD2 (multiple): outside the subset
example : decode 0x0d404400 = none := by decide   -- LD1 {v.h}[i], size<0> = 1: UNDEFINED
example : decode 0x0d40d000 = none := by decide   -- LD1R with S = 1: UNDEFINED
example : decode 0x0d00c000 = none := by decide   -- "ST1R" (L = 0, replicate): UNDEFINED
example : decode 0x0d409400 = none := by decide   -- LD1 {v.d}[i] with S = 1: UNDEFINED
example : (decode 0x0d408400).isSome := by decide -- LD1 {v0.d}[0], [x0]
example : decode 0x7dc00000 = none := by decide   -- LDR, opc<1>:size = 101 > 4: UNDEFINED
example : decode 0x2d400000 = none := by decide   -- LDP s0, s0: CONSTRAINED UNPREDICTABLE
example : decode 0xdc000000 = none := by decide   -- LDR (literal, SIMD) opc = 11
-- System
example : decode 0xd51bd040 = none := by decide   -- MSR TPIDR_EL0, x0
example : decode 0xd50b7e20 = none := by decide   -- DC CIVAC
example : decode 0xd50b7420 = some (.dcZva 0) := by decide
example : decode 0xf98000ff = some (.prefetch 31) := by decide  -- PRFM #0x1f: a hint (reserved prfop = NOP)

