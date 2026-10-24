import Janus

/-!
# Floating-point model: evaluated examples

Concrete results of the IEEE core and of both ISA wrappers, checked by the kernel
(`decide +kernel`). The validation of the model is the differential oracles and TestFloat
(`docs/ORACLE*.md`); these examples pin a few hand-checked values and the decodings of the
words Go emits.
-/

open Janus.Float

-- rounding: ties to even, subnormals, overflow by direction
example : (round binary64 .rne false (2^53 + 1) (-53)).bits = 0x3FF0000000000000 := by decide +kernel
example : (round binary64 .rne false (2^54 + 3) (-54)).bits = 0x3FF0000000000001 := by decide +kernel
example : (round binary64 .rne false 1 (-1074)).bits = 1 := by decide +kernel
example : (round binary64 .rne false 1 (-1075)).bits = 0 := by decide +kernel
example : (round binary64 .rne false 3 (-1076)).bits = 1 := by decide +kernel
example : (round binary64 .rne false 1 1024).bits = 0x7FF0000000000000 := by decide +kernel
example : (round binary64 .rz false 1 1024).bits = 0x7FEFFFFFFFFFFFFF := by decide +kernel
example : (round binary32 .rne true 3 0).bits = 0xC0400000 := by decide +kernel
example : isqrt 1000000 = 1000 ∧ isqrt 999999 = 999 := by decide +kernel

section Arm
open Janus.Arm64 Janus.Arm64.FP
example : fpAdd binary64 0 0x3FF0000000000000 0x4000000000000000 = (0x4008000000000000, {}) := by decide +kernel
-- 0.1 + 0.2 = 0.30000000000000004, inexact
example : fpAdd binary64 0 0x3FB999999999999A 0x3FC999999999999A = (0x3FD3333333333334, ⟨IXC, 0⟩) := by
  decide +kernel
example : (fpSqrt binary64 0 0x4000000000000000).1 = 0x3FF6A09E667F3BCD := by decide +kernel
example : (fpDiv binary64 0 0x3FF0000000000000 0x4008000000000000).1 = 0x3FD5555555555555 := by decide +kernel
-- a signalling NaN is quieted (IOC); with FPCR.DN the default NaN; with AH it is negative
example : fpAdd binary64 0 0x7FF0000000000001 0x3FF0000000000000 = (0x7FF8000000000001, ⟨IOC, 0⟩) := by
  decide +kernel
example : (fpAdd binary64 (2^25) 0x7FF0000000000001 0x3FF0000000000000).1 = 0x7FF8000000000000 := by
  decide +kernel
example : (fpAdd binary64 (2^25 + 2) 0x7FF0000000000001 0x3FF0000000000000).1 = 0xFFF8000000000000 := by
  decide +kernel
-- FCVTZU saturates: -1.5 → 0, 2^64 → 2^64 - 1, NaN → 0, all with IOC
example : fpToFixed binary64 0 true .rz 64 0xBFF8000000000000 = (0, ⟨IOC, 0⟩) := by decide +kernel
example : (fpToFixed binary64 0 true .rz 64 0x43F0000000000000).1 = 2^64 - 1 := by decide +kernel
example : (fpToFixed binary64 0 true .rz 64 0x7FF8000000000000).1 = 0 := by decide +kernel
-- the words Go 1.26 emits for examples/basic/float.go
example : decode 0x1e612800 = some (.fpDP2 1 1 2 0 0) := by decide                -- fadd d0, d0, d1
example : decode 0x1e600863 = some (.fpDP2 1 0 0 3 3) := by decide                -- fmul d3, d3, d0
example : decode 0x1f440c21 = some (.fpDP3 1 false 4 false 3 1 1) := by decide    -- fmadd d1, d1, d4, d3
example : decode 0x9e790000 = some (.fpCvtInt true 1 3 1 0 0) := by decide        -- fcvtzu x0, d0
example : decode 0x1ee02000 = none := by decide                                   -- fcmp h0, h0 (half: rejected)
end Arm

section X86
open Janus.Amd64
example : decode [0xf2, 0x0f, 0x58, 0xc1] = some (.sseArith .add 64 0 (.xmm 1), 4) := by decide
example : decode [0x66, 0x0f, 0x2e, 0xc8] = some (.sseComi false 64 1 (.xmm 0), 4) := by decide
example : decode [0xf2, 0x48, 0x0f, 0x2c, 0xc8] = some (.cvtf2si true 64 64 1 (.xmm 0), 5) := by decide
example : decode [0x66, 0x0f, 0x3a, 0x0b, 0xc8, 0x01] = some (.sseRound 64 1 (.xmm 0) 1, 6) := by decide
example : decode [0x66, 0x0f, 0x58, 0xc1] = none := by decide                     -- addpd (packed: rejected)
example : (FP.binop .add binary64 (FP.ctl 0x1F80) 0x3FF0000000000000 0x4000000000000000).res =
    0x4008000000000000 := by decide +kernel
-- 0 × ∞ is the indefinite with IE; MINSD returns the second operand when one is a NaN
example : FP.binop .mul binary64 (FP.ctl 0x1F80) 0 0x7FF0000000000000 = ⟨0xFFF8000000000000, 1, 1⟩ := by
  decide +kernel
example : (FP.minmax false binary64 (FP.ctl 0x1F80) 0x7FF8000000000000 0x3FF0000000000000).res =
    0x3FF0000000000000 := by decide +kernel
-- CVTTSD2SI of NaN is the integer indefinite
example : (FP.toInt binary64 (FP.ctl 0x1F80) .rz 64 0x7FF8000000000000).res = 2^63 := by decide +kernel
end X86
