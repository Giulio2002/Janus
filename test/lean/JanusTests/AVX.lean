import Janus

/-!
# Known-answer tests of the AVX / AVX2 / FMA3 / F16C instructions (WP-F)

Decoding (instruction and length; the encodings are GNU `as` output), the lane semantics on
literals, and the **VEX.128 zero-upper rule** on a two-instruction sequence (a 256-bit
`VPADDD`, then a legacy-SSE `PADDD` that keeps the upper half it produced; the same sequence
with a VEX.128 `VPADDD` instead zeroes it), all evaluated by the kernel. The values were also
observed on the oracle host (`oracle-amd64` self-test `vpaddd ...`).
-/

namespace JanusTests.AVX

open Janus.Amd64 Janus.Amd64.ExecAVX

-- decoding
example : decode [0xc5, 0xf5, 0xfe, 0xc2] = some (.avx (.pint (.add 32) 256 0 1 (.xmm 2)), 4) := by decide
example : decode [0xc5, 0xf1, 0xfe, 0xc2] = some (.avx (.pint (.add 32) 128 0 1 (.xmm 2)), 4) := by decide
example : decode [0xc4, 0xe3, 0x7d, 0x39, 0xc1, 0x01] = some (.avx (.extract128 (.xmm 1) 0 1), 6) := by decide
example : decode [0xc4, 0xe3, 0x75, 0x38, 0xc2, 0x01] = some (.avx (.insert128 0 1 (.xmm 2) 1), 6) := by decide
example : decode [0xc4, 0xe2, 0x75, 0x36, 0xc2] = some (.avx (.permd 0 1 (.xmm 2)), 5) := by decide
example : decode [0xc4, 0xe3, 0xfd, 0x00, 0xc1, 0x4e] = some (.avx (.permq 0 (.xmm 1) 0x4e), 6) := by decide
example : decode [0xc4, 0xe3, 0x75, 0x46, 0xc2, 0x21] = some (.avx (.perm2 0 1 (.xmm 2) 0x21), 6) := by decide
example : decode [0xc4, 0xe2, 0x7d, 0x58, 0xc1] = some (.avx (.bcast 32 256 0 (.xmm 1)), 5) := by decide
example : decode [0xc4, 0xe2, 0x75, 0x00, 0xc2] = some (.vop .pshufb 256 0 1 (.xmm 2), 5) := by decide
example : decode [0xc4, 0xe2, 0x6d, 0x90, 0x04, 0x88] =
    some (.avx (.gather 32 32 256 0 2 ⟨some 0, some 1, 2, 0, false, false⟩), 6) := by decide
example : decode [0xc4, 0xe2, 0x75, 0x8c, 0x07] =
    some (.avx (.maskmov 32 256 true 0 1 ⟨some 7, none, 0, 0, false, false⟩), 5) := by decide
example : decode [0xc4, 0xe2, 0x75, 0xb8, 0xc2] = some (.avx (.fma 231 false false 0 32 256 0 1 (.xmm 2)), 5) := by decide
example : decode [0xc5, 0xf3, 0x58, 0xc2] = some (.avx (.sArith .add 64 0 1 (.xmm 2)), 4) := by decide
example : decode [0xc4, 0xe1, 0xf9, 0x6e, 0xd6] = some (.avx (.movdG 64 2 (.reg 6)), 5) := by decide
example : decode [0xc5, 0xfc, 0x77] = some (.avx .vzeroall, 3) := by decide
example : decode [0xc4, 0xe2, 0x7d, 0x13, 0xc1] = some (.avx (.cvtph2ps 256 0 (.xmm 1)), 5) := by decide
example : decode [0xc4, 0xe2, 0x75, 0x47, 0xc2] = some (.avx (.shiftv .sll 32 256 0 1 (.xmm 2)), 5) := by decide
example : decode [0xc4, 0xe3, 0x75, 0x02, 0xc2, 0xf0] = some (.avx (.pimm .blendps 256 0 1 (.xmm 2) 0xf0), 6) := by decide
example : decode [0xc5, 0xf4, 0xc2, 0xc2, 0x1e] = some (.avx (.fpCmp 32 256 0 1 (.xmm 2) 30), 5) := by decide
example : decode [0xc5, 0xfd, 0x72, 0xf1, 0x03] = some (.avx (.pshift .sll 32 256 0 1 3), 5) := by decide
example : decode [0xc5, 0xf1, 0x73, 0xd8, 0x08] = some (.avx (.pshift .srldq 128 128 1 0 8), 5) := by decide
example : decode [0xc4, 0xe2, 0x7d, 0x30, 0xc1] = some (.avx (.pmovx false 8 16 256 0 (.xmm 1)), 5) := by decide
-- rejected: VPERMD at VEX.L0 and with VEX.W1, a gather whose mask is its destination, VCMPPS with
-- imm8 ≥ 32, VRCPPS (implementation-specific), scalar FMA3 at VEX.L1, VEXTRACTI128 with
-- VEX.vvvv ≠ 1111
example : decode [0xc4, 0xe2, 0x71, 0x36, 0xc2] = none := by decide
example : decode [0xc4, 0xe2, 0xf5, 0x36, 0xc2] = none := by decide
example : decode [0xc4, 0xe2, 0x7d, 0x90, 0x04, 0x88] = none := by decide
example : decode [0xc5, 0xf4, 0xc2, 0xc2, 0x20] = none := by decide
example : decode [0xc5, 0xfc, 0x53, 0xc1] = none := by decide
example : decode [0xc4, 0xe2, 0xf5, 0xb9, 0xc2] = none := by decide
example : decode [0xc4, 0xe3, 0x75, 0x39, 0xc1, 0x01] = none := by decide

-- lane semantics
/-- `VPADDD ymm`: per 128-bit lane, wrapping. -/
example : pintV (.add 32) 256 (0xFFFFFFFF * 2 ^ 128 + 1) (1 * 2 ^ 128 + 2) = 3 := by decide
/-- `VPERM2I128 $0x21`: the upper lane of `src1`, then the lower lane of `src2`. -/
example : perm2V (5 * 2 ^ 128 + 4) (7 * 2 ^ 128 + 6) 0x21 = 5 + 6 * 2 ^ 128 := by decide
/-- `VPERM2I128` with `imm8<3>`: the lower result lane zeroed. -/
example : perm2V (5 * 2 ^ 128 + 4) (7 * 2 ^ 128 + 6) 0x38 = 7 * 2 ^ 128 := by decide
/-- `VPSRAVD`: a count ≥ 32 fills with the sign. -/
example : shiftvV .sra 32 128 0x80000000 33 = 0xFFFFFFFF := by decide
/-- `VPSLLVD`: a count ≥ 32 gives zero. -/
example : shiftvV .sll 32 128 1 32 = 0 := by decide
/-- `VSHUFPD ymm` uses `imm8<3:2>` in the upper lane. -/
example : pimmV .shufpd 256 0 (2 ^ 192 * 9) 0b1000 = 2 ^ 192 * 9 := by decide
/-- `VPMOVZXBW ymm`: 16 bytes to 16 words. -/
example : pmovxV false 8 16 256 (0xFF * 2 ^ 120 + 0x80) = 0x80 + 0xFF * 2 ^ 240 := by decide
/-- `VCVTPH2PS` of binary16 1.0 (`3C00H`): binary32 1.0 (`3F800000H`). -/
example : (h2s (FP.ctl 0x1F80) 0x3C00).res = 0x3F800000 := by decide
/-- The VEX predicate `GT_OQ` (30) on 2.0 > 1.0. -/
example : (vcmp Janus.Float.binary32 (FP.ctl 0x1F80) 30 0x40000000 0x3F800000).res = 0xFFFFFFFF := by decide

/-! ## The VEX.128 zero-upper rule on a sequence -/

/-- `XMM1 = [1 2 3 4]`, `XMM2 = XMM3 = [0x10 0x10 0xFFFFFFFF 0x10]` (dwords), the upper halves of
`YMM1`, `YMM2` as the oracle self-test sets them. -/
def s0 : State :=
  { regs := fun _ => 0, rip := 0, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun i =>
      if i = 1 then 0x00000004_00000003_00000002_00000001
      else if i = 2 ∨ i = 3 then 0x00000010_FFFFFFFF_00000010_00000010 else 0,
    ymmHi := fun i =>
      if i = 1 then 0xFFFFFFFFFFFFFFFE_2222222222222222
      else if i = 2 then 0xFFFFFFFFFFFFFFFD_3333333333333333 else 0x1111,
    mem := default }

/-- The upper half of `YMM0` and `XMM0` after running `bs₁` then `bs₂` from `s0`. -/
def after (bs₁ bs₂ : List Nat) : Option (Nat × Nat) :=
  match step bs₁ s0 with
  | .ok s1 =>
    match step bs₂ s1 with
    | .ok s2 => some ((s2.ymmHi 0).toNat, (s2.xmm 0).toNat)
    | .error _ => none
  | .error _ => none

/-- `VPADDD ymm0, ymm1, ymm2` then `PADDD xmm0, xmm3`: the legacy-SSE instruction keeps the
upper half that the 256-bit one wrote. -/
example : after [0xc5, 0xf5, 0xfe, 0xc2] [0x66, 0x0f, 0xfe, 0xc3] =
    some (0xFFFFFFFE_FFFFFFFB_55555555_55555555, 0x00000024_00000001_00000022_00000021) := by decide

/-- `VPADDD xmm0, xmm1, xmm2` then `PADDD xmm0, xmm3`: the VEX.128 instruction zeroed it. -/
example : after [0xc5, 0xf1, 0xfe, 0xc2] [0x66, 0x0f, 0xfe, 0xc3] =
    some (0, 0x00000024_00000001_00000022_00000021) := by decide

/-- And with a VEX.128 `VPADDD xmm0, xmm0, xmm3` as the second instruction, zero again. -/
example : after [0xc5, 0xf5, 0xfe, 0xc2] [0xc5, 0xf9, 0xfe, 0xc3] =
    some (0, 0x00000024_00000001_00000022_00000021) := by decide

/-- The symbolic rule, for any state: after a VEX.128 `VPADDD` writing `XMM0`, bits 255:128 of
`YMM0` are zero (`Janus.Amd64.Tactic.exec_vex128_zero_upper`, instantiated). -/
example (s s' : State) (h : step [0xc5, 0xf1, 0xfe, 0xc2] s = .ok s') : s'.ymmHi 0 = 0 := by
  rw [step_of_decode (i := .avx (.pint (.add 32) 128 0 1 (.xmm 2))) (len := 4) (by decide)] at h
  exact Janus.Amd64.Tactic.exec_vex128_zero_upper _ _ s s' h 0 (by simp [AvxI.vdsts])

/-- And a legacy-SSE `PADDD` keeps every upper half (`Janus.Amd64.Tactic.exec_sse_preserves_upper`). -/
example (s s' : State) (h : step [0x66, 0x0f, 0xfe, 0xc3] s = .ok s') : s'.ymmHi = s.ymmHi := by
  rw [step_of_decode (i := .sse (.pint (.add 32) 0 (.xmm 3))) (len := 4) (by decide)] at h
  exact Janus.Amd64.Tactic.exec_sse_preserves_upper _ _ s s' h

end JanusTests.AVX
