import Janus

/-!
# Known-answer tests of the AVX-512 instructions (WP-G)

Decoding (instruction and length; the encodings are GNU `as` 2.46 output, and the real Go std
encodings of `internal/runtime/gc/scan`, `hash/crc32.ieeeCLMUL` and `runtime.asyncPreempt`),
the element semantics on literals (masking: merging and zeroing; `VPCOMPRESSQ`, `VPERMB`,
`VPTERNLOGQ`, the GF(2⁸) operations, `KORTEST`), the **EVEX zero-upper rule** on a literal state
(a 128-bit EVEX write zeroes bits 511:128) and for any state, and the VEX counterpart (a VEX
`VPADDD xmm` zeroes bits 511:128 of a `ZMM` register an EVEX instruction filled), all evaluated
by the kernel. The values agree with the oracle host (an Intel Xeon Gold 5412U, natively).
-/

namespace JanusTests.AVX512

open Janus.Amd64 Janus.Amd64.ExecEVEX
open Janus.Arm64 (elem ofElems)

/-! ## Decoding -/

-- VMAXPS {sae}, VADDPS {rz-sae}, VCMPPS {sae} into k1
example : decode [0x62, 0xf1, 0x6c, 0x18, 0x5f, 0xd9] =
    some (.evex (.fp .max 32 512 3 2 (.xmm 1) 0 5 0 false), 6) := by decide
example : decode [0x62, 0xf1, 0x6c, 0x78, 0x58, 0xd9] =
    some (.evex (.fp .add 32 512 3 2 (.xmm 1) 0 4 0 false), 6) := by decide
example : decode [0x62, 0xf1, 0x6c, 0x18, 0xc2, 0xc9, 0x03] =
    some (.evex (.cmp (.fp 3 true) 32 512 1 2 (.xmm 1) 0 0), 7) := by decide
-- VPERMB zmm0{k1}{z}, zmm0, zmm4 (expandAVX512_*), VPERMI2B zmm5{k1}{z}, zmm2, zmm3
example : decode [0x62, 0xf2, 0x7d, 0xc9, 0x8d, 0xc4] =
    some (.evex (.op .perm 8 512 0 0 (.xmm 4) 0 1 true), 6) := by decide
example : decode [0x62, 0xf2, 0x6d, 0xc9, 0x75, 0xeb] =
    some (.evex (.op .permi2 8 512 5 2 (.xmm 3) 0 1 true), 6) := by decide
-- VPCMPEQB k2{k1}, zmm1, zmm0; VMOVDQU8 zmm0{k1}{z}, [rsi]
example : decode [0x62, 0xf1, 0x75, 0x49, 0x74, 0xd0] =
    some (.evex (.cmp (.int false 0) 8 512 2 1 (.xmm 0) 0 1), 6) := by decide
example : decode [0x62, 0xf1, 0x7f, 0xc9, 0x6f, 0x06] =
    some (.evex (.mov 8 512 false (.xmm 0) (.mem ⟨some 6, none, 0, 0, false, false⟩) 1 true), 6) := by decide
-- compressed displacements: disp8 × 4 with {1to16}, disp8 × 64 without
example : decode [0x62, 0xf1, 0x75, 0x58, 0xfe, 0x50, 0x10] =
    some (.evex (.op (.pint (.add 32)) 32 512 2 1 (.mem ⟨some 0, none, 0, 64, false, false⟩) 32 0 false), 7) := by
  decide
example : decode [0x62, 0x61, 0x75, 0x47, 0xfe, 0x70, 0x02] =
    some (.evex (.op (.pint (.add 32)) 32 512 30 17 (.mem ⟨some 0, none, 0, 128, false, false⟩) 0 7 false), 7) := by
  decide
-- registers 16..31: VPADDD zmm25, zmm30, zmm17
example : decode [0x62, 0x21, 0x0d, 0x40, 0xfe, 0xc9] =
    some (.evex (.op (.pint (.add 32)) 32 512 25 30 (.xmm 17) 0 0 false), 6) := by decide
-- the Go std encodings
example : decode [0x62, 0xf1, 0xfd, 0x48, 0x6f, 0x0e] =
    some (.evex (.mov 64 512 true (.xmm 1) (.mem ⟨some 6, none, 0, 0, false, false⟩) 0 false), 6) := by decide
example : decode [0x62, 0xf2, 0x7d, 0x48, 0x54, 0xd9] = some (.evex (.op .popcnt 8 512 3 0 (.xmm 1) 0 0 false), 6) := by
  decide
example : decode [0x62, 0xf2, 0xfd, 0x49, 0x8b, 0xc9] = some (.evex (.compress 64 512 (.xmm 1) 1 1 false), 6) := by
  decide
example : decode [0x62, 0xf3, 0x75, 0x48, 0x44, 0xc8, 0x00] =
    some (.evex (.op (.clmul 0) 64 512 1 1 (.xmm 0) 0 0 false), 7) := by decide
example : decode [0x62, 0xf3, 0x7d, 0x48, 0x19, 0xca, 0x01] = some (.evex (.extract 32 512 128 (.xmm 2) 1 1 0 false), 7) := by
  decide
example : decode [0x62, 0xf3, 0x85, 0x48, 0x1e, 0xc9, 0x04] =
    some (.evex (.cmp (.int false 4) 64 512 1 15 (.xmm 1) 0 0), 7) := by decide
example : decode [0x62, 0xd3, 0x55, 0x48, 0x25, 0xcb, 0x96] =
    some (.evex (.op (.ternlog 0x96) 32 512 1 5 (.xmm 11) 0 0 false), 7) := by decide
example : decode [0x62, 0xf3, 0xd5, 0x48, 0xce, 0xdb, 0x00] =
    some (.evex (.op (.gfaffine false 0) 8 512 3 5 (.xmm 3) 0 0 false), 7) := by decide
-- VMOVDQU64 Z16, 1024(AX) (asyncPreempt): disp8 0x10 × 64
example : decode [0x62, 0xe1, 0xfe, 0x48, 0x7f, 0x40, 0x10] =
    some (.evex (.mov 64 512 false (.mem ⟨some 0, none, 0, 1024, false, false⟩) (.xmm 16) 0 false), 7) := by decide
-- opmask instructions (VEX)
example : decode [0xc4, 0xe1, 0xfb, 0x92, 0xc8] = some (.evex (.kmov 64 (.k 1) (.gpr 0)), 5) := by decide
example : decode [0xc5, 0x78, 0x93, 0xf9] = some (.evex (.kmov 16 (.gpr 15) (.k 1)), 4) := by decide
example : decode [0xc5, 0xf9, 0x92, 0xc9] = some (.evex (.kmov 8 (.k 1) (.gpr 1)), 4) := by decide
example : decode [0xc4, 0xe1, 0xf8, 0x91, 0x80, 0x00, 0x08, 0x00, 0x00] =
    some (.evex (.kmov 64 (.mem ⟨some 0, none, 0, 2048, false, false⟩) (.k 0)), 9) := by decide
example : decode [0xc5, 0xec, 0x41, 0xd9] = some (.evex (.klogic .and 16 3 2 1), 4) := by decide
example : decode [0xc5, 0xec, 0x46, 0xd9] = some (.evex (.klogic .xnor 16 3 2 1), 4) := by decide
example : decode [0xc4, 0xe1, 0xed, 0x4a, 0xd9] = some (.evex (.klogic .add 32 3 2 1), 5) := by decide
example : decode [0xc4, 0xe1, 0xf8, 0x44, 0xd1] = some (.evex (.knot 64 2 1), 5) := by decide
example : decode [0xc4, 0xe3, 0xf9, 0x33, 0xd1, 0x03] = some (.evex (.kshift true 64 2 1 3), 6) := by decide
example : decode [0xc4, 0xe3, 0xf9, 0x30, 0xd1, 0x05] = some (.evex (.kshift false 16 2 1 5), 6) := by decide
example : decode [0xc4, 0xe1, 0xf8, 0x98, 0xd1] = some (.evex (.kortest 64 2 1), 5) := by decide
example : decode [0xc5, 0xf9, 0x99, 0xd1] = some (.evex (.ktest 8 2 1), 4) := by decide
example : decode [0xc5, 0xed, 0x4b, 0xd9] = some (.evex (.kunpck 8 3 2 1), 4) := by decide
-- VEX VPCLMULQDQ ymm, VGF2P8AFFINEQB xmm
example : decode [0xc4, 0xe3, 0x6d, 0x44, 0xd9, 0x11] = some (.evex (.op (.clmul 0x11) 64 256 3 2 (.xmm 1) 0 0 false), 6) := by
  decide
example : decode [0xc4, 0xe3, 0xe9, 0xce, 0xd9, 0x01] =
    some (.evex (.op (.gfaffine false 1) 8 128 3 2 (.xmm 1) 0 0 false), 6) := by decide
-- more forms
example : decode [0x62, 0xf2, 0xfd, 0x48, 0x7c, 0xc8] = some (.evex (.bcastG 64 512 1 0 0 false), 6) := by decide
example : decode [0x62, 0xf3, 0x7d, 0x48, 0x3b, 0xcb, 0x01] = some (.evex (.extract 32 512 256 (.xmm 3) 1 1 0 false), 7) := by
  decide
example : decode [0x62, 0xf3, 0xed, 0x48, 0x38, 0xd9, 0x03] = some (.evex (.insert 64 512 128 3 2 (.xmm 1) 3 0 false), 7) := by
  decide
example : decode [0x62, 0xf2, 0x7d, 0xc9, 0x89, 0x18] =
    some (.evex (.expand 32 512 3 (.mem ⟨some 0, none, 0, 0, false, false⟩) 1 true), 6) := by decide
example : decode [0x62, 0xf1, 0xfd, 0x58, 0x51, 0xd9] = some (.evex (.fp .sqrt 64 512 3 0 (.xmm 1) 0 3 0 false), 6) := by
  decide
example : decode [0x62, 0xf1, 0xe5, 0x58, 0x73, 0x50, 0x08, 0x03] =
    some (.evex (.uop (.shift .srl) 64 512 3 (.mem ⟨some 0, none, 0, 64, false, false⟩) 64 3 0 false), 8) := by decide
example : decode [0x62, 0xf2, 0x6e, 0x49, 0x27, 0xd9] = some (.evex (.cmp (.test true) 32 512 3 2 (.xmm 1) 0 1), 6) := by
  decide
-- rejected: {z} without a mask, L'L = 11, EVEX.b on a register integer form, W0 VGF2P8AFFINEQB
example : decode [0x62, 0xf1, 0x6d, 0xc8, 0xfe, 0xd9] = none := by decide
example : decode [0x62, 0xf1, 0x6d, 0x68, 0xfe, 0xd9] = none := by decide
example : decode [0x62, 0xf1, 0x6d, 0x58, 0xfe, 0xd9] = none := by decide
example : decode [0x62, 0xf3, 0x55, 0x48, 0xce, 0xdb, 0x00] = none := by decide

/-! ## Semantics -/

/-- `ZMMn` set to `v n` (and `K1 = 0x5555`, `K2 = 0xF0`). -/
def mk (v : Nat → Nat) : State :=
  { regs := fun _ => 0, rip := 0, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun i => BitVec.ofNat 128 (v i), ymmHi := fun i => BitVec.ofNat 128 (v i / 2 ^ 128),
    zmmHi := fun i => BitVec.ofNat 256 (v i / 2 ^ 256),
    kreg := fun i => if i = 1 then 0x5555 else if i = 2 then 0xF0 else 0, mem := default }

/-- `ZMM1 = [0, 1, …, 15]`, `ZMM2 = [100, …]`, `ZMM3 = [7, …]` (dwords); `ZMM17`, `ZMM30` too. -/
def s0 : State := mk fun i =>
  if i = 1 ∨ i = 17 then ofElems 32 16 (fun j => j) else if i = 2 ∨ i = 30 then ofElems 32 16 (fun _ => 100)
  else if i = 3 then ofElems 32 16 (fun _ => 7) else 0

def zmmAfter (bs : List Nat) (s : State) (n : Nat) : Option Nat := (step bs s).toOption.map (·.zmm n)

-- VPADDD zmm3, zmm2, zmm1
example : zmmAfter [0x62, 0xf1, 0x6d, 0x48, 0xfe, 0xd9] s0 3 = some (ofElems 32 16 fun j => j + 100) := by decide +kernel
-- merging-masking {k1}: the odd dwords keep 7
example : zmmAfter [0x62, 0xf1, 0x6d, 0x49, 0xfe, 0xd9] s0 3 =
    some (ofElems 32 16 fun j => if j % 2 = 0 then j + 100 else 7) := by decide +kernel
-- zeroing-masking {k1}{z}
example : zmmAfter [0x62, 0xf1, 0x6d, 0xc9, 0xfe, 0xd9] s0 3 =
    some (ofElems 32 16 fun j => if j % 2 = 0 then j + 100 else 0) := by decide +kernel
-- the high registers: VPADDD zmm25, zmm30, zmm17
example : zmmAfter [0x62, 0x21, 0x0d, 0x40, 0xfe, 0xc9] s0 25 = some (ofElems 32 16 fun j => j + 100) := by decide +kernel
-- the EVEX zero-upper rule on literals: EVEX.128 VPADDD xmm3, xmm2, xmm1 (P2 = 08) zeroes bits 511:128
example : zmmAfter [0x62, 0xf1, 0x6d, 0x08, 0xfe, 0xd9] s0 3 = some (ofElems 32 4 fun j => j + 100) := by decide +kernel
-- and so does VEX.128 VPADDD xmm3, xmm2, xmm1 (bits 511:256 included)
example : zmmAfter [0xc5, 0xe9, 0xfe, 0xd9] s0 3 = some (ofElems 32 4 fun j => j + 100) := by decide +kernel
-- VPCOMPRESSQ zmm3{k2}, zmm1 (k2 = 0xF0: qwords 4..7 to 0..3, the rest of zmm3 kept)
example : zmmAfter [0x62, 0xf2, 0xfd, 0x4a, 0x8b, 0xcb] s0 3 =
    some (ofElems 64 8 fun j => if j < 4 then elem (ofElems 32 16 fun j => j) 64 (j + 4) else elem (ofElems 32 16 fun _ => 7) 64 j) := by
  decide +kernel
-- VPTERNLOGQ 0x96 is a three-way XOR
example : zmmAfter [0x62, 0xf3, 0xed, 0x48, 0x25, 0xd9, 0x96] s0 3 =
    some ((ofElems 32 16 fun _ => 7) ^^^ (ofElems 32 16 fun _ => 100) ^^^ (ofElems 32 16 fun j => j)) := by decide +kernel
-- VPERMB zmm3, zmm2, zmm1: the index bytes of zmm2 are 100 (mod 64 = 36: byte 36 of zmm1 = 9) and 0 (byte 0 = 0)
example : zmmAfter [0x62, 0xf2, 0x6d, 0x48, 0x8d, 0xd9] s0 3 = some (ofElems 32 16 fun _ => 9) := by decide +kernel

-- GF(2⁸): the AES inverse of 0x53 is 0xCA; the identity matrix is the identity
example : gfInv 0x53 = 0xCA := by decide +kernel
example : gfMul 0x53 0xCA = 1 := by decide +kernel
example : gfAffine 0x0102040810204080 0xA7 0 = 0xA7 := by decide +kernel
-- carry-less: (x + 1)² = x² + 1
example : clmulN 64 3 3 = 5 := by decide +kernel

-- KMOVQ k1, rax with RAX = 0, then KORTESTQ k1, k1: ZF = 1, CF = 0
example : ((step [0xc4, 0xe1, 0xfb, 0x92, 0xc8] s0).toOption.bind fun s =>
    ((step [0xc4, 0xe1, 0xf8, 0x98, 0xc9] { s with rip := 0 }).toOption.map fun t => (t.flags.zf, t.flags.cf))) =
    some (some true, some false) := by decide +kernel

/-! ## The rules for every state -/

/-- After an EVEX.128 `VPADDD xmm3, xmm2, xmm1`, bits 511:128 of `ZMM3` are zero
(`Janus.Amd64.Tactic.exec_evex_zero_upper`, instantiated). -/
example (s s' : State) (h : step [0x62, 0xf1, 0x6d, 0x08, 0xfe, 0xd9] s = .ok s') :
    s'.zmmHi 3 = 0 ∧ s'.ymmHi 3 = 0 := by
  rw [step_of_decode (i := .evex (.op (.pint (.add 32)) 32 128 3 2 (.xmm 1) 0 0 false)) (len := 6) (by decide)] at h
  have := Janus.Amd64.Tactic.exec_evex_zero_upper _ _ s s' h 3 128 (by simp [EvexI.vdsts]) (by decide)
  exact ⟨this.1, this.2 rfl⟩

/-- After a VEX.256 `VPADDD ymm0, ymm1, ymm2`, bits 511:256 of `ZMM0` are zero
(`Janus.Amd64.Tactic.exec_avx_zero_zmm`). -/
example (s s' : State) (h : step [0xc5, 0xf5, 0xfe, 0xc2] s = .ok s') : s'.zmmHi 0 = 0 := by
  rw [step_of_decode (i := .avx (.pint (.add 32) 256 0 1 (.xmm 2))) (len := 4) (by decide)] at h
  exact Janus.Amd64.Tactic.exec_avx_zero_zmm _ _ s s' h 0 256 (by simp [AvxI.vdsts])

/-- A legacy-SSE `PADDD` keeps the AVX-512 state (`Janus.Amd64.Tactic.exec_sse_preserves_avx512`). -/
example (s s' : State) (h : step [0x66, 0x0f, 0xfe, 0xc3] s = .ok s') : s'.zmmHi = s.zmmHi ∧ s'.kreg = s.kreg := by
  rw [step_of_decode (i := .sse (.pint (.add 32) 0 (.xmm 3))) (len := 4) (by decide)] at h
  exact Janus.Amd64.Tactic.exec_sse_preserves_avx512 _ _ s s' h

end JanusTests.AVX512
