import Janus
import Extracted

/-! `internal/runtime/gc/scan.expandAVX512_2` on amd64: one of the 29 AVX-512 kernels the garbage
collector's span scanner (`scanSpanPackedAVX512`) calls through `gcExpandersAVX512` to expand the
grey-object bitmap of a span into a grey-word bitmap. For size class 2 (16-byte objects, two
words each) the 512-bit packed bitmap at `[AX]` (one bit per object) becomes the 1024-bit word
bitmap in `Z1` (low half) and `Z2` (high half): every bit twice.

```
VMOVDQU64 expandAVX512_2_inShuf0<>(SB), Z0      // byte indices
VMOVDQU64 expandAVX512_2_mat0<>(SB), Z1         // two 8x8 bit matrices
VMOVDQU64 expandAVX512_2_inShuf1<>(SB), Z2
VMOVDQU64 expandAVX512_2_outShufLo(SB), Z3
VMOVDQU64 (AX), Z4
VPERMB Z4, Z0, Z0 ; VGF2P8AFFINEQB $0, Z1, Z0, Z0    // bytes 0..31, each nibble's bits doubled
VPERMB Z4, Z2, Z2 ; VGF2P8AFFINEQB $0, Z1, Z2, Z2    // bytes 32..63
VPERMB Z0, Z3, Z1 ; VPERMB Z2, Z3, Z2                // interleave the halves
RET
```

The function is static Go assembly with its own convention (input in `AX`, results in `Z1` and
`Z2`, no Go ABI), so the theorem is a `Summary`: from the entry, the run reaches the return
address on the stack with the expanded bitmap in `Z1`/`Z2`.

**Guarantee.** For every state at the entry whose memory holds the kernel's read-only tables
(`DataLoaded`), in which the 64 bytes at `AX` and the return-address slot are readable and the
return address is a user address, the call returns with `Expanded`: bit `j` of `Z1` is bit `j/2`
of the input and bit `j` of `Z2` is bit `256 + j/2`, for every `j < 512`.

**How.** `janus64_run` executes the nine EVEX instructions; each byte `q` of the result is the
GF(2) affine transformation (`VGF2P8AFFINEQB`) of an input byte chosen by the two `VPERMB` index
tables, by a matrix chosen by the `VPERMB` index. `expand_tables` reduces the result to two facts
about the extracted tables (the input byte is `base + q/2`, the matrix doubles the low nibble for
even `q` and the high one for odd `q`), decided by the kernel on the bytes of the binary, and to
`affine_dup`, the bit behaviour of the two matrices on all 256 byte values (also decided). The
proof names no address: the tables come from `DataLoaded`, the entry is `Extracted.entry`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.Tactic Janus.Tactic
open Janus.Arm64 (elem ofElems)

set_option exponentiation.threshold 600

/-- The size-class-2 expansion: bit `j` of the low (`lo`) and high (`hi`) halves of the
1024-bit result is bit `j/2`, resp. `256 + j/2`, of the 512-bit packed bitmap `x`. -/
def Expanded (x lo hi : Nat) : Prop :=
  ∀ j < 512, elem lo 1 j = elem x 1 (j / 2) ∧ elem hi 1 j = elem x 1 (256 + j / 2)

/-- The two bit matrices of `expandAVX512_2_mat0`: the low nibble, the high nibble, each bit
twice. -/
def dupLo : Nat := 0x0101020204040808
def dupHi : Nat := 0x1010202040408080

/-- `VGF2P8AFFINEQB` with the two matrices: output bit `r` is input bit `4h + r/2`. -/
theorem affine_dup : ∀ h < 2, ∀ b < 256, ∀ r < 8,
    elem (ExecEVEX.gfAffine (if h = 0 then dupLo else dupHi) b 0) 1 r = elem b 1 (4 * h + r / 2) := by
  decide +kernel

theorem elem_bit_byte (x m t : Nat) (ht : t < 8) : elem (elem x 8 m) 1 t = elem x 1 (8 * m + t) := by
  have := elem_lane (x := x) (e := 1) (k := 8) (j := m) ht
  simpa using this

/-- The functional core: a 512-bit value built byte by byte as `gfAffine (matrix q) (input byte
(base + q / 2))`, with the matrix of byte `q` the low-nibble one for even `q`. -/
theorem expand_bytes (X : Nat) (f : Nat → Nat) (base : Nat)
    (hf : ∀ q < 64, f q = ExecEVEX.gfAffine (if q % 2 = 0 then dupLo else dupHi) (elem X 8 (base + q / 2)) 0 % 256) :
    ∀ j < 512, elem (ofElems 8 64 f) 1 j = elem X 1 (8 * base + j / 2) := by
  intro j hj
  have hq : j / 8 < 64 := by omega
  rw [show j = 8 * (j / 8) + j % 8 by omega, ← elem_bit_byte _ _ _ (by omega), elem_ofElems _ hq, hf _ hq,
    Nat.mod_mod]
  have hb := elem_lt X 8 (base + j / 8 / 2)
  rw [Nat.mod_eq_of_lt (by
    have := ExecEVEX.gfAffine (if j / 8 % 2 = 0 then dupLo else dupHi) (elem X 8 (base + j / 8 / 2)) 0
    unfold ExecEVEX.gfAffine; exact Nat.lt_of_lt_of_le (ofElems_lt 1 8 _) (by decide))]
  have := affine_dup (j / 8 % 2) (by omega) _ hb (j % 8) (by omega)
  have h2 : (if j / 8 % 2 = 0 then dupLo else dupHi) = (if j / 8 % 2 = 0 then dupLo else dupHi) := rfl
  rw [this, elem_bit_byte _ _ _ (by omega)]
  congr 1; omega

/-- `expand_bytes` for the shape `janus64_run` leaves: the input byte offset and the matrix of
output byte `q` come from the kernel's tables `IN`, `OUT` (`VPERMB` indices) and `MAT`. -/
theorem expand_tables (m : Janus.Arm64.Memory) (p MAT OUT IN base : Nat)
    (hIN : ∀ q < 64, elem IN 8 (elem OUT 8 q % 64) % 64 = base + q / 2)
    (hMAT : ∀ q < 64, elem MAT 64 (elem OUT 8 q % 64 / 8) = if q % 2 = 0 then dupLo else dupHi) (hb : base + 32 ≤ 64) :
    ∀ j < 512, elem (ofElems 8 64 fun i => ExecEVEX.gfAffine (elem MAT 64 (elem OUT 8 i % 64 / 8))
        (m.readLE (p + elem IN 8 (elem OUT 8 i % 64) % 64) 1) 0 % 256) 1 j =
      elem (m.readLE p 64) 1 (8 * base + j / 2) := by
  apply expand_bytes
  intro q hq
  rw [hIN q hq, hMAT q hq, show (64 : Nat) = 8 * 8 by rfl, elem_readLE m (k := 1) (by omega), Nat.one_mul]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem correctness : Summary Extracted.program Extracted.entry
    (fun s => Extracted.program.DataLoaded s.mem ∧ s.mem.accessible (s.regs 0).toNat 64 false = true ∧
      s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (fun s s' => Expanded (s.mem.readLE (s.regs 0).toNat 64) (s'.zmm 1) (s'.zmm 2)) := by
  intro s hpc ⟨hd, hacc, hsp, hra⟩
  janus64_data hd
  janus64_run
  simp only [Expanded, State.zmm, State.ymm, setXmmF_apply, setZmmF_apply, reduceIte, Nat.reduceEqDiff,
    ymmJoin_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMul, zmm_join, ofElems_mod_of_le, Nat.reduceLeDiff]
  intro j hj
  constructor
  · refine (expand_tables s.mem (s.regs 0).toNat _ _ _ 0 ?_ ?_ (by decide) j hj).trans (by congr 1 <;> omega)
    · decide +kernel
    · decide +kernel
  · refine (expand_tables s.mem (s.regs 0).toNat _ _ _ 32 ?_ ?_ (by decide) j hj).trans (by congr 1 <;> omega)
    · decide +kernel
    · decide +kernel

end Proof
