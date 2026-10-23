import Janus
import Extracted

/-!
# Benchmark `MulAdd8(z, x *[8]uint64, y, c uint64) uint64` on amd64

The amd64 version of `bench/proofs-arm64/MulAdd8.lean` (98 instructions: `MULQ` into
`RDX:RAX`, carries through `ADDQ`/`SBBQ`/`SUBQ`). `z` and `x` must not overlap each other or the
return-address slot.
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

set_option exponentiation.threshold 1024

/-- 64 bytes as 8 little-endian limbs. -/
theorem readLE_64 (m : Memory) (a : Nat) :
    m.readLE a 64 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 + 2 ^ 128 * m.readLE (a + 16) 8 +
      2 ^ 192 * m.readLE (a + 24) 8 + 2 ^ 256 * m.readLE (a + 32) 8 +
      2 ^ 320 * m.readLE (a + 40) 8 + 2 ^ 384 * m.readLE (a + 48) 8 +
      2 ^ 448 * m.readLE (a + 56) 8 := by
  have h := fun b k l => Janus.Arm64.Memory.readLE_add m b k l
  rw [show 64 = 8 + 56 from rfl, h, show 56 = 8 + 48 from rfl, h, show 48 = 8 + 40 from rfl, h,
    show 40 = 8 + 32 from rfl, h, show 32 = 8 + 24 from rfl, h, show 24 = 8 + 16 from rfl, h,
    show 16 = 8 + 8 from rfl, h]
  simp only [Nat.add_assoc, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add]

/-- The carry materialised by `SBBQ R, R` (all ones or zero). -/
theorem ite_allOnes_toNat (P : Prop) [Decidable P] :
    (if P then 18446744073709551615#64 else 0#64).toNat = 18446744073709551615 * (decide P).toNat := by
  by_cases h : P <;> simp [h]

set_option maxHeartbeats 4000000 in
theorem correctness (z x y c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, c]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 64 true ∧ Buffer s x 64 false ∧
        Disjoint z 64 x 64 ∧ Disjoint z 64 (s.regs regSP) 8)
      (fun s s' => s'.mem.readLE z.toNat 64 + 2 ^ 512 * (s'.regs 0).toNat =
        s.mem.readLE z.toNat 64 + y.toNat * s.mem.readLE x.toNat 64 + c.toNat) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hz', hz⟩, ⟨hx', hx⟩, hd, hds⟩ := hpre
  simp only [Disjoint, regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hd hds
  simp only [readLE_64]
  janus64_run
  janus64_simp [ite_allOnes_toNat, Nat.mul_add, Nat.mul_left_comm y.toNat]
  have hb0 : y.toNat * s.mem.readLE x.toNat 8 ≤ 18446744073709551615 * 18446744073709551615 :=
    Nat.mul_le_mul (by have := y.isLt; omega) (by have := Janus.Arm64.Memory.readLE_lt s.mem x.toNat 8; omega)
  generalize y.toNat * s.mem.readLE x.toNat 8 = p0 at *
  have hb1 : y.toNat * s.mem.readLE (x.toNat + 8) 8 ≤ 18446744073709551615 * 18446744073709551615 :=
    Nat.mul_le_mul (by have := y.isLt; omega) (by have := Janus.Arm64.Memory.readLE_lt s.mem (x.toNat + 8) 8; omega)
  generalize y.toNat * s.mem.readLE (x.toNat + 8) 8 = p1 at *
  have hb2 : y.toNat * s.mem.readLE (x.toNat + 16) 8 ≤ 18446744073709551615 * 18446744073709551615 :=
    Nat.mul_le_mul (by have := y.isLt; omega) (by have := Janus.Arm64.Memory.readLE_lt s.mem (x.toNat + 16) 8; omega)
  generalize y.toNat * s.mem.readLE (x.toNat + 16) 8 = p2 at *
  have hb3 : y.toNat * s.mem.readLE (x.toNat + 24) 8 ≤ 18446744073709551615 * 18446744073709551615 :=
    Nat.mul_le_mul (by have := y.isLt; omega) (by have := Janus.Arm64.Memory.readLE_lt s.mem (x.toNat + 24) 8; omega)
  generalize y.toNat * s.mem.readLE (x.toNat + 24) 8 = p3 at *
  have hb4 : y.toNat * s.mem.readLE (x.toNat + 32) 8 ≤ 18446744073709551615 * 18446744073709551615 :=
    Nat.mul_le_mul (by have := y.isLt; omega) (by have := Janus.Arm64.Memory.readLE_lt s.mem (x.toNat + 32) 8; omega)
  generalize y.toNat * s.mem.readLE (x.toNat + 32) 8 = p4 at *
  have hb5 : y.toNat * s.mem.readLE (x.toNat + 40) 8 ≤ 18446744073709551615 * 18446744073709551615 :=
    Nat.mul_le_mul (by have := y.isLt; omega) (by have := Janus.Arm64.Memory.readLE_lt s.mem (x.toNat + 40) 8; omega)
  generalize y.toNat * s.mem.readLE (x.toNat + 40) 8 = p5 at *
  have hb6 : y.toNat * s.mem.readLE (x.toNat + 48) 8 ≤ 18446744073709551615 * 18446744073709551615 :=
    Nat.mul_le_mul (by have := y.isLt; omega) (by have := Janus.Arm64.Memory.readLE_lt s.mem (x.toNat + 48) 8; omega)
  generalize y.toNat * s.mem.readLE (x.toNat + 48) 8 = p6 at *
  have hb7 : y.toNat * s.mem.readLE (x.toNat + 56) 8 ≤ 18446744073709551615 * 18446744073709551615 :=
    Nat.mul_le_mul (by have := y.isLt; omega) (by have := Janus.Arm64.Memory.readLE_lt s.mem (x.toNat + 56) 8; omega)
  generalize y.toNat * s.mem.readLE (x.toNat + 56) 8 = p7 at *
  janus64_arith

end Proof
