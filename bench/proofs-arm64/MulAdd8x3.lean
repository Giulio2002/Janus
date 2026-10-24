import Extracted

/-!
# Benchmark `MulAdd8x3(z0, z1, z2, x *[8]uint64, y0, y1, y2 uint64) (c0, c1, c2 uint64)` on arm64

Three fully unrolled 8-limb multiply-adds, `z_k + x·y_k = z_k' + 2^512·c_k` for `k < 3`: about
270 instructions of straight-line code (24 `MUL`/`UMULH` pairs, 48 loads, 24 stores), with the
three outputs and the input pairwise disjoint. Every load of `x` in rows 1 and 2 is resolved
past the stores of the earlier rows (`omega` on the disjointness facts).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

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

set_option maxHeartbeats 10000000 in
theorem correctness (z0 z1 z2 x y0 y1 y2 : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z0, z1, z2, x, y0, y1, y2]
      (fun s => Ptr s.mem z0 64 true ∧ Ptr s.mem z1 64 true ∧ Ptr s.mem z2 64 true ∧
        Ptr s.mem x 64 false ∧ Disjoint z0.toNat 64 x.toNat 64 ∧ Disjoint z1.toNat 64 x.toNat 64 ∧
        Disjoint z2.toNat 64 x.toNat 64 ∧ Disjoint z0.toNat 64 z1.toNat 64 ∧
        Disjoint z0.toNat 64 z2.toNat 64 ∧ Disjoint z1.toNat 64 z2.toNat 64)
      (fun s s' =>
        s'.mem.readLE z0.toNat 64 + 2 ^ 512 * (s'.regs 0).toNat =
          s.mem.readLE z0.toNat 64 + y0.toNat * s.mem.readLE x.toNat 64 ∧
        s'.mem.readLE z1.toNat 64 + 2 ^ 512 * (s'.regs 1).toNat =
          s.mem.readLE z1.toNat 64 + y1.toNat * s.mem.readLE x.toNat 64 ∧
        s'.mem.readLE z2.toNat 64 + 2 ^ 512 * (s'.regs 2).toNat =
          s.mem.readLE z2.toNat 64 + y2.toNat * s.mem.readLE x.toNat 64) := by
  intro ret hret s hs ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩, ⟨hx, hx'⟩, d0, d1, d2, d01, d02, d12⟩
  janus_intro hs
  simp only [Disjoint] at *
  simp only [readLE_64]
  janus_run
  janus_arith

end Proof
