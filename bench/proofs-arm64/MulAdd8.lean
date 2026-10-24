import Extracted

/-!
# Benchmark `MulAdd8(z, x *[8]uint64, y, c uint64) uint64` on arm64

`z + x·y + c = z' + 2^512·carry` over 8 little-endian limbs, fully unrolled (92 instructions:
8 `MUL`/`UMULH` pairs, 16 loads, 8 stores, carry chains through `ADDS`/`ADC`), for disjoint
`z` and `x`. After the run, `janus_arith` closes the carry arithmetic by reflection
(`janus_carry`): no product is named and no bound stated by hand.
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

set_option maxHeartbeats 4000000 in
theorem correctness (z x y c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, c]
      (fun s => Ptr s.mem z 64 true ∧ Ptr s.mem x 64 false ∧ Disjoint z.toNat 64 x.toNat 64)
      (fun s s' => s'.mem.readLE z.toNat 64 + 2 ^ 512 * (s'.regs 0).toNat =
        s.mem.readLE z.toNat 64 + y.toNat * s.mem.readLE x.toNat 64 + c.toNat) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, hd⟩
  janus_intro hs
  simp only [Disjoint] at hd
  simp only [readLE_64]
  janus_run
  janus_arith

end Proof
