import Janus
import Extracted

/-!
# Benchmark `Mul256(z, x, y *[4]uint64)` on amd64: `z = x·y mod 2^256`

The amd64 version of `bench/proofs-arm64/Mul256.lean` (6 `MULQ`, 4 `IMULQ`, carries through
`ADDQ`/`SBBQ`/`SUBQ`, a 48-byte frame with five spill slots). `z` may equal or overlap `x` or
`y`: every limb is loaded before `z` is written. The stack conditions are the ones any Go
heap or caller-frame pointer satisfies: `x` and `y` do not overlap the frame-pointer push
(the only store before the loads), and `z` does not overlap the frame or the return address
(which are read after `z` is written).
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- 32 bytes as 4 little-endian limbs. -/
theorem readLE_32 (m : Memory) (a : Nat) :
    m.readLE a 32 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 +
      2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 := by
  rw [show 32 = 8 + 24 from rfl, Janus.Arm64.Memory.readLE_add, show 24 = 8 + 16 from rfl,
    Janus.Arm64.Memory.readLE_add, show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  simp only [Nat.add_assoc]
  omega

theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => StackWritable s 48 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
        Buffer s y 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 48 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat ≤ y.toNat))
      (fun s s' => valueAt s' z 32 = valueAt s x 32 * valueAt s y 32 % 2 ^ 256) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨hsp, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, hdz, hdx, hdy⟩ := hpre
  simp only [regSP] at hsp hnw hacc hdz hdx hdy
  simp only [valueAt]
  janus64_run [readLE_32, BitVec.toNat_mul]
  janus64_arith

end Proof
