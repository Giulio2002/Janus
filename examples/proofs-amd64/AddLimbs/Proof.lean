import Janus
import Extracted

/-! `example.com/basic.AddLimbs(z, x, y *[4]uint64)` on amd64: the carry loop
`z[i], c = bits.Add64(x[i], y[i], c)` for `i < 4` computes `*z = (*x + *y) mod 2^256`.

The loop has a constant bound, so symbolic execution unrolls it. The carry travels through
`ESI` (`NEGL SI; ADCQ; SBBQ SI, SI; NEGQ SI`). The precondition is that of `Add256`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem carry_toNat (t : Nat) (h : t < 2 * 18446744073709551616) :
    (decide (18446744073709551616 ≤ t)).toNat = t / 18446744073709551616 := by
  by_cases h' : 18446744073709551616 ≤ t
  · simp [h']; omega
  · simp [h']; omega

theorem readLE_32 (m : Memory) (a : Nat) :
    m.readLE a 32 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 +
      2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 := by
  rw [show 32 = 8 + 24 from rfl, Janus.Arm64.Memory.readLE_add, show 24 = 8 + 16 from rfl,
    Janus.Arm64.Memory.readLE_add, show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  simp only [Nat.add_assoc]
  omega

theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
        Buffer s y 32 false ∧ Disjoint z 32 x 32 ∧ Disjoint z 32 y 32 ∧
        Disjoint z 32 (s.regs regSP) 8)
      (fun s s' => valueAt s' z 32 = (valueAt s x 32 + valueAt s y 32) % 2 ^ 256) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, hdx, hdy, hds⟩ := hpre
  simp only [Disjoint, regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hdx hdy hds
  simp only [valueAt]
  janus64_run [readLE_32]
  have b := fun a => Janus.Arm64.Memory.readLE_lt s.mem a 8
  have := b x.toNat; have := b (x.toNat + 8); have := b (x.toNat + 16); have := b (x.toNat + 24)
  have := b y.toNat; have := b (y.toNat + 8); have := b (y.toNat + 16); have := b (y.toNat + 24)
  simp only [Nat.reducePow] at *
  simp (disch := omega) only [carry_toNat]
  omega

end Proof
