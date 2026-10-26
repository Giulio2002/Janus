import JanusASL.Proofs.FP.JanusDecode

/-! # Janus' decoder on the scalar floating-point arithmetic words (2-source, 3-source, FSQRT) -/

namespace JanusASL.Proofs
open Janus.Arm64

theorem decodeFloat_fpDP2 {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 2) (hop : (w / 2 ^ 12) % 16 ≤ 8) :
    decodeFloat w = some (.fpDP2 (bits w 23 22) (bits w 20 16) (bits w 15 12) (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ bits w 23 22 ≥ 2 := by simp only [bits_def]; omega
  have e2 : (w &&& 0xFF000000 = 0x1F000000) = False := by
    apply propext; constructor
    · intro h; have := and_top_byte h; rw [htop] at this; exact absurd this (by decide)
    · intro h; exact h.elim
  have e3 := mask_FF200000 hw htop h21
  have e4 : bits w 11 10 = 2 := by simp only [bits_def]; omega
  have e5 : bits w 15 12 ≤ 8 := by simp only [bits_def]; omega
  unfold decodeFloat
  simp only [e1, ite_false, e2, e3, ite_true, e4, e5]
  simp

theorem mask_FF000000 {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1F) : w &&& 0xFF000000 = 0x1F000000 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  rcases (by omega : i < 24 ∨ (24 ≤ i ∧ i < 32) ∨ 32 ≤ i) with h | h | h
  · have : ∀ j < 24, (0xFF000000 : Nat).testBit j = false ∧ (0x1F000000 : Nat).testBit j = false := by decide
    rw [(this i h).1, (this i h).2, Bool.and_false]
  · rw [testBit_top htop h.1]
    have : ∀ j < 32, 24 ≤ j → ((0x1F : Nat).testBit (j - 24) && (0xFF000000 : Nat).testBit j) =
      (0x1F000000 : Nat).testBit j := by decide
    exact this i h.2 h.1
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) h))]
    have : (0x1F000000 : Nat) < 2 ^ i := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) h)
    rw [Nat.testBit_lt_two_pow this, Bool.false_and]

theorem decodeFloat_fpDP3 {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1F) (hft : (w / 2 ^ 22) % 4 < 2) :
    decodeFloat w = some (.fpDP3 (bits w 23 22) (bit w 21) (bits w 20 16) (bit w 15) (bits w 14 10) (bits w 9 5)
      (bits w 4 0)) := by
  have e1 : ¬ bits w 23 22 ≥ 2 := by simp only [bits_def]; omega
  have e2 := mask_FF000000 hw htop
  unfold decodeFloat
  simp only [e1, ite_false, e2, ite_true]

theorem decodeFloat_fpDP1 {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 32 = 16) (hop : (w / 2 ^ 15) % 64 ≤ 3) :
    decodeFloat w = some (.fpDP1 (bits w 23 22) (bits w 20 15) (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ bits w 23 22 ≥ 2 := by simp only [bits_def]; omega
  have e2 : (w &&& 0xFF000000 = 0x1F000000) = False := by
    apply propext; constructor
    · intro h; have := and_top_byte h; rw [htop] at this; exact absurd this (by decide)
    · intro h; exact h.elim
  have e3 := mask_FF200000 hw htop h21
  have e4 : bits w 11 10 = 0 := by simp only [bits_def]; omega
  have e5 : bits w 14 10 = 0b10000 := by simp only [bits_def]; omega
  have e6 : bits w 20 15 ≤ 3 := by simp only [bits_def]; omega
  unfold decodeFloat
  simp only [e1, ite_false, e2, e3, ite_true, e4, e5, e6]
  simp

end JanusASL.Proofs
