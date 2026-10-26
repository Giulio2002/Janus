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


theorem top_ne2 {w m v : Nat} (htop : w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E)
    (h1 : 0x1E &&& (m / 2 ^ 24) ≠ v / 2 ^ 24) (h2 : 0x9E &&& (m / 2 ^ 24) ≠ v / 2 ^ 24) : (w &&& m = v) = False := by
  apply propext; constructor
  · intro h; have := and_top_byte h; rcases htop with e | e <;> rw [e] at this
    · exact h1 this
    · exact h2 this
  · intro h; exact h.elim

theorem testBit_win {w k m v : Nat} (h : (w / 2 ^ k) % 2 ^ m = v) {j : Nat} (hj : j < m) :
    w.testBit (k + j) = v.testBit j := by
  rw [← h, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hj, Nat.add_comm]

theorem mask_conv {w : Nat} (hw : w < 2 ^ 32) (htop : (w / 2 ^ 24) % 128 = 0x1E) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h10 : (w / 2 ^ 10) % 64 = 0) : w &&& 0x7F20FC00 = 0x1E200000 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  rcases (by omega : i < 10 ∨ (10 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 21) ∨ i = 21 ∨ (22 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 31) ∨ 31 ≤ i)
    with h | h | h | rfl | h | h | h
  · have : ∀ j < 10, (0x7F20FC00 : Nat).testBit j = false ∧ (0x1E200000 : Nat).testBit j = false := by decide
    rw [(this i h).1, (this i h).2, Bool.and_false]
  · have e := testBit_win (w := w) (k := 10) (m := 6) (v := 0) (by simpa using h10) (j := i - 10) (by omega)
    rw [show 10 + (i - 10) = i by omega] at e
    rw [e]
    have : ∀ j < 6, ((0 : Nat).testBit j && (0x7F20FC00 : Nat).testBit (10 + j)) = (0x1E200000 : Nat).testBit (10 + j) := by decide
    have := this (i - 10) (by omega)
    rw [show 10 + (i - 10) = i by omega] at this
    exact this
  · have : ∀ j < 21, 16 ≤ j → (0x7F20FC00 : Nat).testBit j = false ∧ (0x1E200000 : Nat).testBit j = false := by decide
    rw [(this i h.2 h.1).1, (this i h.2 h.1).2, Bool.and_false]
  · have e := testBit_win (w := w) (k := 21) (m := 1) (v := 1) (by simpa using h21) (j := 0) (by decide)
    simp only [Nat.add_zero] at e
    rw [e]; decide
  · have : ∀ j < 24, 22 ≤ j → (0x7F20FC00 : Nat).testBit j = false ∧ (0x1E200000 : Nat).testBit j = false := by decide
    rw [(this i h.2 h.1).1, (this i h.2 h.1).2, Bool.and_false]
  · have e := testBit_win (w := w) (k := 24) (m := 7) (v := 0x1E) (by simpa using htop) (j := i - 24) (by omega)
    rw [show 24 + (i - 24) = i by omega] at e
    rw [e]
    have : ∀ j < 7, ((0x1E : Nat).testBit j && (0x7F20FC00 : Nat).testBit (24 + j)) = (0x1E200000 : Nat).testBit (24 + j) := by decide
    have := this (i - 24) (by omega)
    rw [show 24 + (i - 24) = i by omega] at this
    exact this
  · rcases (by omega : i < 32 ∨ 32 ≤ i) with h2 | h2
    · have : (0x7F20FC00 : Nat).testBit 31 = false ∧ (0x1E200000 : Nat).testBit 31 = false := by decide
      have hi : i = 31 := by omega
      subst hi
      rw [this.1, this.2, Bool.and_false]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) h2))]
      have : (0x1E200000 : Nat) < 2 ^ i := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) h2)
      rw [Nat.testBit_lt_two_pow this, Bool.false_and]

theorem decode_conv {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 64 = 0) (hop6 : (w / 2 ^ 16) % 8 ≠ 6)
    (hop7 : (w / 2 ^ 16) % 8 ≠ 7) : decode w = decodeFpCvtInt w := by
  have hc : (w &&& 0x7F20FC00 = 0x1E200000) = True := by
    apply propext; constructor
    · intro _; trivial
    · intro _; exact mask_conv hw (by omega) h21 h10
  have hop : bits w 28 25 = 15 := by simp only [bits_def]; omega
  have hw' : ¬ w ≥ 2 ^ 32 := by omega
  have ho : bits w 18 16 ≠ 6 ∧ bits w 18 16 ≠ 7 := by simp only [bits_def]; omega
  unfold decode
  simp only [hw', ite_false, hop]
  simp (config := { decide := true }) only [decodeSimdDP, top_ne2 htop, hc, ite_true]
  simp [ho.1, ho.2]


theorem decodeFpCvtInt_itof {w : Nat} (hft : (w / 2 ^ 22) % 4 < 2) (hop : (w / 2 ^ 16) % 8 = 2 ∨ (w / 2 ^ 16) % 8 = 3)
    (hrm : (w / 2 ^ 19) % 4 = 0) :
    decodeFpCvtInt w = some (.fpCvtInt (bit w 31) (bits w 23 22) (bits w 20 19) (bits w 18 16) (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ bits w 23 22 ≥ 2 := by simp only [bits_def]; omega
  have e2 : bits w 18 16 = 2 ∨ bits w 18 16 = 3 := by simp only [bits_def]; omega
  have e3 : bits w 20 19 = 0 := by simp only [bits_def]; omega
  unfold decodeFpCvtInt
  rcases e2 with e | e <;> simp [e1, e, e3]


theorem decodeFpCvtInt_ftoi {w : Nat} (hft : (w / 2 ^ 22) % 4 < 2) (hop : (w / 2 ^ 16) % 8 = 0 ∨ (w / 2 ^ 16) % 8 = 1) :
    decodeFpCvtInt w = some (.fpCvtInt (bit w 31) (bits w 23 22) (bits w 20 19) (bits w 18 16) (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ bits w 23 22 ≥ 2 := by simp only [bits_def]; omega
  have e2 : bits w 18 16 ≤ 1 := by simp only [bits_def]; omega
  unfold decodeFpCvtInt
  simp [e1, e2]

end JanusASL.Proofs
