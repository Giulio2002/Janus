import Janus.Arm64.Decode
import JanusASL.Proofs.JanusDecode

/-! # Janus' decoder on the scalar floating-point words

`decode w = decodeFloat w` for every word whose top byte is `0x1E` or `0x1F` (`M 0 S 1111x` with
`M = S = 0`), except the conversions between floating point and integers (`0x1E`, bit 21 set,
bits 15:10 clear): every other test of `decodeSimdDP` and of `decodeCrypto` fails on the top byte. -/

namespace JanusASL.Proofs
open Janus.Arm64

theorem and_top_byte {w m v : Nat} (h : w &&& m = v) : (w / 2 ^ 24) &&& (m / 2 ^ 24) = v / 2 ^ 24 := by
  rw [← h, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_and_distrib]

theorem top_ne {w m v : Nat} (htop : w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x1F)
    (h1 : 0x1E &&& (m / 2 ^ 24) ≠ v / 2 ^ 24) (h2 : 0x1F &&& (m / 2 ^ 24) ≠ v / 2 ^ 24) : (w &&& m = v) = False := by
  apply propext; constructor
  · intro h; have := and_top_byte h; rcases htop with e | e <;> rw [e] at this
    · exact h1 this
    · exact h2 this
  · intro h; exact h.elim

theorem decodeCrypto_float {w : Nat} (htop : w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x1F) : decodeCrypto w = none := by
  unfold decodeCrypto
  have hw : ¬ w ≥ 2 ^ 32 := by omega
  simp (config := { decide := true }) only [hw, ite_false, top_ne htop]

theorem bit_of_and {w m v : Nat} (h : w &&& m = v) {i : Nat} (hm : m.testBit i = true) :
    w.testBit i = v.testBit i := by
  rw [← h, Nat.testBit_and, hm, Bool.and_true]

theorem conv_mask {w : Nat} (h : w &&& 0x7F20FC00 = 0x1E200000) :
    (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 10) % 64 = 0 := by
  have b : ∀ i, (0x7F20FC00 : Nat).testBit i = true → w.testBit i = (0x1E200000 : Nat).testBit i :=
    fun i hm => bit_of_and h hm
  have t21 := b 21 (by decide)
  have t10 := b 10 (by decide); have t11 := b 11 (by decide); have t12 := b 12 (by decide)
  have t13 := b 13 (by decide); have t14 := b 14 (by decide); have t15 := b 15 (by decide)
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow] at t21 t10 t11 t12 t13 t14 t15
  have e : ∀ k, (1 &&& w / 2 ^ k) = w / 2 ^ k % 2 := fun k => by rw [Nat.and_comm, Nat.and_one_is_mod]
  simp only [e] at t21 t10 t11 t12 t13 t14 t15
  simp (config := { decide := true }) at t21 t10 t11 t12 t13 t14 t15
  constructor
  · omega
  · omega

theorem decode_float {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x1F)
    (hconv : ¬ (w / 2 ^ 24 = 0x1E ∧ (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 10) % 64 = 0)) :
    decode w = decodeFloat w := by
  have hc : (w &&& 0x7F20FC00 = 0x1E200000) = False := by
    apply propext; constructor
    · intro h
      rcases htop with e | e
      · exact hconv ⟨e, conv_mask h⟩
      · have := and_top_byte h; rw [e] at this; exact absurd this (by decide)
    · intro h; exact h.elim
  have hop : bits w 28 25 = 15 := by simp only [bits_def]; omega
  have hw' : ¬ w ≥ 2 ^ 32 := by omega
  unfold decode
  simp only [hw', ite_false, hop]
  simp (config := { decide := true }) only [decodeSimdDP, top_ne htop, hc, ite_false, ite_true,
    decodeCrypto_float htop]

theorem testBit_top {w : Nat} {a : Nat} (htop : w / 2 ^ 24 = a) {i : Nat} (hi : 24 ≤ i) :
    w.testBit i = a.testBit (i - 24) := by
  rw [← htop, Nat.testBit_div_two_pow]; congr 1; omega

theorem testBit_of_mod {w : Nat} {k b : Nat} (h : (w / 2 ^ k) % 2 = b) : w.testBit k = decide (b = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  simp only [Nat.one_and_eq_mod_two, h]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b ≥ 2) with rfl | rfl | hb
  · decide
  · decide
  · have := Nat.mod_lt (w / 2 ^ k) (show 2 > 0 by decide); omega

theorem mask_FF200000 {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (h21 : (w / 2 ^ 21) % 2 = 1) :
    w &&& 0xFF200000 = 0x1E200000 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  rcases (by omega : i < 21 ∨ i = 21 ∨ (21 < i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ 32 ≤ i) with h | rfl | h | h | h
  · have : ∀ j < 21, (0xFF200000 : Nat).testBit j = false ∧ (0x1E200000 : Nat).testBit j = false := by decide
    rw [(this i h).1, (this i h).2, Bool.and_false]
  · rw [testBit_of_mod h21]; decide
  · have : ∀ j < 24, 21 < j → (0xFF200000 : Nat).testBit j = false ∧ (0x1E200000 : Nat).testBit j = false := by
      decide
    rw [(this i h.2 h.1).1, (this i h.2 h.1).2, Bool.and_false]
  · rw [testBit_top htop h.1]
    have : ∀ j < 32, 24 ≤ j → ((0x1E : Nat).testBit (j - 24) && (0xFF200000 : Nat).testBit j) =
      (0x1E200000 : Nat).testBit j := by decide
    exact this i h.2 h.1
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) h))]
    have : (0x1E200000 : Nat) < 2 ^ i := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) h)
    rw [Nat.testBit_lt_two_pow this, Bool.false_and]

theorem decodeFloat_fpCmp {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 16 = 8) (h14 : (w / 2 ^ 14) % 4 = 0) (h0 : w % 8 = 0)
    (hz : (w / 2 ^ 3) % 2 = 1 → (w / 2 ^ 16) % 32 = 0) :
    decodeFloat w = some (.fpCmp (bits w 23 22) (bits w 20 16) (bits w 4 3) (bits w 9 5)) := by
  have e1 : ¬ bits w 23 22 ≥ 2 := by simp only [bits_def]; omega
  have e2 : (w &&& 0xFF000000 = 0x1F000000) = False := by
    apply propext; constructor
    · intro h; have := and_top_byte h; rw [htop] at this; exact absurd this (by decide)
    · intro h; exact h.elim
  have e3 := mask_FF200000 hw htop h21
  have e4 : bits w 11 10 = 0 := by simp only [bits_def]; omega
  have e5 : bits w 14 10 ≠ 0b10000 := by simp only [bits_def]; omega
  have e6 : bits w 13 10 = 0b1000 := by simp only [bits_def]; omega
  have e7 : bits w 15 14 = 0 := by simp only [bits_def]; omega
  have e8 : bits w 2 0 = 0 := by simp only [bits_def]; omega
  have e9 : (bits w 4 3 % 2 = 1 && bits w 20 16 ≠ 0) = false := by
    simp only [bits_def]
    by_cases h : (w / 2 ^ 3) % 2 = 1
    · have := hz h; simp; omega
    · simp; omega
  unfold decodeFloat
  simp only [e1, if_false, e2, e3, ite_true, e4, e5, e6, e7, e8, e9]
  simp

end JanusASL.Proofs
