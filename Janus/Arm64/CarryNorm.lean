import Lean
import Janus.Arm64.Exec

/-!
# arm64 carry chains in the vocabulary of `janus_carry` (`adds`/`adcs`/`subs`/`sbcs`/`ngc`)

`janus_run` on arm64 multi-limb arithmetic leaves `addWithCarry` limbs, carry flags as `decide (2^64 ≤ A)` and
borrows as `decide (b ≤ a)`, `ngc` masks and negated flag tests. These lemmas (from FV-G's `UtilAM`, now the library's)
put them in the floors-and-remainders vocabulary `janus_carry`/`janus_carry_nf` normalise (`janus_carry_simp_b` applies
them; the side conditions are closed by `janus_carry_disch_b`: `janus_carry_disch`, then `omega` on the bound facts only).
Every lemma is an ordinary kernel-checked theorem; none is in a default simp set.
-/

namespace Janus.Arm64

theorem addWithCarry_fst_toNat (a b : BitVec 64) (c : Bool) :
    (addWithCarry a b c).1.toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64 := by
  simp only [addWithCarry, BitVec.toNat_ofNat]

theorem addWithCarry_c64 (a b : BitVec 64) (c : Bool) :
    (addWithCarry a b c).2.c = decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) := by
  simp only [addWithCarry, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat
  · have : (a.toNat + b.toNat + c.toNat) % 2 ^ 64 ≠ a.toNat + b.toNat + c.toNat := by
      intro he; have := Nat.mod_lt (a.toNat + b.toNat + c.toNat) (Nat.two_pow_pos 64); omega
    simp [this, h]
  · rw [Nat.mod_eq_of_lt (by omega)]; simp [h]

/-- A subtraction borrow flag (`subs`/`sbcs` carry: no borrow) as a floor. -/
theorem dec_le_div (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (decide (b ≤ a)).toNat = (a + 18446744073709551616 - b) / 18446744073709551616 := by
  by_cases h : b ≤ a
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

/-- An addition carry flag as a floor. -/
theorem dec_add_div (A : Nat) (h : A < 2 * 18446744073709551616) :
    (decide (18446744073709551616 ≤ A)).toNat = A / 18446744073709551616 := by
  by_cases hc : 18446744073709551616 ≤ A
  · simp only [hc, decide_true, Bool.toNat_true]; omega
  · simp only [hc, decide_false, Bool.toNat_false]; omega

/-- `ngc`/`neg` of a flag `c ≤ 1`: a borrow turned into a mask. -/
theorem ngc_flag (c : Nat) (hc : c ≤ 1) :
    (18446744073709551616 - (0 % 18446744073709551616 + 18446744073709551615 % 18446744073709551616 + c) %
      18446744073709551616) % 18446744073709551616 = 1 - c := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h <;> subst h <;> decide

theorem flag_mod (c : Nat) (hc : c ≤ 1) :
    (0 % 18446744073709551616 + 0 % 18446744073709551616 + c) % 18446744073709551616 = c := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h <;> subst h <;> decide

/-- An `sbcs` limb with carry-in `q = 1 - borrow` in the form `janus_carry` reads. -/
theorem sbc_num (a b q : Nat) (hb : b < 18446744073709551616) (hq : q ≤ 1) :
    a + (18446744073709551616 - 1 - b) + q = a + (18446744073709551616 - b - (1 - q)) := by omega

/-- A negated flag test as an equation, for `c ≤ 1` (no case split for `omega`). -/
theorem not_sub_flag (c : Nat) (hc : c ≤ 1) : (¬ (1 - c = 0)) = (c = 0) := propext (by omega)

theorem not_flag (c : Nat) (hc : c ≤ 1) : (¬ (c = 0)) = (c = 1) := propext (by omega)

end Janus.Arm64
