import JanusASL.Proofs.FP.RoundSide
import JanusASL.Proofs.FP.Prim

/-! # The quotient and the round-to-odd quotient lie on the same side of the lattice

`div_side`: the exact quotient `m1*2^e1 / (m2*2^e2)` and Janus' round-to-odd approximation `divOdd` are
`Side`-equivalent on the lattice of multiples of `2^(ex+1)`, where `ex` is the approximation's unit exponent. -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem intCast_two_mul (n : Int) : (n : Rat) * 2 ^ (1 : Int) = ((2 * n : Int) : Rat) := by
  rw [Rat.zpow_one, Rat.intCast_mul]
  have : ((2 : Int) : Rat) = 2 := rfl
  rw [this, Rat.mul_comm]

theorem odd_side (M : Int) (hM : M % 2 = 1) (v : Rat) (h1 : (M : Rat) - 1 < v) (h2 : v < (M : Rat) + 1) :
    Side 1 v (M : Rat) := by
  intro n
  rw [intCast_two_mul]
  have e1 : (M : Rat) - 1 = ((M - 1 : Int) : Rat) := by simp [Rat.intCast_sub]
  have e2 : (M : Rat) + 1 = ((M + 1 : Int) : Rat) := by simp [Rat.intCast_add]
  rw [e1] at h1; rw [e2] at h2
  rcases (by omega : M < 2 * n ∨ 2 * n < M) with h | h
  · have a1 : (M : Rat) < ((2 * n : Int) : Rat) := Rat.intCast_lt_intCast.mpr h
    have a2 : ((M + 1 : Int) : Rat) ≤ ((2 * n : Int) : Rat) := Rat.intCast_le_intCast.mpr (by omega)
    have a3 : v < ((2 * n : Int) : Rat) := rat_lt_of_lt_of_le h2 a2
    refine ⟨⟨fun _ => a1, fun _ => a3⟩, ⟨fun h' => absurd h' (Rat.ne_of_lt a3), fun h' => absurd h' (Rat.ne_of_lt a1)⟩⟩
  · have a1 : ((2 * n : Int) : Rat) < (M : Rat) := Rat.intCast_lt_intCast.mpr h
    have a2 : ((2 * n : Int) : Rat) ≤ ((M - 1 : Int) : Rat) := Rat.intCast_le_intCast.mpr (by omega)
    have a3 : ((2 * n : Int) : Rat) < v := rat_lt_of_le_of_lt a2 h1
    refine ⟨⟨fun h' => absurd h' (Rat.not_lt.mpr (Rat.le_of_lt a3)), fun h' => absurd h' (Rat.not_lt.mpr (Rat.le_of_lt a1))⟩,
      ⟨fun h' => absurd h' (Rat.ne_of_gt a3), fun h' => absurd h' (Rat.ne_of_gt a1)⟩⟩

theorem or_one_eq (N : Nat) : (N ||| 1) = 2 * (N / 2) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rcases j with _ | j
  · simp [Nat.testBit_zero]
  · rw [Nat.testBit_or, Nat.testBit_add_one, Nat.testBit_add_one, Nat.testBit_add_one]
    have h1 : ((1 : Nat) / 2) = 0 := by decide
    have h2 : (2 * (N / 2) + 1) / 2 = N / 2 := by omega
    rw [h1, h2]; simp

theorem div_lt_iff_mul' (X Y P : Rat) (hY : 0 < Y) : X / Y < P ↔ X < P * Y := by
  rw [← Rat.mul_lt_mul_right hY, Rat.div_mul_cancel (Rat.ne_of_gt hY)]

theorem div_eq_iff_mul' (X Y P : Rat) (hY : 0 < Y) : X / Y = P ↔ X = P * Y := by
  constructor
  · intro h; rw [← h, Rat.div_mul_cancel (Rat.ne_of_gt hY)]
  · intro h; rw [h, Rat.mul_div_cancel (Rat.ne_of_gt hY)]

theorem two_pow_nat_int (k : Nat) : ((2 : Rat) ^ k) = (2 : Rat) ^ (k : Int) := (Rat.zpow_natCast 2 k).symm

/-- `m * 2^e` is `num * 2^(e-k)` for `num = m * 2^k`. -/
theorem num_scale (m k : Nat) (e : Int) : (m : Rat) * 2 ^ e = ((m * 2 ^ k : Nat) : Rat) * 2 ^ (e - k) := by
  rw [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat, two_pow_nat_int, Rat.mul_assoc,
    ← Rat.zpow_add two_ne_zero_rat]
  congr 2; omega

/-- The comparison behind `div_side`: `num / m'` (made odd unless exact) against the lattice point `2n'`. -/
theorem div_nat_cmp (num m' n' M : Nat) (hm' : 0 < m')
    (hM : (num % m' = 0 ∧ M = num / m') ∨ (num % m' ≠ 0 ∧ M = 2 * ((num / m') / 2) + 1)) :
    (num < 2 * n' * m' ↔ M < 2 * n') ∧ (num = 2 * n' * m' ↔ M = 2 * n') := by
  have hdm := Nat.div_add_mod num m'
  have hlt := Nat.mod_lt num hm'
  generalize num / m' = N at *
  generalize num % m' = r at *
  rcases hM with ⟨h0, hM⟩ | ⟨h0, hM⟩
  · subst h0; rw [hM]
    have e : num = N * m' := by rw [Nat.mul_comm]; omega
    rw [e]
    exact ⟨Nat.mul_lt_mul_right hm', ⟨fun h => Nat.eq_of_mul_eq_mul_right hm' h, fun h => by rw [h]⟩⟩
  · rw [hM]
    have hr : 0 < r := Nat.pos_of_ne_zero h0
    have l1 : N * m' < num := by rw [Nat.mul_comm]; omega
    have l2 : num < (N + 1) * m' := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · have : N * m' < 2 * n' * m' := Nat.lt_trans l1 h
      have := Nat.lt_of_mul_lt_mul_right this
      omega
    · have h1 : N + 1 ≤ 2 * n' := by omega
      have : (N + 1) * m' ≤ 2 * n' * m' := Nat.mul_le_mul_right m' h1
      omega
    · exfalso
      rw [h] at l1 l2
      have a1 := Nat.lt_of_mul_lt_mul_right l1
      have a2 := Nat.lt_of_mul_lt_mul_right l2
      omega
    · omega

theorem div_cmp_rat (m m' k : Nat) (e e' : Int) (hm' : m' ≠ 0) (n : Int) :
    ((m : Rat) * 2 ^ e / ((m' : Rat) * 2 ^ e') < (n : Rat) * 2 ^ (e - e' - k + 1) ↔
        (((m * 2 ^ k : Nat) : Int) < 2 * n * (m' : Int))) ∧
    ((m : Rat) * 2 ^ e / ((m' : Rat) * 2 ^ e') = (n : Rat) * 2 ^ (e - e' - k + 1) ↔
        (((m * 2 ^ k : Nat) : Int) = 2 * n * (m' : Int))) := by
  have hY : (0 : Rat) < (m' : Rat) * 2 ^ e' := Rat.mul_pos (Rat.natCast_pos.mpr (Nat.pos_of_ne_zero hm')) (rat_pos_zpow _)
  have hZ : (0 : Rat) < 2 ^ (e - k) := rat_pos_zpow _
  have hX : (m : Rat) * 2 ^ e = ((m * 2 ^ k : Nat) : Rat) * 2 ^ (e - k) := num_scale m k e
  have hPY : (n : Rat) * 2 ^ (e - e' - k + 1) * ((m' : Rat) * 2 ^ e') = ((2 * n * (m' : Int) : Int) : Rat) * 2 ^ (e - k) := by
    have h1 : (m' : Rat) = (((m' : Int)) : Rat) := (Rat.intCast_natCast m').symm
    rw [h1, mul_zpow, show (e - e' - k + 1 + e') = (e - k) + 1 by omega, Rat.zpow_add_one two_ne_zero_rat]
    simp only [Rat.intCast_mul]
    have h2 : ((2 : Int) : Rat) = 2 := rfl
    rw [h2]
    generalize (2 : Rat) ^ (e - k) = Z
    generalize (n : Rat) = a
    generalize ((m' : Int) : Rat) = b
    calc a * b * (Z * 2) = 2 * a * b * Z := by
          rw [Rat.mul_comm Z 2, ← Rat.mul_assoc (a * b) 2 Z, Rat.mul_comm (a * b) 2, ← Rat.mul_assoc 2 a b]
      _ = 2 * a * b * Z := rfl
  rw [div_lt_iff_mul' _ _ _ hY, div_eq_iff_mul' _ _ _ hY, hX, hPY, ← Rat.intCast_natCast (m * 2 ^ k)]
  constructor
  · rw [Rat.mul_lt_mul_right hZ]
    exact Rat.intCast_lt_intCast
  · constructor
    · intro h
      have := mul_cancel_pos hZ h
      exact Rat.intCast_inj.mp this
    · intro h
      rw [h]

/-- `N = ⌊m * 2^k / m'⌋ ≥ 2^(fbits+4)` for `k = fbits + 5 + log2 m'`. -/
theorem divN_big (fbits m m' : Nat) (hm : m ≠ 0) (hm' : m' ≠ 0) :
    2 ^ (fbits + 4) ≤ m * 2 ^ (fbits + 5 + Nat.log2 m') / m' := by
  have hm'pos : 0 < m' := Nat.pos_of_ne_zero hm'
  apply (Nat.le_div_iff_mul_le hm'pos).mpr
  have h1 : m' < 2 ^ (Nat.log2 m' + 1) := Nat.lt_log2_self
  have h2 : 1 ≤ m := Nat.pos_of_ne_zero hm
  calc 2 ^ (fbits + 4) * m' ≤ 2 ^ (fbits + 4) * 2 ^ (Nat.log2 m' + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_of_lt h1)
    _ = 2 ^ (fbits + 5 + Nat.log2 m') := by rw [← Nat.pow_add]; congr 1; omega
    _ = 1 * 2 ^ (fbits + 5 + Nat.log2 m') := (Nat.one_mul _).symm
    _ ≤ m * 2 ^ (fbits + 5 + Nat.log2 m') := Nat.mul_le_mul_right _ h2

theorem dy_cmp (M : Nat) (x n : Int) :
    ((M : Rat) * 2 ^ x < (n : Rat) * 2 ^ (x + 1) ↔ (M : Int) < 2 * n) ∧
      ((M : Rat) * 2 ^ x = (n : Rat) * 2 ^ (x + 1) ↔ (M : Int) = 2 * n) := by
  have hp : (0 : Rat) < 2 ^ x := rat_pos_zpow x
  have e : (n : Rat) * 2 ^ (x + 1) = ((2 * n : Int) : Rat) * 2 ^ x := by
    rw [Rat.zpow_add_one two_ne_zero_rat, Rat.intCast_mul]
    have h2 : ((2 : Int) : Rat) = 2 := rfl
    rw [h2, Rat.mul_comm (2 : Rat) (n : Rat), Rat.mul_assoc, Rat.mul_comm (2 ^ x : Rat) 2, ← Rat.mul_assoc]
  rw [e, ← Rat.intCast_natCast M]
  refine ⟨?_, ?_⟩
  · rw [Rat.mul_lt_mul_right hp]; exact Rat.intCast_lt_intCast
  · constructor
    · intro h; exact Rat.intCast_inj.mp (mul_cancel_pos hp h)
    · intro h; rw [h]

theorem div_side (fbits m m' : Nat) (e e' : Int) (hm : m ≠ 0) (hm' : m' ≠ 0) :
    Side ((Janus.Float.divOdd fbits m e m' e').2 + 1) ((m : Rat) * 2 ^ e / ((m' : Rat) * 2 ^ e'))
        (((Janus.Float.divOdd fbits m e m' e').1 : Rat) * 2 ^ (Janus.Float.divOdd fbits m e m' e').2) ∧
      2 ^ (fbits + 4) ≤ (Janus.Float.divOdd fbits m e m' e').1 := by
  have hm'pos : 0 < m' := Nat.pos_of_ne_zero hm'
  have hbig := divN_big fbits m m' hm hm'
  unfold Janus.Float.divOdd
  generalize hk : fbits + 5 + Nat.log2 m' = k at *
  simp only []
  generalize hnum : m * 2 ^ k = num at *
  have hN : 2 ^ (fbits + 4) ≤ num / m' := hbig
  have hM : (num % m' = 0 ∧ (if num % m' = 0 then num / m' else num / m' ||| 1) = num / m') ∨
      (num % m' ≠ 0 ∧ (if num % m' = 0 then num / m' else num / m' ||| 1) = 2 * ((num / m') / 2) + 1) := by
    by_cases h : num % m' = 0
    · exact Or.inl ⟨h, by simp [h]⟩
    · exact Or.inr ⟨h, by simp [h, or_one_eq]⟩
  generalize hMm : (if num % m' = 0 then num / m' else num / m' ||| 1) = Mm at *
  have hpos : 0 < Mm := by
    rcases hM with ⟨_, h⟩ | ⟨_, h⟩ <;> have := Nat.two_pow_pos (fbits + 4) <;> omega
  refine ⟨?_, ?_⟩
  · intro n
    have c := div_cmp_rat m m' k e e' hm' n
    rw [hnum] at c
    have hnumpos : 0 < num := by
      rw [← hnum]; exact Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.two_pow_pos k)
    have d := dy_cmp Mm (e - e' - k) n
    have hint : (((num : Int) < 2 * n * (m' : Int) ↔ (Mm : Int) < 2 * n) ∧
        ((num : Int) = 2 * n * (m' : Int) ↔ (Mm : Int) = 2 * n)) := by
      by_cases hn : 0 < n
      · obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hn)
        have := div_nat_cmp num m' n' Mm hm'pos hM
        constructor
        · have h1 := this.1; exact_mod_cast h1
        · have h1 := this.2; exact_mod_cast h1
      · have hn0 : n ≤ 0 := Int.not_lt.mp hn
        have hneg : 2 * n * (m' : Int) ≤ 0 := by
          have := Int.mul_le_mul_of_nonneg_right (show 2 * n ≤ 0 by omega) (Int.natCast_nonneg m')
          simpa using this
        have hnum' : (0 : Int) < num := by exact_mod_cast hnumpos
        have hMp : (0 : Int) < Mm := by exact_mod_cast hpos
        refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩ <;> omega
    exact ⟨c.1.trans (hint.1.trans d.1.symm), c.2.trans (hint.2.trans d.2.symm)⟩
  · omega

end JanusASL.Proofs
