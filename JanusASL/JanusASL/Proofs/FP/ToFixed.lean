import JanusASL.Proofs.FP.Sqrt
import JanusASL.Proofs.FP.Exec2

/-! # Float to integer conversion with rounding toward zero: the rational part of `FPToFixed`

`FPToFixed` rounds `value` down, then adds one when `rounding` asks for it (`error != 0 && int_result < 0` for
`FPRounding_ZERO`); Janus' `roundToInt` truncates the magnitude. -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem floor_eq_of_bounds (y : Rat) (z : Int) (h1 : (z : Rat) ≤ y) (h2 : y < (z : Rat) + 1) : round_down y = z := by
  simp only [round_down]
  apply Int.le_antisymm
  · have : y.floor < z + 1 := by
      rw [Rat.floor_lt_iff]; rw [Rat.intCast_add, Rat.intCast_one]; exact h2
    omega
  · rw [Rat.le_floor_iff]; exact h1

theorem floor_negfrac (f : Rat) (h0 : 0 < f) (h1 : f < 1) : round_down (-f) = -1 := by
  apply floor_eq_of_bounds
  · rw [Rat.intCast_neg, Rat.intCast_one]; exact Rat.neg_le_neg (Rat.le_of_lt h1)
  · rw [Rat.intCast_neg, Rat.intCast_one, Rat.neg_add_cancel]
    have := Rat.neg_lt_neg h0
    rwa [Rat.neg_zero] at this

theorem sub_eq_zero_rat {a b : Rat} (h : a - b = 0) : a = b := by
  rw [Rat.sub_eq_add_neg] at h
  exact Rat.add_right_cancel (-b) (h.trans (Rat.add_neg_cancel b).symm)

theorem bne_sub (a : Rat) (z : Int) : (sub_real a (to_real z) != 0) = decide (a ≠ (z : Rat)) := by
  simp only [sub_real, to_real]
  by_cases h : a = (z : Rat)
  · have e : Rat.ofInt z = (z : Rat) := rfl
    rw [e, h]; simp [Rat.sub_self]
  · have e : Rat.ofInt z = (z : Rat) := rfl
    rw [e]
    have : a - (z : Rat) ≠ 0 := fun h0 => h (sub_eq_zero_rat h0)
    simp [h, this]


theorem rz_false (neg : Bool) (k rem s : Nat) : Janus.Float.roundUp .rz neg k rem s = false := by
  simp [Janus.Float.roundUp]

theorem natCast_eq_mul (m e : Nat) : (m : Rat) * 2 ^ (e : Int) = ((m * 2 ^ e : Nat) : Rat) := nat_mul_two_pow m e

/-- `RoundDown`, the error and the `FPRounding_ZERO` adjustment of `±m * 2^e` agree with `roundToInt .rz`. -/
theorem asl_trunc (neg : Bool) (m : Nat) (e : Int) :
    ((sub_real (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e)
        (to_real (round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e)))) != 0) =
      decide ((Janus.Float.roundToInt .rz neg m e).2 = true) ∧
    (if ((sub_real (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e)
        (to_real (round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e)))) != 0 &&
      decide (round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e) < 0)) = true
     then round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e) + 1
     else round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e)) =
      (Janus.Float.roundToInt .rz neg m e).1 := by
  rw [bne_sub]
  unfold Janus.Float.roundToInt
  by_cases he : 0 ≤ e
  · obtain ⟨hf, -⟩ := (rd_split m e).1 he
    have e1 : (m : Rat) * 2 ^ e = ((m * 2 ^ e.toNat : Nat) : Rat) := by
      rw [← nat_mul_two_pow]; congr 2; omega
    simp only [he, ite_true]
    cases neg
    · simp only [Bool.false_eq_true, ite_false]
      rw [hf, e1, Rat.intCast_natCast]
      simp
    · simp only [ite_true]
      have hfl : round_down (-((m : Rat) * 2 ^ e)) = -((m * 2 ^ e.toNat : Nat) : Int) := by
        rw [e1, ← Rat.intCast_natCast, ← Rat.intCast_neg]
        simp only [round_down]; exact Rat.floor_intCast _
      rw [hfl, e1, Rat.intCast_neg, Rat.intCast_natCast]
      simp
  · have hd : e < 0 := by omega
    obtain ⟨hf, -⟩ := (rd_split m e).2 hd
    have e1 : (m : Rat) * 2 ^ e = (m : Rat) * 2 ^ (-(((-e).toNat : Nat) : Int)) := by congr 2; omega
    have hsp := split_div m (-e).toNat
    have hlt : m % 2 ^ (-e).toNat < 2 ^ (-e).toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hf1 := frac_lt_one _ _ hlt
    have hz : (((m % 2 ^ (-e).toNat : Nat) : Rat) * 2 ^ (-(((-e).toNat : Nat) : Int)) = 0) = (m % 2 ^ (-e).toNat = 0) :=
      frac_eq_zero _ _
    simp only [he, ite_false, rz_false, Bool.false_eq_true]
    rw [e1] at hf
    simp only [e1]
    generalize hk : m / 2 ^ (-e).toNat = k at hf hsp
    generalize hr : m % 2 ^ (-e).toNat = r at hz hf1 hsp hlt
    generalize hF : (r : Rat) * 2 ^ (-(((-e).toNat : Nat) : Int)) = f at hz hf1 hsp
    cases neg
    · simp only [Bool.false_eq_true, ite_false]
      rw [hf]
      by_cases hr0 : r = 0
      · subst hr0
        have : f = 0 := hz.mpr rfl
        rw [hsp, this, Rat.add_zero]
        simp [Rat.intCast_natCast]
      · have hf0 : f ≠ 0 := fun h0 => hr0 (hz.mp h0)
        have : (k : Rat) + f ≠ ((k : Int) : Rat) := by
          rw [Rat.intCast_natCast]
          intro h0
          apply hf0
          have := Rat.add_left_cancel (k : Rat) (h0.trans (Rat.add_zero _).symm)
          exact this
        rw [hsp]
        simp [this, hr0]
        intro h; omega
    · simp only [ite_true]
      have hneg : -((k : Rat) + f) = (-f) + (((-(k : Int)) : Int) : Rat) := by
        rw [Rat.neg_add, Rat.intCast_neg, Rat.intCast_natCast, Rat.add_comm]
      rw [hsp, hneg]
      by_cases hr0 : r = 0
      · subst hr0
        have hf0 : f = 0 := hz.mpr rfl
        have hfl : round_down ((-f) + (((-(k : Int)) : Int) : Rat)) = -(k : Int) := by
          rw [hf0, Rat.neg_zero, Rat.zero_add]
          simp only [round_down]; exact Rat.floor_intCast _
        rw [hfl]
        rw [hf0, Rat.neg_zero, Rat.zero_add]
        simp [Rat.intCast_natCast]
      · have hf0 : f ≠ 0 := fun h0 => hr0 (hz.mp h0)
        have hfnn : (0 : Rat) ≤ f := by
          rw [← hF]
          exact Rat.mul_nonneg (Rat.natCast_nonneg) (Rat.le_of_lt (Rat.zpow_pos two_pos_rat))
        have hfpos : 0 < f := Classical.byContradiction fun h => hf0 (Rat.le_antisymm (Rat.not_lt.mp h) hfnn)
        have hfl : round_down ((-f) + (((-(k : Int)) : Int) : Rat)) = -1 + -(k : Int) := by
          simp only [round_down]
          rw [Rat.floor_add_intCast]
          have := floor_negfrac f hfpos hf1
          simp only [round_down] at this
          rw [this]
        rw [hfl]
        have hne : (-f) + (((-(k : Int)) : Int) : Rat) ≠ (((-1 + -(k : Int)) : Int) : Rat) := by
          intro h0
          simp only [Rat.intCast_add, Rat.intCast_neg, Rat.intCast_one, Rat.intCast_natCast] at h0
          have := Rat.add_right_cancel _ h0
          have h1 : f = 1 := by
            have := congrArg Neg.neg this
            rwa [Rat.neg_neg, Rat.neg_neg] at this
          rw [h1] at hf1
          exact absurd hf1 (Rat.lt_irrefl)
        have hdec : decide ((-f) + (((-(k : Int)) : Int) : Rat) ≠ (((-1 + -(k : Int)) : Int) : Rat)) = true := decide_eq_true hne
        have hr' : decide (r ≠ 0) = true := by simp [hr0]
        have hneg0 : (-1 + -(k : Int) <b 0) = true := by
          show decide ((-1 + -(k : Int)) < 0) = true
          simp; omega
        rw [hdec, hr', hneg0]
        simp only [Bool.true_and, ite_true, decide_true]
        refine ⟨by simp, ?_⟩
        omega


theorem integer_subrange_toNat' (i : Int) (hi : Nat) :
    (integer_subrange i (hi : Int) 0).toNat = (i % 2 ^ (hi + 1)).toNat := by
  simp only [integer_subrange, Sail.get_slice_int, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    BitVec.toNat_ofInt]
  have e1 : ((hi : Int) - 0 + 1).toNat = hi + 1 := by omega
  have e2 : (hi : Int).toNat = hi := by omega
  simp only [Int.toNat_zero, e1, e2, Nat.shiftRight_zero, Nat.zero_add, Nat.sub_zero, Nat.mod_mod]
  have hb : (0 : Int) ≤ i % ((2 ^ (hi + 1 + 1) : Nat) : Int) :=
    Int.emod_nonneg _ (by have := Nat.two_pow_pos (hi + 1 + 1); omega)
  rw [← Int.toNat_natCast (2 ^ (hi + 1)), ← Int.toNat_emod hb (Int.natCast_nonneg _)]
  congr 1
  rw [Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 (show hi + 1 ≤ hi + 1 + 1 by omega)))]
  simp [Int.natCast_pow]


theorem subrange_toNat {M : Nat} (hM : M = 32 ∨ M = 64) (res : Int) :
    (BitVec.setWidth M (integer_subrange res ((M : Int) - 1) 0)).toNat = (res % 2 ^ M).toNat := by
  rcases hM with rfl | rfl
  · show (BitVec.setWidth 32 (integer_subrange res ((31 : Nat) : Int) 0)).toNat = (res % 2 ^ 32).toNat
    rw [BitVec.toNat_setWidth]
    have := integer_subrange_toNat' res 31
    rw [this]
    have h : (res % 2 ^ (31 + 1)).toNat < 2 ^ 32 := by
      have h0 : 0 ≤ res % 2 ^ (31 + 1) := Int.emod_nonneg _ (by decide)
      have h1 := Int.emod_lt_of_pos res (show (0 : Int) < 2 ^ (31 + 1) by decide)
      omega
    exact Nat.mod_eq_of_lt h
  · show (BitVec.setWidth 64 (integer_subrange res ((63 : Nat) : Int) 0)).toNat = (res % 2 ^ 64).toNat
    rw [BitVec.toNat_setWidth]
    have := integer_subrange_toNat' res 63
    rw [this]
    have h : (res % 2 ^ (63 + 1)).toNat < 2 ^ 64 := by
      have h0 : 0 ≤ res % 2 ^ (63 + 1) := Int.emod_nonneg _ (by decide)
      have h1 := Int.emod_lt_of_pos res (show (0 : Int) < 2 ^ (63 + 1) by decide)
      omega
    exact Nat.mod_eq_of_lt h

theorem subrange_eq {M : Nat} (hM : M = 32 ∨ M = 64) (res : Int) :
    BitVec.setWidth M (integer_subrange res ((M : Int) - 1) 0) = BitVec.ofNat M (res % 2 ^ M).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [subrange_toNat hM, BitVec.toNat_ofNat]
  have hP : (0 : Int) < 2 ^ M := Int.pow_pos (by decide)
  have h0 : 0 ≤ res % 2 ^ M := Int.emod_nonneg _ (Int.ne_of_gt hP)
  have h1 := Int.emod_lt_of_pos res hP
  have : (res % 2 ^ M).toNat < 2 ^ M := by
    rw [Int.toNat_lt h0]; simpa [Int.natCast_pow] using h1
  rw [Nat.mod_eq_of_lt this]

theorem run_SatQ {M : Nat} (hM : M = 32 ∨ M = 64) (i : Int) (u : Bool) (s : SState) :
    (SatQ i M u).run s = .ok (BitVec.ofNat M (Janus.Arm64.FP.satQ M u i).1, (Janus.Arm64.FP.satQ M u i).2) s := by
  have hM1 : (0 : Int) ≤ (M : Int) - 1 := by omega
  have hM' := hM
  unfold SatQ
  cases u
  · unfold SignedSatQ
    simp only [Bool.false_eq_true, ite_false, run_bind, run_undefined_int, run_undefined_bool, run_undefined_bitvector,
      run_pure, run_sail_assert_of (show ((0 : Int) ≤b (M : Int) - 1) = true by simp; omega)]
    unfold Janus.Arm64.FP.satQ
    simp only [Bool.false_eq_true, ite_false]
    have hp : (2 : Int) ^ ((M : Int) - 1) = ((2 ^ (M - 1) : Nat) : Int) := by
      rw [ipow_int, show ((M : Int) - 1).toNat = M - 1 by omega]; simp
    have hPm : 2 ^ M = 2 * 2 ^ (M - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hP0 : 0 < 2 ^ (M - 1) := Nat.two_pow_pos _
    have hmI : ((2 : Int) ^ M) = (2 : Int) * ((2 ^ (M - 1) : Nat) : Int) := by
      have := congrArg (fun n : Nat => (n : Int)) hPm
      simpa [Int.natCast_pow] using this
    have hI : (2 : Int) ^ (M - 1) = ((2 ^ (M - 1) : Nat) : Int) := by simp [Int.natCast_pow]
    generalize hPN : 2 ^ (M - 1) = P at hp hPm hP0 hmI hI ⊢
    have hm : (2 : Int) ^ M = 2 * (P : Int) := hmI
    have tn_small : ∀ (x m : Int), 0 ≤ x → x < m → (x % m).toNat = x.toNat := fun x m h0 h1 => by
      rw [Int.emod_eq_of_lt h0 h1]
    have tn_neg : ∀ (x m : Int), -m ≤ x → x < 0 → (x % m).toNat = (x + m).toNat := fun x m h0 h1 => by
      rw [Int.emod_eq_add_self_emod (a := x) (b := m), Int.emod_eq_of_lt (by omega) (by omega)]
    by_cases h1 : i > (2 : Int) ^ ((M : Int) - 1) - 1
    · have h1' : (i >b (2 : Int) ^ ((M : Int) - 1) - 1) = true := by simpa using h1
      have h2 : ¬ i < -(2 : Int) ^ ((M : Int) - 1) := by rw [hp] at h1 ⊢; omega
      simp only [h1', ite_true]
      rw [subrange_eq hM]
      rw [hp, hm, tn_small _ _ (by omega) (by omega)]
      rw [hI]
      have h3 : ¬ i < -(P : Int) := by rw [hp] at h1; omega
      have h4 : i ≥ (P : Int) := by rw [hp] at h1; omega
      simp only [h3, h4, ite_false, ite_true]
      congr 3
      omega
    · have h1' : ¬ (i >b (2 : Int) ^ ((M : Int) - 1) - 1) = true := by simpa using h1
      simp only [h1', ite_false, Bool.false_eq_true]
      by_cases h2 : i < -(2 : Int) ^ ((M : Int) - 1)
      · have h2' : (i <b -(2 : Int) ^ ((M : Int) - 1)) = true := by simpa using h2
        simp only [h2', ite_true, ite_false, Bool.false_eq_true]
        rw [subrange_eq hM]
        rw [hp] at h2
        rw [hp, hm, tn_neg _ _ (by omega) (by omega)]
        rw [hI]
        have h3 : i < -(P : Int) := h2
        simp only [h3, ite_true]
        congr 3
        omega
      · have h2' : ¬ (i <b -(2 : Int) ^ ((M : Int) - 1)) = true := by simpa using h2
        simp only [h2', ite_false, Bool.false_eq_true]
        rw [subrange_eq hM]
        rw [hp] at h1 h2
        rw [hm]
        rw [hI]
        have h3 : ¬ i < -(P : Int) := h2
        have h4 : ¬ i ≥ (P : Int) := by omega
        simp only [h3, h4, ite_false]
  · unfold UnsignedSatQ
    simp only [Bool.false_eq_true, ite_false, ite_true, run_bind, run_undefined_int, run_undefined_bool, run_undefined_bitvector,
      run_pure, run_sail_assert_of (show ((0 : Int) ≤b (M : Int) - 1) = true by simp; omega)]
    unfold Janus.Arm64.FP.satQ
    simp only [ite_true]
    have hq : (2 : Int) ^ (M : Int) = ((2 ^ M : Nat) : Int) := by
      rw [ipow_int, show (M : Int).toNat = M by omega]; simp
    have hP0 : 0 < 2 ^ M := Nat.two_pow_pos _
    have hq2 : (2 : Int) ^ M = ((2 ^ M : Nat) : Int) := by simp [Int.natCast_pow]
    generalize hQN : 2 ^ M = Q at hq hq2 hP0
    have tn_small : ∀ (x m : Int), 0 ≤ x → x < m → (x % m).toNat = x.toNat := fun x m h0 h1 => by
      rw [Int.emod_eq_of_lt h0 h1]
    by_cases h1 : i > (2 : Int) ^ (M : Int) - 1
    · have h1' : (i >b (2 : Int) ^ (M : Int) - 1) = true := by simpa using h1
      simp only [h1', ite_true]
      rw [subrange_eq hM]
      have h4 : ¬ i < 0 := by rw [hq] at h1; omega
      have h5 : i ≥ (Q : Int) := by rw [hq] at h1; omega
      simp only [hq, hq2]
      rw [tn_small _ _ (by omega) (by omega)]
      simp only [h4, h5, ite_false, ite_true, Bool.false_eq_true, hq2]
      congr 3
      omega
    · have h1' : ¬ (i >b (2 : Int) ^ (M : Int) - 1) = true := by simpa using h1
      simp only [h1', ite_false, Bool.false_eq_true]
      have h5 : ¬ i ≥ (Q : Int) := by rw [hq] at h1; omega
      by_cases h2 : i < 0
      · have h2' : (i <b 0) = true := by simpa using h2
        simp only [h2', ite_true, hq2, h2, h5, ite_false, Bool.false_eq_true, decide_true]
        rw [subrange_eq hM]
        simp
      · have h2' : ¬ (i <b 0) = true := by simpa using h2
        simp only [h2', ite_false, hq2, h2, h5, Bool.false_eq_true, decide_false]
        rw [subrange_eq hM, hq2, tn_small _ _ (by omega) (by rw [hq] at h1; omega)]

end JanusASL.Proofs
