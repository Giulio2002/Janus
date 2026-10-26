import JanusASL.Proofs.FP.Sqrt
import JanusASL.Proofs.FP.Exec2
import JanusASL.Proofs.FP.Unpack2

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

theorem roundToInt_zero (rm : Janus.Float.RM) (neg : Bool) (e : Int) : Janus.Float.roundToInt rm neg 0 e = (0, false) := by
  unfold Janus.Float.roundToInt
  by_cases he : 0 ≤ e
  · simp [he]
  · simp [he, Janus.Float.roundUp]

theorem satQ_zero (M : Nat) (u : Bool) (hM : 0 < M) : Janus.Arm64.FP.satQ M u 0 = (0, false) := by
  have hp : 0 < 2 ^ (M - 1) := Nat.two_pow_pos _
  have hq : 0 < 2 ^ M := Nat.two_pow_pos _
  unfold Janus.Arm64.FP.satQ
  cases u
  · simp only [Bool.false_eq_true, ite_false]
    have h1 : ¬ (0 : Int) < -(2 ^ (M - 1) : Int) := by have : (0 : Int) < 2 ^ (M - 1) := Int.pow_pos (by decide); omega
    have h2 : ¬ (0 : Int) ≥ 2 ^ (M - 1) := by have : (0 : Int) < 2 ^ (M - 1) := Int.pow_pos (by decide); omega
    have hpI : (0 : Int) ≤ 2 ^ (M - 1) := Int.le_of_lt (Int.pow_pos (by decide))
    simp [h1, h2, hpI]
  · simp only [ite_true]
    have h2 : ¬ (0 : Int) ≥ 2 ^ M := by have : (0 : Int) < 2 ^ M := Int.pow_pos (by decide); omega
    simp [h2]

theorem satQ_far (M : Nat) (hM : 0 < M) (u : Bool) (i : Int)
    (h : i ≥ 2 ^ (M + 1) ∨ i ≤ -(2 ^ (M + 1) : Int)) :
    Janus.Arm64.FP.satQ M u i =
      (if i < 0 then (if u then (0, true) else (2 ^ (M - 1), true))
       else (if u then (2 ^ M - 1, true) else (2 ^ (M - 1) - 1, true))) := by
  have hP : 0 < 2 ^ (M - 1) := Nat.two_pow_pos _
  have h1 : 2 ^ M = 2 * 2 ^ (M - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have h2 : 2 ^ (M + 1) = 4 * 2 ^ (M - 1) := by
    rw [show M + 1 = (M - 1) + 2 by omega, Nat.pow_add]; omega
  have e0 : ((2 : Int) ^ (M - 1)) = ((2 ^ (M - 1) : Nat) : Int) := by simp [Int.natCast_pow]
  have e1 : ((2 : Int) ^ M) = ((2 ^ M : Nat) : Int) := by simp [Int.natCast_pow]
  have e2 : ((2 : Int) ^ (M + 1)) = ((2 ^ (M + 1) : Nat) : Int) := by simp [Int.natCast_pow]
  unfold Janus.Arm64.FP.satQ
  rw [e0, e1] at *
  rw [e2] at h
  generalize 2 ^ (M - 1) = P at *
  generalize 2 ^ M = Q at *
  generalize 2 ^ (M + 1) = R at *
  cases u
  · simp only [Bool.false_eq_true, ite_false]
    by_cases hn : i < 0
    · have h3 : i < -(P : Int) := by omega
      simp [hn, h3]
    · have h3 : i ≥ (P : Int) := by omega
      have h4 : ¬ i < -(P : Int) := by omega
      simp [hn, h3, h4]
  · simp only [ite_true]
    by_cases hn : i < 0
    · simp [hn]
    · have h3 : i ≥ (Q : Int) := by omega
      simp [hn, h3]

theorem int_pow_cast (K : Nat) : (((2 : Int) ^ K : Int) : Rat) = (2 : Rat) ^ (K : Int) := by
  rw [Rat.zpow_natCast, Rat.intCast_pow]; rfl

theorem asl_trunc' (neg : Bool) (m : Nat) (e : Int) :
    (sub_real (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e)
        (to_real (round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e))) = 0 ↔
      (Janus.Float.roundToInt .rz neg m e).2 = false) ∧
    (if ¬ sub_real (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e)
        (to_real (round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e))) = 0 ∧
      round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e) < 0
     then round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e) + 1
     else round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e)) =
      (Janus.Float.roundToInt .rz neg m e).1 := by
  obtain ⟨h1, h2⟩ := asl_trunc neg m e
  generalize (sub_real (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e)
        (to_real (round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e)))) = err at h1 h2 ⊢
  generalize round_down (if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e) = fl at h2 ⊢
  generalize (Janus.Float.roundToInt .rz neg m e) = r at h1 h2 ⊢
  refine ⟨?_, ?_⟩
  · cases hr : r.2
    · by_cases he : err = 0
      · simp [he]
      · rw [hr] at h1; simp [he] at h1
    · by_cases he : err = 0
      · rw [hr] at h1; simp [he] at h1
      · simp [he]
  · rw [← h2]
    by_cases hc : ¬ err = 0 ∧ fl < 0
    · have : (err != 0 && decide (fl < 0)) = true := by simp [hc.1, hc.2]
      simp [hc, this]
    · have : ¬ (err != 0 && decide (fl < 0)) = true := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]; exact hc
      simp [hc, this]

set_option hygiene false in
macro "fp_or_closeT" : tactic => `(tactic| (
  simp only [d1, raise_direct, raise_proc, exc_empty_direct, exc_empty_proc, ofNat0,
    BitVec.or_zero, BitVec.zero_or, ofNat_or, fpExcBit, Janus.Arm64.FP.IOC, Janus.Arm64.FP.IXC, Nat.pow_zero,
    Nat.pow_one, Nat.reducePow, exc_append_proc, exc_append_direct] <;> ac_rfl))

theorem unpack_proc_false (f : Janus.Float.Fmt) (fpcr x : Nat) :
    (Janus.Arm64.FP.unpack f fpcr false x).2.proc = 0 := by
  simp only [Janus.Arm64.FP.unpack]; split <;> (try split) <;> simp [Janus.Arm64.FP.raise]

theorem run_FPUnpackE {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (x : BitVec N)
    (fpcr v : BitVec 64) (e : Bool)
    (hen : e = true → (Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true x.toNat).2.proc ≠ 0 → fpcr.getLsbD 15 = false) :
    (FPUnpack__1 x fpcr e).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat e x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2) (s.set .FPSR (v ||| BitVec.ofNat 64 r.2.proc)) := by
  cases e
  · have hp := unpack_proc_false (fmtN N) fpcr.toNat x.toNat
    simp only [hp, ofNat0, BitVec.or_zero]
    rcases hN with rfl | rfl
    · exact run_FPUnpack32_nox (hc.set_FPSR v) x fpcr
    · exact run_FPUnpack64_nox (hc.set_FPSR v) x fpcr
  · exact run_FPUnpackN hN hc x fpcr v (hen rfl)

theorem unpack_nan_val (f : Janus.Float.Fmt) (fpcr : Nat) (e : Bool) (x : Nat)
    (h : (Janus.Arm64.FP.unpack f fpcr e x).1.1.isNaN = true) :
    (Janus.Arm64.FP.unpack f fpcr e x).1.2.2 = .num 0 0 := by
  unfold Janus.Arm64.FP.unpack at h ⊢
  generalize Janus.Float.classify f x = k at h ⊢
  cases k <;> simp only [Janus.Arm64.FP.FPType.isNaN] at h ⊢ <;> (try simp at h)
  by_cases hz : (Janus.Arm64.FP.fz fpcr = true ∧ Janus.Arm64.FP.ah fpcr = false) ∨ Janus.Arm64.FP.fiz fpcr = true
  · simp [hz]
  · simp [hz] at h

theorem fpexc_eq (b : Bool) : (!(BitVec.ofBool b == 1#1)) = !b := by cases b <;> decide

theorem run_FPToFixed {N M : Nat} (hN : N = 32 ∨ N = 64) (hM : M = 32 ∨ M = 64) {s : SState} (hc : LinuxEL0Config s)
    (op : BitVec N) (u : Bool) (fpcr v : BitVec 64)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpToFixed (fmtN N) fpcr.toNat u .rz M op.toNat).2) :
    (FPToFixed op 0 u fpcr (aslRM .rz) M).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpToFixed (fmtN N) fpcr.toNat u .rz M op.toNat
      .ok (BitVec.ofNat M r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have hN' : (Sail.BitVec.length op == 16 || (Sail.BitVec.length op == 32 || Sail.BitVec.length op == 64)) = true := by
    simp only [Sail.BitVec.length]; rcases hN with rfl | rfl <;> decide
  have hM' : (M == 16 || (M == 32 || M == 64)) = true := by rcases hM with rfl | rfl <;> decide
  have h0 : ((0 : Int) ≥b 0) = true := by decide
  have hrne : (aslRM .rz != FPRounding.FPRounding_ODD) = true := by decide
  have hrz : aslRM .rz = FPRounding.FPRounding_ZERO := rfl
  have hrne' : (FPRounding.FPRounding_ZERO != FPRounding.FPRounding_ODD) = true := by decide
  have hahe : ∀ fpcr : BitVec 64, (!Janus.Arm64.FP.ah fpcr.toNat) = !decide (fpcr.toNat / 2 % 2 = 1) := by
    intro fpcr; simp [Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit]
  unfold FPToFixed
  cfg_simp [undefined_FPType, undefined_real, run_internal_pick, run_undefined_bool, run_undefined_bitvector,
    run_sail_assert_true, hN', hM', h0, hrne, HaveAltFP, run_IsFeatureImplemented (hc.set_FPSR v),
    run_UsingAArch32 (hc.set_FPSR v), get_AH, hrz, hrne', fpexc_eq]
  unfold Janus.Arm64.FP.fpToFixed at hnt ⊢
  have d1 := unpack_direct' (fmtN N) fpcr.toNat (!Janus.Arm64.FP.ah fpcr.toNat) op.toNat
  have sp1 := unpack_spec (fmtN N) fpcr.toNat (!Janus.Arm64.FP.ah fpcr.toNat) op.toNat
  have nz1 := unpack_nzs (fmtN N) fpcr.toNat (!Janus.Arm64.FP.ah fpcr.toNat) op.toNat
  have nn1 := unpack_nan_val (fmtN N) fpcr.toNat (!Janus.Arm64.FP.ah fpcr.toNat) op.toNat
  have hUraw := fun v' hen => run_FPUnpackE hN hc op fpcr v' (!Janus.Arm64.FP.ah fpcr.toNat) hen
  generalize hUe : Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat (!Janus.Arm64.FP.ah fpcr.toNat) op.toNat = U at hnt d1 sp1 nz1 nn1 hUraw
  rcases U with ⟨⟨t1, s1, v1⟩, x1⟩
  simp only at hnt d1 sp1 nz1 nn1 hUraw
  have mr0 : ∀ q : Rat, mult_real q (real_power 2 0) = q := by
    intro q; simp [mult_real, real_power]
  rcases v1 with ⟨n, ex⟩ | neg
  case num =>
    simp only at hnt ⊢
    have hnt1 : NT fpcr.toNat x1 := nt_left (nt_left hnt)
    have hU := fun v' => hUraw v' (fun he hne => by
      have e1 : Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op.toNat =
          Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat (!Janus.Arm64.FP.ah fpcr.toNat) op.toNat := by rw [he]
      have h2 : NT fpcr.toNat (Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op.toNat).2 := by rw [e1, hUe]; exact hnt1
      exact nt_unpack h2 hne)
    rw [← hahe fpcr]
    simp only [hU, valRat_num, mr0]
    have hq : (n : Rat) * 2 ^ ex = if decide (n < 0) = true then -((n.natAbs : Rat) * 2 ^ ex) else (n.natAbs : Rat) * 2 ^ ex := by
      by_cases hn : n < 0
      · have h1 : (n : Rat) = -((n.natAbs : Nat) : Rat) := by
          have h2 : ((n.natAbs : Nat) : Int) = Neg.neg n := by omega
          have := congrArg (fun z : Int => (z : Rat)) h2
          simp only [Rat.intCast_natCast, Rat.intCast_neg] at this
          rw [this, Rat.neg_neg]
        simp only [hn, decide_true, ite_true]
        rw [h1, Rat.neg_mul]
      · have h1 : (n : Rat) = ((n.natAbs : Nat) : Rat) := by
          have h2 : ((n.natAbs : Nat) : Int) = n := by omega
          have := congrArg (fun z : Int => (z : Rat)) h2
          simp only [Rat.intCast_natCast] at this
          exact this.symm
        simp only [hn, decide_false, ite_false, Bool.false_eq_true]
        rw [h1]
    have hRI : (if n = 0 then (0, false) else Janus.Float.roundToInt Janus.Float.RM.rz s1 n.natAbs ex) =
        Janus.Float.roundToInt Janus.Float.RM.rz (decide (n < 0)) n.natAbs ex := by
      by_cases hn0 : n = 0
      · subst hn0; simp [roundToInt_zero]
      · simp only [hn0, ite_false]
        have ht : t1 = .nonzero ∨ t1 = .denormal := by
          cases t1
          · exact absurd (sp1.2.2 rfl) (by intro h; cases h; exact hn0 rfl)
          · exact Or.inr rfl
          · exact Or.inl rfl
          · exfalso; obtain ⟨s', hh⟩ := sp1.1 rfl; cases hh
          · exact absurd (nn1 rfl) (by intro h; cases h; exact hn0 rfl)
          · exact absurd (nn1 rfl) (by intro h; cases h; exact hn0 rfl)
        obtain ⟨n', e', hv, -, hs⟩ := nz1 ht
        cases hv
        rw [hs]
    obtain ⟨hA, hB⟩ := asl_trunc' (decide (n < 0)) n.natAbs ex
    rw [hq, hB]
    simp only [hA, hRI]
    generalize hJR : Janus.Float.roundToInt Janus.Float.RM.rz (decide (n < 0)) n.natAbs ex = JR
    rcases JR with ⟨i, inx⟩
    simp only [run_SatQ hM]
    simp only [hRI] at hnt
    rw [hJR] at hnt
    have hE := nt_right hnt
    have hEn := nt_right (nt_left hnt)
    have hc0 : (Janus.Arm64.FP.satQ M u i).snd = true ∨ t1.isNaN = true →
        fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false := by
      intro hh
      rcases hh with hh | hh
      · simp only [hh, ite_true] at hE
        exact getLsbD_of_testBit (nt_raise_ioc hE)
      · simp only [hh, ite_true] at hEn
        exact getLsbD_of_testBit (nt_raise_ioc hEn)
    have hc4 : (Janus.Arm64.FP.satQ M u i).snd = false → inx = true →
        fpcr.getLsbD (fpExcBit .FPExc_Inexact + 8) = false := by
      intro hh hi
      simp only [hh, hi, Bool.false_eq_true, ite_false, ite_true] at hE
      exact getLsbD_of_testBit (nt_bit hE (k := 4) (by decide) (by decide))
    have hnan_cases : t1.isNaN = true → (aslFPType t1 == FPType.FPType_SNaN) = true ∨
        (aslFPType t1 == FPType.FPType_QNaN) = true := by
      intro hh; cases t1 <;> first | exact absurd hh (by decide) | decide
    have hnan_not : t1.isNaN = false → ¬ ((aslFPType t1 == FPType.FPType_SNaN) = true ∨
        (aslFPType t1 == FPType.FPType_QNaN) = true) := by
      intro hh; cases t1 <;> first | exact absurd hh (by decide) | decide
    have hdir : ∀ (a b : Janus.Arm64.FP.Exc), a.direct = 0 → b.direct = 0 → (a +++ b).direct = 0 := by
      intro a b ha hb; simp [exc_append_direct, ha, hb]
    by_cases hnan : t1.isNaN = true
    · obtain ⟨hn0, hex0⟩ : n = 0 ∧ ex = 0 := by
        have := nn1 hnan
        simpa using this
      subst hn0; subst hex0
      rw [Int.natAbs_zero, roundToInt_zero] at hJR
      simp only [Prod.mk.injEq] at hJR
      obtain ⟨hi0, hinx⟩ := hJR
      subst hi0; subst hinx
      have hsq := satQ_zero M u (by omega)
      simp only [hsq]
      have hcn := hnan_cases hnan
      have hbit := hc0 (Or.inr hnan)
      simp only [hcn, ite_true]
      have hPE := run_PE_set (s := s) hc .FPExc_InvalidOp fpcr hbit (v ||| BitVec.ofNat 64 x1.proc)
      simp only [hPE, hnan, ite_true, Bool.false_eq_true, ite_false, run_pure]
      fp_or_closeT
    · have hnan' : t1.isNaN = false := by simpa using hnan
      have hnn := hnan_not hnan'
      simp only [hnn, ite_false, hnan, Bool.false_eq_true, run_pure]
      by_cases hs : (Janus.Arm64.FP.satQ M u i).snd = true
      · have hbit := hc0 (Or.inl hs)
        have hPE := run_PE_set (s := s) hc .FPExc_InvalidOp fpcr hbit (v ||| BitVec.ofNat 64 x1.proc)
        simp only [hs, ite_true, hPE]
        fp_or_closeT
      · have hs' : (Janus.Arm64.FP.satQ M u i).snd = false := by simpa using hs
        by_cases hi : inx = true
        · have hbit := hc4 hs' hi
          have hPE := run_PE_set (s := s) hc .FPExc_Inexact fpcr hbit (v ||| BitVec.ofNat 64 x1.proc)
          simp only [hs', hi, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, hPE]
          fp_or_closeT
        · have hi' : inx = false := by simpa using hi
          simp only [hs', hi', Bool.false_eq_true, ite_false, ite_true, run_pure]
          fp_or_closeT
  case inf =>
    simp only at hnt ⊢
    have hnt1 : NT fpcr.toNat x1 := nt_left (nt_left hnt)
    have hU := fun v' => hUraw v' (fun he hne => by
      have e1 : Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op.toNat =
          Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat (!Janus.Arm64.FP.ah fpcr.toNat) op.toNat := by rw [he]
      have h2 : NT fpcr.toNat (Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op.toNat).2 := by rw [e1, hUe]; exact hnt1
      exact nt_unpack h2 hne)
    rw [← hahe fpcr]
    simp only [hU]
    have hti : t1 = .infinity := by
      refine Classical.byContradiction fun hne => ?_
      obtain ⟨n, e', h⟩ := sp1.2.1 hne
      cases h
    subst hti
    have hbig : ((2 : Int) ^ 1000000) ≥ 2 ^ (M + 1) := by
      have : 2 ^ (M + 1) ≤ 2 ^ 1000000 := Nat.pow_le_pow_right (by decide) (by rcases hM with rfl | rfl <;> decide)
      have := Int.ofNat_le.mpr this
      simpa [Int.natCast_pow] using this
    generalize hKq : (1000000 : Nat) = K at hbig
    have hvr : valRat (Janus.Float.Val.inf neg) = (((if neg = true then -(2 : Int) ^ K else (2 : Int) ^ K : Int)) : Rat) := by
      cases neg
      · simp only [valRat, Bool.false_eq_true, ite_false]
        rw [int_pow_cast, ← hKq]; rfl
      · simp only [valRat, ite_true, Rat.intCast_neg]
        rw [int_pow_cast, ← hKq]; rfl
    rw [hvr, mr0]
    have hfl : round_down ((((if neg = true then -(2 : Int) ^ K else (2 : Int) ^ K : Int)) : Rat)) =
        (if neg = true then -(2 : Int) ^ K else (2 : Int) ^ K) := by
      simp only [round_down]; exact Rat.floor_intCast _
    rw [hfl]
    have herr : sub_real ((((if neg = true then -(2 : Int) ^ K else (2 : Int) ^ K : Int)) : Rat))
        (to_real (if neg = true then -(2 : Int) ^ K else (2 : Int) ^ K)) = 0 := by
      simp only [sub_real, to_real]; exact Rat.sub_self
    simp only [herr, ne_eq, not_true_eq_false, false_and, ite_false, and_false, run_SatQ hM]
    have hM0 : 0 < M := by omega
    have hq1 : Janus.Arm64.FP.satQ M u (if neg = true then -(2 : Int) ^ K else (2 : Int) ^ K) =
        Janus.Arm64.FP.satQ M u (if neg = true then -(2 : Int) ^ (M + 1) else (2 : Int) ^ (M + 1)) := by
      cases neg
      · simp only [Bool.false_eq_true, ite_false]
        rw [satQ_far M hM0 u _ (Or.inl hbig), satQ_far M hM0 u _ (Or.inl (Int.le_refl _))]
        have h1 : ¬ ((2 : Int) ^ K < 0) := Int.not_lt.mpr (Int.le_of_lt (Int.pow_pos (by decide)))
        have h2 : ¬ ((2 : Int) ^ (M + 1) < 0) := Int.not_lt.mpr (Int.le_of_lt (Int.pow_pos (by decide)))
        simp only [h1, h2]
      · simp only [ite_true]
        have hb2 : -(2 : Int) ^ K ≤ -(2 : Int) ^ (M + 1) := by omega
        rw [satQ_far M hM0 u _ (Or.inr hb2), satQ_far M hM0 u _ (Or.inr (Int.le_refl _))]
        have h1 : -(2 : Int) ^ K < 0 := by have : (0 : Int) < 2 ^ K := Int.pow_pos (by decide); omega
        have h2 : -(2 : Int) ^ (M + 1) < 0 := by have : (0 : Int) < 2 ^ (M + 1) := Int.pow_pos (by decide); omega
        simp only [h1, h2]
    rw [hq1]
    have hsat : (Janus.Arm64.FP.satQ M u (if neg = true then -(2 : Int) ^ (M + 1) else (2 : Int) ^ (M + 1))).snd = true := by
      have hM0' : 0 < M := hM0
      cases neg
      · simp only [Bool.false_eq_true, ite_false]
        rw [satQ_far M hM0 u _ (Or.inl (Int.le_refl _))]
        have h2 : ¬ ((2 : Int) ^ (M + 1) < 0) := Int.not_lt.mpr (Int.le_of_lt (Int.pow_pos (by decide)))
        simp only [h2, ite_false]; cases u <;> rfl
      · simp only [ite_true]
        rw [satQ_far M hM0 u _ (Or.inr (Int.le_refl _))]
        have h2 : -(2 : Int) ^ (M + 1) < 0 := by have : (0 : Int) < 2 ^ (M + 1) := Int.pow_pos (by decide); omega
        simp only [h2, ite_true]; cases u <;> rfl
    have hbit : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false :=
      getLsbD_of_testBit (nt_raise_ioc (nt_right hnt))
    have hPE := run_PE_set (s := s) hc .FPExc_InvalidOp fpcr hbit (v ||| BitVec.ofNat 64 x1.proc)
    have hnn : Janus.Arm64.FP.FPType.infinity.isNaN = false := rfl
    have hnn2 : ¬ ((aslFPType Janus.Arm64.FP.FPType.infinity == FPType.FPType_SNaN) = true ∨
        (aslFPType Janus.Arm64.FP.FPType.infinity == FPType.FPType_QNaN) = true) := by decide
    simp only [hnn2, ite_false, hnn, Bool.false_eq_true, hsat, ite_true, hPE, run_pure, EStateM.run_bind]
    fp_or_closeT

end JanusASL.Proofs
