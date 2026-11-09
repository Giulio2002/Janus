import JanusASL.Proofs.FP.Round
import JanusASL.Proofs.FP.Unpack
import JanusASL.Proofs.FP.SailME

/-! # Building blocks of `FPRoundBase` against Janus' `fpRound` (binary32): the generated loops, the
scaled mantissas, floors and errors, the comparison with 1/2, and the result encoding -/
set_option linter.unusedSimpArgs false
namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- Janus' rounding direction as the ASL's `FPRounding`. -/
def aslRM : Janus.Float.RM → FPRounding
  | .rne => .FPRounding_TIEEVEN
  | .rpi => .FPRounding_POSINF
  | .rmi => .FPRounding_NEGINF
  | .rz => .FPRounding_ZERO
  | .rna => .FPRounding_TIEAWAY

/-- The signed value `(-1)^neg * m * 2^e`. -/
def sval (neg : Bool) (m : Nat) (e : Int) : Rat := if neg then -((m : Rat) * 2 ^ e) else (m : Rat) * 2 ^ e

theorem fpr_loop1 {β : Type} (m : Nat) (hm : m ≠ 0) (e : Int) :
    (forIn (m := SailME β) Lean.Loop.mk ((0 : Int), (m : Rat) * 2 ^ e) fun _ (r : Int × real) =>
        if lt_real r.2 1 = true then pure (ForInStep.yield (r.1 - 1, mult_real r.2 2)) else pure (ForInStep.done r)) =
      pure (-(((-((Nat.log2 m : Int) + e)).toNat : Nat) : Int),
        (m : Rat) * 2 ^ e * 2 ^ (((-((Nat.log2 m : Int) + e)).toNat : Nat) : Int)) := by
  obtain ⟨c1, c2, _, _⟩ := norm_counts m hm e
  exact loop_dbl _ (fun r => by by_cases h : r.2 < 1 <;> simp [lt_real, mult_real, h]) _ _ c1 c2

theorem fpr_loop2 {β : Type} (m : Nat) (hm : m ≠ 0) (e : Int) :
    (forIn (m := SailME β) Lean.Loop.mk (-max (-((Nat.log2 m : Int) + e)) 0,
        (m : Rat) * 2 ^ e * 2 ^ max (-((Nat.log2 m : Int) + e)) 0) fun _ (r : Int × real) =>
        if gteq_real r.2 2 = true then pure (ForInStep.yield (r.1 + 1, div_real r.2 2)) else pure (ForInStep.done r)) =
      pure ((Nat.log2 m : Int) + e, (m : Rat) * 2 ^ (-(Nat.log2 m : Int))) := by
  obtain ⟨_, _, c3, c4⟩ := norm_counts m hm e
  have e1 : max (-((Nat.log2 m : Int) + e)) 0 = (((-((Nat.log2 m : Int) + e)).toNat : Nat) : Int) := by omega
  rw [e1, loop_half _ (fun r => by by_cases h : 2 ≤ r.2 <;> simp [gteq_real, div_real, h]) _ _ _ c3 c4]
  congr 2
  · omega
  · rw [Rat.mul_assoc, Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat, ← Rat.zpow_add two_ne_zero_rat]
    congr 2; omega

theorem sc32 (m : Nat) (e : Int) :
    mult_real (if max ((Nat.log2 m : Int) + e + 126 + 1) 0 = 0 then
        div_real ((m : Rat) * 2 ^ (-(Nat.log2 m : Int))) (real_power 2 (-126 - ((Nat.log2 m : Int) + e)))
      else (m : Rat) * 2 ^ (-(Nat.log2 m : Int))) (real_power 2 23) =
      (m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23)) := by
  simp only [mult_real, div_real, real_power]
  split
  · rw [Rat.div_def, ← Rat.zpow_neg, Rat.mul_assoc, Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat,
      ← Rat.zpow_add two_ne_zero_rat]
    congr 2; omega
  · rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
    congr 2; omega

theorem su32 (m : Nat) :
    mult_real ((m : Rat) * 2 ^ (-(Nat.log2 m : Int))) (real_power 2 23) =
      (m : Rat) * 2 ^ (23 - (Nat.log2 m : Int)) := by
  simp only [mult_real, real_power]
  rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
  congr 2; omega

theorem mag_pos (m : Nat) (hm : m ≠ 0) (e : Int) : (0 : Rat) < (m : Rat) * 2 ^ e :=
  Rat.mul_pos (Rat.natCast_pos.mpr (Nat.pos_of_ne_zero hm)) (Rat.zpow_pos two_pos_rat)

theorem sval_sign (neg : Bool) (m : Nat) (hm : m ≠ 0) (e : Int) :
    (if lt_real (sval neg m e) 0 = true then (neg_real (sval neg m e), 1#1) else (sval neg m e, 0#1)) =
      ((m : Rat) * 2 ^ e, if neg then 1#1 else 0#1) := by
  have hp := mag_pos m hm e
  cases neg
  · have : ¬ (m : Rat) * 2 ^ e < 0 := Rat.not_lt.mpr (Rat.le_of_lt hp)
    simp [sval, lt_real, this]
  · have : -((m : Rat) * 2 ^ e) < 0 := by have := Rat.neg_lt_neg hp; rwa [Rat.neg_zero] at this
    simp [sval, lt_real, this, neg_real]

theorem nat_mul_two_pow (m k : Nat) : (m : Rat) * 2 ^ (k : Int) = ((m * 2 ^ k : Nat) : Rat) := by
  rw [Rat.zpow_natCast, Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat]

/-- Floor and error of `m * 2^d`, as `roundAt` splits it. -/
theorem rd_split (m : Nat) (d : Int) :
    (0 ≤ d → round_down ((m : Rat) * 2 ^ d) = ((m * 2 ^ d.toNat : Nat) : Int) ∧
      sub_real ((m : Rat) * 2 ^ d) (to_real (round_down ((m : Rat) * 2 ^ d))) = 0) ∧
    (d < 0 → round_down ((m : Rat) * 2 ^ d) = ((m / 2 ^ (-d).toNat : Nat) : Int) ∧
      sub_real ((m : Rat) * 2 ^ d) (to_real (round_down ((m : Rat) * 2 ^ d))) =
        ((m % 2 ^ (-d).toNat : Nat) : Rat) * 2 ^ (-((-d).toNat : Int))) := by
  constructor
  · intro hd
    have e : (m : Rat) * 2 ^ d = ((m * 2 ^ d.toNat : Nat) : Rat) := by
      rw [← nat_mul_two_pow]; congr 2; omega
    have hf : round_down ((m : Rat) * 2 ^ d) = ((m * 2 ^ d.toNat : Nat) : Int) := by
      simp only [round_down]; rw [e, ← Rat.intCast_natCast, Rat.floor_intCast]
    refine ⟨hf, ?_⟩
    simp only [sub_real, to_real]; rw [hf, e]
    show ((m * 2 ^ d.toNat : Nat) : Rat) - (((m * 2 ^ d.toNat : Nat) : Int) : Rat) = 0
    rw [Rat.intCast_natCast, Rat.sub_eq_add_neg, Rat.add_neg_cancel]
  · intro hd
    have e : (m : Rat) * 2 ^ d = (m : Rat) * 2 ^ (-((-d).toNat : Int)) := by congr 2; omega
    have hf : round_down ((m : Rat) * 2 ^ d) = ((m / 2 ^ (-d).toNat : Nat) : Int) := by
      simp only [round_down]; rw [e, floor_div]
    refine ⟨hf, ?_⟩
    simp only [sub_real, to_real]; rw [hf, e, split_div]
    show ((m / 2 ^ (-d).toNat : Nat) : Rat) + _ - (((m / 2 ^ (-d).toNat : Nat) : Int) : Rat) = _
    rw [Rat.intCast_natCast, Rat.sub_eq_add_neg, Rat.add_comm _ (_ * _), Rat.add_assoc, Rat.add_neg_cancel,
      Rat.add_zero]

theorem get_UFE (v : BitVec 64) : _get_FPCRType_UFE v = BitVec.ofBool (v.toNat / 2 ^ 11 % 2 = 1) := by
  apply BitVec.eq_of_toNat_eq
  show (Sail.BitVec.extractLsb v 11 11).toNat = _
  rw [extractLsb_toNat']
  rcases (by omega : v.toNat / 2 ^ 11 % 2 = 0 ∨ v.toNat / 2 ^ 11 % 2 = 1) with h | h <;> rw [h] <;> decide

theorem err_exact (m : Nat) (d : Int) (hd : 0 ≤ d) :
    sub_real ((m : Rat) * 2 ^ d) (to_real ((m * 2 ^ d.toNat : Nat) : Int)) = 0 := by
  have := (rd_split m d).1 hd
  rw [this.1] at this; exact this.2

theorem err_inexact (m : Nat) (d : Int) (hd : d < 0) :
    sub_real ((m : Rat) * 2 ^ d) (to_real ((m / 2 ^ (-d).toNat : Nat) : Int)) =
      ((m % 2 ^ (-d).toNat : Nat) : Rat) * 2 ^ (-((-d).toNat : Int)) := by
  have := (rd_split m d).2 hd
  rw [this.1] at this; exact this.2

theorem half_pos : (0 : Rat) < 1 / 2 := by
  rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr two_pos_rat
theorem gt_zero_half : gt_real (0 : Rat) (1 / 2) = false := by
  simp only [gt_real, decide_eq_false_iff_not]; exact Rat.not_lt.mpr (Rat.le_of_lt half_pos)
theorem eq_zero_half : eq_real (0 : Rat) (1 / 2) = false := by
  simp only [eq_real, beq_eq_false_iff_ne, ne_eq]; intro h; exact Rat.lt_irrefl (h ▸ half_pos)
theorem bne_zero_zero : ((0 : Rat) != 0) = false := by simp
theorem gt_frac_half (r s : Nat) : gt_real ((r : Rat) * 2 ^ (-(s : Int))) (1 / 2) = decide (2 ^ s < 2 * r) := by
  simp only [gt_real]; exact decide_eq_decide.mpr (half_lt_frac r s)
theorem eq_frac_half (r s : Nat) : eq_real ((r : Rat) * 2 ^ (-(s : Int))) (1 / 2) = decide (2 * r = 2 ^ s) := by
  simp only [eq_real]; by_cases h : 2 * r = 2 ^ s
  · simp [h, (frac_eq_half r s).mpr h]
  · have : ¬ ((r : Rat) * 2 ^ (-(s : Int)) = 1 / 2) := fun e => h ((frac_eq_half r s).mp e)
    simp [h, this]
theorem bne_frac_zero (r s : Nat) : (((r : Rat) * 2 ^ (-(s : Int))) != 0) = decide (r ≠ 0) := by
  by_cases h : r = 0
  · subst h; simp
  · have : (r : Rat) * 2 ^ (-(s : Int)) ≠ 0 := (frac_ne_zero r s).mpr h
    simp [h, this]


theorem run_FPInfinity32 (s : SState) (neg : Bool) :
    (FPInfinity (if neg then 1#1 else 0#1) 32).run s = .ok (BitVec.ofNat 32 (Janus.Float.inf Janus.Float.binary32 neg)) s := by
  cases neg <;> cfg_simp [FPInfinity] <;> decide

theorem run_FPMaxNormal32 (s : SState) (neg : Bool) :
    (FPMaxNormal (if neg then 1#1 else 0#1) 32).run s =
      .ok (BitVec.ofNat 32 (Janus.Float.maxNormal Janus.Float.binary32 neg)) s := by
  cases neg <;> cfg_simp [FPMaxNormal] <;> decide

theorem run_FPZero32 (s : SState) (neg : Bool) :
    (FPZero (if neg then 1#1 else 0#1) 32).run s = .ok (BitVec.ofNat 32 (Janus.Float.zero Janus.Float.binary32 neg)) s := by
  cases neg <;> cfg_simp [FPZero] <;> decide

theorem integer_access0 (k : Int) (hk : 0 ≤ k) : (integer_access k 0 = 1#1) = (k % 2 = 1) := by
  simp only [integer_access, integer_subrange, Sail.get_slice_int]
  rw [access_eq _ 0 (by simp)]
  simp only [ofBool_eq_one, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt]
  apply propext
  simp
  omega

theorem fdiv_two (k : Int) (hk : 0 ≤ k) : fdiv_int k 2 = k / 2 := by
  have h1 : ¬ (k < 0) := by omega
  simp [fdiv_int, h1, Int.tdiv_eq_ediv_of_nonneg hk]



theorem integer_subrange_toNat (i : Int) (hi : Nat) (hi0 : 0 ≤ i) :
    (integer_subrange i (hi : Int) 0).toNat = i.toNat % 2 ^ (hi + 1) := by
  simp only [integer_subrange, Sail.get_slice_int, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    BitVec.toNat_ofInt]
  have e1 : ((hi : Int) - 0 + 1).toNat = hi + 1 := by omega
  have e2 : (hi : Int).toNat = hi := by omega
  simp only [Int.toNat_zero, e1, e2, Nat.shiftRight_zero, Nat.zero_add, Nat.sub_zero, Nat.mod_mod]
  rw [Int.toNat_emod hi0 (Int.natCast_nonneg _), Int.toNat_natCast]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]



theorem enc32_toNat (neg : Bool) (be k : Int) (hbe0 : 0 ≤ be) (hk : 0 ≤ k) :
    ((if neg then 1#1 else 0#1) +++ integer_subrange be 7 0 +++ integer_subrange k 22 0).toNat =
      (if neg then 2 ^ 31 else 0) + be.toNat % 2 ^ 8 * 2 ^ 23 + k.toNat % 2 ^ 23 := by
  simp only [BitVec.toNat_append]
  rw [show (7 : Int) = ((7 : Nat) : Int) from rfl, show (22 : Int) = ((22 : Nat) : Int) from rfl,
    integer_subrange_toNat be 7 hbe0, integer_subrange_toNat k 22 hk]
  rw [show ((7 : Nat) : Int).toNat - Int.toNat 0 + 1 = 8 by decide,
    show ((22 : Nat) : Int).toNat - Int.toNat 0 + 1 = 23 by decide]
  have b1 : be.toNat % 2 ^ (7 + 1) < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have b2 : k.toNat % 2 ^ (22 + 1) < 2 ^ 23 := Nat.mod_lt _ (by decide)
  rw [← Nat.shiftLeft_add_eq_or_of_lt b1]
  rw [← Nat.shiftLeft_add_eq_or_of_lt b2, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  cases neg <;> simp <;> omega


theorem frac_eq_zero (r s : Nat) : ((r : Rat) * 2 ^ (-(s : Int)) = 0) = (r = 0) := by
  apply propext; constructor
  · intro h; rcases Nat.eq_zero_or_pos r with hr | hr
    · exact hr
    · exact absurd h ((frac_ne_zero r s).mpr (by omega))
  · intro h; subst h; simp


end JanusASL.Proofs
