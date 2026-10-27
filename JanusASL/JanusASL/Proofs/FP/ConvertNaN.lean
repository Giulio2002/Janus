import JanusASL.Proofs.FP.CvtPrim

/-! # `FPConvertNaN` against Janus' `convertNaN` (single to double, double to single) -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem toNat_cat3 (a : BitVec 1) (o : BitVec 12) (e : BitVec 22) (z : BitVec 29) :
    (((a +++ o) +++ (e +++ z) : BitVec (1 + 12 + (22 + 29)))).toNat =
      a.toNat * 2 ^ 63 + o.toNat * 2 ^ 51 + e.toNat * 2 ^ 29 + z.toNat := by
  simp only [BitVec.toNat_append]
  have b1 : o.toNat < 2 ^ 12 := o.isLt
  have b2 : e.toNat < 2 ^ 22 := e.isLt
  have b3 : z.toNat < 2 ^ 29 := z.isLt
  have b0 : a.toNat < 2 := a.isLt
  have s1 := Nat.shiftLeft_add_eq_or_of_lt (a := a.toNat) b1
  have s2 := Nat.shiftLeft_add_eq_or_of_lt (a := e.toNat) b3
  have c2 : e.toNat <<< 29 + z.toNat < 2 ^ 51 := by simp only [Nat.shiftLeft_eq]; omega
  have s3 := Nat.shiftLeft_add_eq_or_of_lt (a := a.toNat <<< 12 + o.toNat) c2
  rw [← s1, ← s2, ← s3]
  simp only [Nat.shiftLeft_eq]; omega

set_option maxRecDepth 100000 in
theorem cnan_3264 (op : BitVec 32) (s : SState) :
    (FPConvertNaN op 64).run s = .ok (BitVec.ofNat 64 (Janus.Arm64.FP.convertNaN Janus.Float.binary32 Janus.Float.binary64 op.toNat)) s := by
  unfold FPConvertNaN
  cfg_simp [run_undefined_bitvector, run_sail_assert_true, Sail.BitVec.length]
  congr 1
  apply BitVec.eq_of_toNat_eq
  refine (toNat_cat3 _ _ _ _).trans ?_
  rw [access_eq op 31 (by decide), extractLsb_toNat']
  have hOnes : (Ones : BitVec 12).toNat = 2 ^ 12 - 1 := by simp [Ones, sail_ones]
  have hZ : (Zeros : BitVec 29).toNat = 0 := by simp [Zeros, BitVec.zero]
  rw [hOnes, hZ, BitVec.toNat_ofNat]
  have hop : op.toNat < 2 ^ 32 := op.isLt
  unfold Janus.Arm64.FP.convertNaN Janus.Float.pack
  generalize op.toNat = n at hop ⊢
  have hsg : Janus.Float.signOf Janus.Float.binary32 n = decide (n / 2 ^ 31 % 2 = 1) := rfl
  rw [hsg]
  simp only [Janus.Float.binary32, Janus.Float.binary64, Janus.Float.Fmt.quietBit, Janus.Float.Fmt.expMax]
  have hb : (BitVec.ofBool (decide (n / 2 ^ 31 % 2 = 1))).toNat = n / 2 ^ 31 % 2 := by
    by_cases h : n / 2 ^ 31 % 2 = 1
    · simp only [h, decide_true]; rfl
    · have : n / 2 ^ 31 % 2 = 0 := by omega
      simp only [h, decide_false, this]; rfl
  rw [hb]
  simp only [decide_eq_true_eq, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.pow_zero, Nat.div_one]
  simp only [Janus.Float.Fmt.signBit, Nat.reducePow, Nat.reduceAdd]
  split <;> omega

theorem toNat_cat2 (a : BitVec 1) (o : BitVec 9) (e : BitVec 22) :
    (((a +++ o) +++ e : BitVec (1 + 9 + 22))).toNat = a.toNat * 2 ^ 31 + o.toNat * 2 ^ 22 + e.toNat := by
  simp only [BitVec.toNat_append]
  have b1 : o.toNat < 2 ^ 9 := o.isLt
  have b2 : e.toNat < 2 ^ 22 := e.isLt
  have b0 : a.toNat < 2 := a.isLt
  have s1 := Nat.shiftLeft_add_eq_or_of_lt (a := a.toNat) b1
  have c2 : (a.toNat <<< 9 + o.toNat) <<< 22 + e.toNat = ((a.toNat <<< 9 + o.toNat) <<< 22) ||| e.toNat :=
    Nat.shiftLeft_add_eq_or_of_lt (a := a.toNat <<< 9 + o.toNat) b2
  rw [← s1, ← c2]
  simp only [Nat.shiftLeft_eq]; omega

set_option maxRecDepth 100000 in
theorem cnan_6432 (op : BitVec 64) (s : SState) :
    (FPConvertNaN op 32).run s = .ok (BitVec.ofNat 32 (Janus.Arm64.FP.convertNaN Janus.Float.binary64 Janus.Float.binary32 op.toNat)) s := by
  unfold FPConvertNaN
  cfg_simp [run_undefined_bitvector, run_sail_assert_true, Sail.BitVec.length]
  congr 1
  apply BitVec.eq_of_toNat_eq
  refine (toNat_cat2 _ _ _).trans ?_
  rw [access_eq op 63 (by decide), extractLsb_toNat', extractLsb_toNat']
  have hOnes : (Ones : BitVec 9).toNat = 2 ^ 9 - 1 := by simp [Ones, sail_ones]
  rw [hOnes, BitVec.toNat_ofNat]
  have hop : op.toNat < 2 ^ 64 := op.isLt
  unfold Janus.Arm64.FP.convertNaN Janus.Float.pack
  generalize op.toNat = n at hop ⊢
  have hsg : Janus.Float.signOf Janus.Float.binary64 n = decide (n / 2 ^ 63 % 2 = 1) := rfl
  rw [hsg]
  simp only [Janus.Float.binary32, Janus.Float.binary64, Janus.Float.Fmt.quietBit, Janus.Float.Fmt.expMax]
  have hb : (BitVec.ofBool (decide (n / 2 ^ 63 % 2 = 1))).toNat = n / 2 ^ 63 % 2 := by
    by_cases h : n / 2 ^ 63 % 2 = 1
    · simp only [h, decide_true]; rfl
    · have : n / 2 ^ 63 % 2 = 0 := by omega
      simp only [decide_false, this]; rfl
  rw [hb]
  simp only [decide_eq_true_eq, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.pow_zero, Nat.div_one]
  simp only [Janus.Float.Fmt.signBit, Nat.reducePow, Nat.reduceAdd]
  split <;> omega

end JanusASL.Proofs
