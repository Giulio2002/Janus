import JanusASL.Proofs.FP.RoundEq
/-! # `FPRoundBase` (binary64) equals Janus' `fpRound`

The binary64 instance of FP/RoundBase and FP/RoundEq (F = 52, E = 11, minimum exponent -1022),
obtained from the binary32 development by substituting the format constants. -/
set_option linter.unusedSimpArgs false
namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem sc64 (m : Nat) (e : Int) :
    mult_real (if max ((Nat.log2 m : Int) + e + 1022 + 1) 0 = 0 then
        div_real ((m : Rat) * 2 ^ (-(Nat.log2 m : Int))) (real_power 2 (-1022 - ((Nat.log2 m : Int) + e)))
      else (m : Rat) * 2 ^ (-(Nat.log2 m : Int))) (real_power 2 52) =
      (m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)) := by
  simp only [mult_real, div_real, real_power]
  split
  · rw [Rat.div_def, ← Rat.zpow_neg, Rat.mul_assoc, Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat,
      ← Rat.zpow_add two_ne_zero_rat]
    congr 2; omega
  · rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
    congr 2; omega


theorem su64 (m : Nat) :
    mult_real ((m : Rat) * 2 ^ (-(Nat.log2 m : Int))) (real_power 2 52) =
      (m : Rat) * 2 ^ (52 - (Nat.log2 m : Int)) := by
  simp only [mult_real, real_power]
  rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
  congr 2; omega


theorem run_FPInfinity64 (s : SState) (neg : Bool) :
    (FPInfinity (if neg then 1#1 else 0#1) 64).run s = .ok (BitVec.ofNat 64 (Janus.Float.inf Janus.Float.binary64 neg)) s := by
  cases neg <;> cfg_simp [FPInfinity] <;> decide


theorem run_FPMaxNormal64 (s : SState) (neg : Bool) :
    (FPMaxNormal (if neg then 1#1 else 0#1) 64).run s =
      .ok (BitVec.ofNat 64 (Janus.Float.maxNormal Janus.Float.binary64 neg)) s := by
  cases neg <;> cfg_simp [FPMaxNormal] <;> decide


theorem run_FPZero64 (s : SState) (neg : Bool) :
    (FPZero (if neg then 1#1 else 0#1) 64).run s = .ok (BitVec.ofNat 64 (Janus.Float.zero Janus.Float.binary64 neg)) s := by
  cases neg <;> cfg_simp [FPZero] <;> decide


def rbTiny64 (ah : Bool) (rm : Janus.Float.RM) (neg : Bool) (E Au : Int) (Eu : Rat) : Bool :=
  let bu : Int := E + 1022 + 1
  let (bu', imu) : Int × Int :=
    if rbRU rm neg Eu Au then (if Au + 1 = 2 ^ 53 then (bu + 1, fdiv_int (Au + 1) 2) else (bu, Au + 1)) else (bu, Au)
  ah && decide (bu' < 1) && decide (imu ≠ 0)


def rbBE2_64 (ru : Bool) (E A : Int) : Int × Int :=
  let be : Int := max (E + 1022 + 1) 0
  if ru then
    (let b : Int := if A + 1 = 2 ^ 52 then 1 else be
     if A + 1 = 2 ^ 53 then (b + 1, fdiv_int (A + 1) 2) else (b, A + 1))
  else (be, A)


def rb64 (ah fz ufe : Bool) (rm : Janus.Float.RM) (neg : Bool) (E A Au : Int) (Er Eu : Rat) :
    BitVec 64 × Nat × Nat :=
  if !ah && fz && decide (E < -1022) then (BitVec.ofNat 64 (Janus.Float.zero Janus.Float.binary64 neg), 0, 8) else
  let be : Int := max (E + 1022 + 1) 0
  let uf1 : Bool := !ah && decide (be = 0) && (Er != 0 || ufe)
  let tinyA := rbTiny64 ah rm neg E Au Eu
  if tinyA && fz then (BitVec.ofNat 64 (Janus.Float.zero Janus.Float.binary64 neg), 16, 8) else
  let uf : Nat := if uf1 || (tinyA && (Er != 0 || ufe)) then 8 else 0
  let (be2, im2) : Int × Int := rbBE2_64 (rbRU rm neg Er A) E A
  let ovf : Prop := 2 ^ 11 - 1 ≤ be2
  let err : Rat := if ovf then 1 else Er
  (if ovf then BitVec.ofNat 64 (if rbOTI rm neg then Janus.Float.inf Janus.Float.binary64 neg
      else Janus.Float.maxNormal Janus.Float.binary64 neg)
    else BitVec.ofNat 64 ((if neg then 2 ^ 63 else 0) + be2.toNat % 2 ^ 11 * 2 ^ 52 + im2.toNat % 2 ^ 52),
    uf ||| (if ovf then 4 else 0) ||| (if err != 0 then 16 else 0), 0)


/-- `rb64` at the floors and errors `FPRoundBase` computes for `(-1)^neg * m * 2^e`. -/
def rb64Of (fpcr : Nat) (rm : Janus.Float.RM) (neg : Bool) (m : Nat) (e : Int) : BitVec 64 × Nat × Nat :=
  let dc : Int := e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)
  let du : Int := 52 - (Nat.log2 m : Int)
  rb64 (Janus.Arm64.FP.ah fpcr) (Janus.Arm64.FP.fz fpcr) (Janus.Arm64.FP.ufe fpcr) rm neg ((Nat.log2 m : Int) + e)
    (round_down ((m : Rat) * 2 ^ dc)) (round_down ((m : Rat) * 2 ^ du))
    (sub_real ((m : Rat) * 2 ^ dc) (to_real (round_down ((m : Rat) * 2 ^ dc))))
    (sub_real ((m : Rat) * 2 ^ du) (to_real (round_down ((m : Rat) * 2 ^ du))))


theorem run_ME_FPInfinity64 {β : Type} (s : SState) (neg : Bool) :
    (ExceptT.run (liftM (FPInfinity (if neg then 1#1 else 0#1) 64) : SailME β (BitVec 64))).run s =
      .ok (.ok (BitVec.ofNat 64 (Janus.Float.inf Janus.Float.binary64 neg))) s := by
  simp only [run_ME_lift, run_FPInfinity64]


theorem run_ME_FPMaxNormal64 {β : Type} (s : SState) (neg : Bool) :
    (ExceptT.run (liftM (FPMaxNormal (if neg then 1#1 else 0#1) 64) : SailME β (BitVec 64))).run s =
      .ok (.ok (BitVec.ofNat 64 (Janus.Float.maxNormal Janus.Float.binary64 neg))) s := by
  simp only [run_ME_lift, run_FPMaxNormal64]


theorem fdiv53 : fdiv_int 9007199254740992 2 = 4503599627370496 := by decide

theorem bits64_ite (c : Prop) [Decidable c] (a X : BitVec 64) (N : Nat) (h : X.toNat = N % 2 ^ 64) :
    (if c then a else X) = (if c then a else BitVec.ofNat 64 N) := by
  have : X = BitVec.ofNat 64 N := BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat])
  rw [this]


theorem isub10 (i : Int) (h : 0 ≤ i) : (integer_subrange i 10 0).toNat = i.toNat % 2048 :=
  integer_subrange_toNat i 10 h

theorem isub51 (i : Int) (h : 0 ≤ i) : (integer_subrange i 51 0).toNat = i.toNat % 4503599627370496 :=
  integer_subrange_toNat i 51 h


theorem enc64_fin (neg : Bool) (be k : Int) (w1 w2 : Nat) (hw1 : w1 = 11) (hw2 : w2 = 52) (x : BitVec 1)
    (hx : x = if neg then 1#1 else 0#1) (y z : Nat) (hy : y = be.toNat % 2048) (hz : z = k.toNat % 4503599627370496) :
    (x.toNat <<< w1 ||| y) <<< w2 ||| z =
      ((if neg then 9223372036854775808 else 0) + be.toNat % 2048 * 4503599627370496 + k.toNat % 4503599627370496) % 2 ^ 64 := by
  subst hw1 hw2 hx hy hz
  have b1 : be.toNat % 2048 < 2 ^ 11 := Nat.mod_lt _ (by decide)
  have b2 : k.toNat % 4503599627370496 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  rw [← Nat.shiftLeft_add_eq_or_of_lt b1, ← Nat.shiftLeft_add_eq_or_of_lt b2, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have : (if neg then 9223372036854775808 else 0) + be.toNat % 2048 * 4503599627370496 + k.toNat % 4503599627370496 < 2 ^ 64 := by
    cases neg <;> simp <;> omega
  rw [Nat.mod_eq_of_lt this]
  cases neg <;> simp <;> omega


theorem run_ME_infmax64 {β : Type} (s : SState) (neg : Bool) (c : Prop) [Decidable c] :
    (ExceptT.run (if c then liftM (FPInfinity (if neg then 1#1 else 0#1) 64)
        else liftM (FPMaxNormal (if neg then 1#1 else 0#1) 64) : SailME β (BitVec 64))).run s =
      .ok (.ok (if c then BitVec.ofNat 64 (Janus.Float.inf Janus.Float.binary64 neg)
        else BitVec.ofNat 64 (Janus.Float.maxNormal Janus.Float.binary64 neg))) s := by
  by_cases h : c <;> simp only [h, ite_true, ite_false, run_ME_FPInfinity64, run_ME_FPMaxNormal64]


theorem FPInf64_pure (neg : Bool) :
    FPInfinity (if neg then 1#1 else 0#1) 64 = pure (BitVec.ofNat 64 (Janus.Float.inf Janus.Float.binary64 neg)) :=
  funext fun s => run_FPInfinity64 s neg

theorem FPMax64_pure (neg : Bool) :
    FPMaxNormal (if neg then 1#1 else 0#1) 64 = pure (BitVec.ofNat 64 (Janus.Float.maxNormal Janus.Float.binary64 neg)) :=
  funext fun s => run_FPMaxNormal64 s neg

theorem FPZero64_pure (neg : Bool) :
    FPZero (if neg then 1#1 else 0#1) 64 = pure (BitVec.ofNat 64 (Janus.Float.zero Janus.Float.binary64 neg)) :=
  funext fun s => run_FPZero64 s neg

theorem FPInf64_0 : FPInfinity 0#1 64 = pure (BitVec.ofNat 64 (Janus.Float.inf Janus.Float.binary64 false)) :=
  FPInf64_pure false

theorem FPInf64_1 : FPInfinity 1#1 64 = pure (BitVec.ofNat 64 (Janus.Float.inf Janus.Float.binary64 true)) :=
  FPInf64_pure true

theorem FPMax64_0 : FPMaxNormal 0#1 64 = pure (BitVec.ofNat 64 (Janus.Float.maxNormal Janus.Float.binary64 false)) :=
  FPMax64_pure false

theorem FPMax64_1 : FPMaxNormal 1#1 64 = pure (BitVec.ofNat 64 (Janus.Float.maxNormal Janus.Float.binary64 true)) :=
  FPMax64_pure true

theorem FPZero64_0 : FPZero 0#1 64 = pure (BitVec.ofNat 64 (Janus.Float.zero Janus.Float.binary64 false)) :=
  FPZero64_pure false

theorem FPZero64_1 : FPZero 1#1 64 = pure (BitVec.ofNat 64 (Janus.Float.zero Janus.Float.binary64 true)) :=
  FPZero64_pure true


theorem ipow11 : (2 : Int) ^ (11 : Int) = 2048 := by decide

theorem ipow52 : (2 : Int) ^ (52 : Int) = 4503599627370496 := by decide

theorem ipow53 : (2 : Int) ^ (53 : Int) = 9007199254740992 := by decide

set_option hygiene false in
macro "rb64_leaf_simp" : tactic => `(tactic|
    simp (config := { contextual := true }) [run_ME_ifPE hc, run_ME_ifPE' hc, fpExcBit, hOF, hUF, hIX, hT,
      run_ME_ovf2 hc fpcr, run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, ofNat_ite,
      run_PE_set hc, run_FPZero64, run_readReg, fst_ite, snd_ite, Except.map, fdiv53, run_map, run_bind, run_pure,
      run_UsingAArch32_set hc])


set_option maxHeartbeats 20000000 in
theorem run_FPRoundBase64_rb {s : SState} (hc : LinuxEL0Config s) (hism : (InStreamingMode ()).run s = .ok false s)
    (fpcr : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (m : Nat) (hm : m ≠ 0) (e : Int)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs)
    (hOF : Nat.testBit (rb64Of fpcr.toNat rm neg m e).2.1 2 = true → fpcr.getLsbD 10 = false)
    (hUF : Nat.testBit (rb64Of fpcr.toNat rm neg m e).2.1 3 = true → fpcr.getLsbD 11 = false)
    (hIX : Nat.testBit (rb64Of fpcr.toNat rm neg m e).2.1 4 = true → fpcr.getLsbD 12 = false) :
    (FPRoundBase__1 (sval neg m e) fpcr (aslRM rm) false true 64).run s =
      let o := rb64Of fpcr.toNat rm neg m e
      .ok o.1 (s.set .FPSR (xs ||| BitVec.ofNat 64 (o.2.1 ||| o.2.2))) := by
  have hp := mag_pos m hm e
  have hne0 : sval neg m e ≠ 0 := by
    cases neg
    · simp only [sval, Bool.false_eq_true, ite_false]; exact fun h => Rat.lt_irrefl (h ▸ hp)
    · simp only [sval, ite_true]; intro h
      have : (m : Rat) * 2 ^ e = 0 := by rw [← Rat.neg_neg ((m : Rat) * 2 ^ e), h, Rat.neg_zero]
      exact Rat.lt_irrefl (this ▸ hp)
  have hne : ((sval neg m e) != 0) = true := by simpa using hne0
  have hr' : (aslRM rm != .FPRounding_TIEAWAY) = true := by cases rm <;> first | decide | exact absurd rfl hrm
  have hA0 := rd_nonneg m (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))
  have hAu0 := rd_nonneg m (52 - (Nat.log2 m : Int))
  have e0 : s = s.set .FPSR xs := (SState.set_same s .FPSR xs hx).symm
  rw [e0] at hism
  conv => lhs; rw [e0]
  simp only [rb64Of] at hOF hUF hIX ⊢
  unfold FPRoundBase__1
  rw [run_SailME_run]
  cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, undefined_real, undefined_FPRounding,
    hne, hr', sval_sign neg m hm e, fpr_loop1 m hm e, fpr_loop2 m hm e,
    HaveAltFP, run_IsFeatureImplemented hc, run_IsFeatureImplemented (hc.set_FPSR xs), run_UsingAArch32 (hc.set_FPSR xs), sc64, su64,
    ipow11, ipow52, ipow53, fst_ite, snd_ite]
  simp only [get_AH, get_FZ, get_UFE, ofBool_eq_one] at *
  generalize sub_real ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)))
    (to_real (round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))))) = Er at *
  generalize sub_real ((m : Rat) * 2 ^ (52 - (Nat.log2 m : Int)))
    (to_real (round_down ((m : Rat) * 2 ^ (52 - (Nat.log2 m : Int))))) = Eu at *
  generalize round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))) = A at *
  generalize round_down ((m : Rat) * 2 ^ (52 - (Nat.log2 m : Int))) = Au at *
  generalize (Nat.log2 m : Int) + e = E at *
  simp only [Janus.Arm64.FP.ah, Janus.Arm64.FP.fz, Janus.Arm64.FP.ufe, Janus.Arm64.FP.fpcrBit] at *
  have hT0 : ∀ rm, rbTiny64 false rm neg E Au Eu = false := fun rm => by simp [rbTiny64]
  by_cases hT : rbTiny64 true rm neg E Au Eu = true
  all_goals cases rm
  all_goals try exact absurd rfl hrm
  all_goals
    by_cases hAH : fpcr.toNat / 2 ^ 1 % 2 = 1 <;> by_cases hFZ : fpcr.toNat / 2 ^ 24 % 2 = 1 <;>
      by_cases hUFE : fpcr.toNat / 2 ^ 11 % 2 = 1 <;> by_cases hE : E < -1022
  all_goals
    fp_simp [aslRM, rbRU, rbOTI, rbTiny64, rbBE2_64, hAH, hFZ, hUFE, hism, hE, hT0, testBit_ite, Nat.testBit_or, upd_bit3,
      fst_ite, snd_ite, ipow11, ipow52, ipow53] at hT
  all_goals
    fp_simp [aslRM, rb64, rbRU, rbOTI, rbTiny64, rbBE2_64, hAH, hFZ, hUFE, hism, hE, hT0, run_ME_bind, run_ME_lift, run_ME_pure,
        run_ME_map, run_ME_throw, testBit_ite, Nat.testBit_or, upd_bit3, fst_ite, snd_ite, ipow11, ipow52, ipow53,
        FPInf64_pure, FPMax64_pure, FPZero64_pure, FPInf64_0, FPInf64_1, FPMax64_0, FPMax64_1, FPZero64_0, FPZero64_1,
        liftM_pure_ME, ite_pure_ME]
      at hOF hUF hIX ⊢
  all_goals try simp only [ite_t hT, hT, true_implies, false_implies, imp_false, not_true_eq_false,
    not_false_eq_true, Classical.not_not, and_true, true_and, and_false, false_and] at hOF hUF hIX ⊢
  all_goals try (have hT' := fun (h : _ ∧ ¬ _) => h.2 (hT h.1)
                 simp only [ite_f hT', eq_true hT, eq_false hT', true_implies, false_and, and_false, false_or,
                   or_false, ↓reduceIte] at hOF hUF hIX ⊢)
  all_goals
    rb64_leaf_simp
  all_goals try (rw [run_readReg_FPSR_set]; rb64_leaf_simp)
  all_goals try refine ⟨?_, ?_⟩
  all_goals try (first
         | rfl
         | (apply bits64_ite
            erw [BitVec.toNat_append, BitVec.toNat_append]
            refine enc64_fin neg _ _ _ _ (by decide) (by decide) _ rfl _ _ (isub10 _ ?_) (isub51 _ ?_)
            all_goals (repeat' split) <;> first | omega | (apply fdiv_nonneg; omega) | decide)
         | (congr 1
            simp only [ofNat_or, ofNat_ite, BitVec.or_assoc, Nat.or_zero, BitVec.ofNat_eq_ofNat, BitVec.or_zero]
            try ac_rfl))


theorem A64_bounds (m : Nat) (hm : m ≠ 0) (e : Int) :
    0 ≤ round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))) ∧
    (-1022 ≤ (Nat.log2 m : Int) + e →
      2 ^ 52 ≤ round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))) ∧
      round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))) < 2 ^ 53) ∧
    ((Nat.log2 m : Int) + e < -1022 →
      round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))) < 2 ^ 52) := by
  have h1 : 2 ^ Nat.log2 m ≤ m := Nat.log2_self_le hm
  have h2 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  refine ⟨rd_nonneg _ _, ?_, ?_⟩
  · intro hn
    by_cases hd : 0 ≤ e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)
    · rw [((rd_split m _).1 hd).1]
      have ht : (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)).toNat = 52 - Nat.log2 m := by omega
      rw [ht]
      obtain ⟨b1, b2⟩ := nb_mul m (Nat.log2 m) (52 - Nat.log2 m) h1 h2
      rw [show Nat.log2 m + (52 - Nat.log2 m) = 52 by omega] at b1
      rw [show Nat.log2 m + 1 + (52 - Nat.log2 m) = 53 by omega] at b2
      constructor <;> omega
    · rw [((rd_split m _).2 (by omega)).1]
      have ht : (-(e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))).toNat = Nat.log2 m - 52 := by omega
      rw [ht]
      obtain ⟨b1, b2⟩ := nb_div m (Nat.log2 m) (Nat.log2 m - 52) h1 h2 (by omega)
      rw [show Nat.log2 m - (Nat.log2 m - 52) = 52 by omega] at b1
      rw [show Nat.log2 m + 1 - (Nat.log2 m - 52) = 53 by omega] at b2
      constructor <;> omega
  · intro hs
    by_cases hd : 0 ≤ e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)
    · rw [((rd_split m _).1 hd).1]
      obtain ⟨_, b2⟩ := nb_mul m (Nat.log2 m) (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)).toNat h1 h2
      have : 2 ^ (Nat.log2 m + 1 + (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)).toNat) ≤ 2 ^ 52 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · rw [((rd_split m _).2 (by omega)).1]
      have : m / 2 ^ (-(e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))).toNat < 2 ^ 52 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
        exact Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))
      omega


theorem Au64_bounds (m : Nat) (hm : m ≠ 0) :
    2 ^ 52 ≤ round_down ((m : Rat) * 2 ^ (52 - (Nat.log2 m : Int))) ∧
      round_down ((m : Rat) * 2 ^ (52 - (Nat.log2 m : Int))) < 2 ^ 53 := by
  have h1 : 2 ^ Nat.log2 m ≤ m := Nat.log2_self_le hm
  have h2 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  by_cases hd : 0 ≤ 52 - (Nat.log2 m : Int)
  · rw [((rd_split m _).1 hd).1]
    have ht : (52 - (Nat.log2 m : Int)).toNat = 52 - Nat.log2 m := by omega
    rw [ht]
    obtain ⟨b1, b2⟩ := nb_mul m (Nat.log2 m) (52 - Nat.log2 m) h1 h2
    rw [show Nat.log2 m + (52 - Nat.log2 m) = 52 by omega] at b1
    rw [show Nat.log2 m + 1 + (52 - Nat.log2 m) = 53 by omega] at b2
    constructor <;> omega
  · rw [((rd_split m _).2 (by omega)).1]
    have ht : (-(52 - (Nat.log2 m : Int))).toNat = Nat.log2 m - 52 := by omega
    rw [ht]
    obtain ⟨b1, b2⟩ := nb_div m (Nat.log2 m) (Nat.log2 m - 52) h1 h2 (by omega)
    rw [show Nat.log2 m - (Nat.log2 m - 52) = 52 by omega] at b1
    rw [show Nat.log2 m + 1 - (Nat.log2 m - 52) = 53 by omega] at b2
    constructor <;> omega


def ju64 (ru : Bool) (E A : Int) : Nat × Int :=
  let k : Nat := if ru then A.toNat + 1 else A.toNat
  let q : Int := max E (-1022) - 52
  if k = 2 ^ 53 then (k / 2, q + 1) else (k, q)


theorem roundUnits64_rd (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (m : Nat) (e : Int) :
    Janus.Float.roundUnits Janus.Float.binary64 rm neg m e =
      ju64 (rbRU rm neg (sub_real ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)))
          (to_real (round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))))))
          (round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)))))
        ((Nat.log2 m : Int) + e) (round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)))) := by
  unfold Janus.Float.roundUnits ju64
  simp only [roundAt_rd rm hrm neg m e (max ((Nat.log2 m : Int) + e) Janus.Float.binary64.emin -
    (Janus.Float.binary64.fbits : Int)) (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)) (by
      simp only [Janus.Float.binary64, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias, Janus.Float.Fmt.fbits]; omega)]
  simp only [Janus.Float.binary64, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias, Janus.Float.Fmt.fbits]
  rfl


theorem fdiv53b : fdiv_int (2 ^ 53) 2 = 2 ^ 52 := by decide


theorem rbBE2_64_biased (ru : Bool) (E A : Int) (hA0 : 0 ≤ A) (hAn : -1022 ≤ E → 2 ^ 52 ≤ A ∧ A < 2 ^ 53)
    (hAs : E < -1022 → A < 2 ^ 52) :
    (rbBE2_64 ru E A).1 = Janus.Float.biasedExp Janus.Float.binary64 (ju64 ru E A).1 (ju64 ru E A).2 ∧
      (rbBE2_64 ru E A).2.toNat % 2 ^ 52 = (ju64 ru E A).1 % 2 ^ 52 ∧ 0 ≤ (rbBE2_64 ru E A).1 := by
  unfold rbBE2_64 ju64 Janus.Float.biasedExp
  simp only [Janus.Float.binary64, Janus.Float.Fmt.bias, Janus.Float.Fmt.fbits]
  by_cases hE : E < -1022
  · have := hAs hE
    cases ru <;> simp only [Bool.false_eq_true, ite_true, ite_false]
    · have h1 : ¬ A.toNat = 2 ^ 53 := by omega
      simp only [h1, ite_false]
      refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial
    · by_cases h23 : A + 1 = 2 ^ 52
      · have h1 : ¬ A.toNat + 1 = 2 ^ 53 := by omega
        have h2 : ¬ A + 1 = 2 ^ 53 := by omega
        simp only [h1, h2, h23, ite_true, ite_false]
        refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial
      · have h1 : ¬ A.toNat + 1 = 2 ^ 53 := by omega
        have h2 : ¬ A + 1 = 2 ^ 53 := by omega
        simp only [h1, h2, h23, ite_true, ite_false]
        refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial
  · have := hAn (by omega)
    cases ru <;> simp only [Bool.false_eq_true, ite_true, ite_false]
    · have h1 : ¬ A.toNat = 2 ^ 53 := by omega
      simp only [h1, ite_false]
      refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial
    · have h23 : ¬ A + 1 = 2 ^ 52 := by omega
      by_cases h24 : A + 1 = 2 ^ 53
      · have h1 : A.toNat + 1 = 2 ^ 53 := by omega
        simp only [h1, h24, h23, ite_true, ite_false, fdiv53b]
        refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial
      · have h1 : ¬ A.toNat + 1 = 2 ^ 53 := by omega
        simp only [h1, h24, h23, ite_true, ite_false]
        refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial


theorem rbTiny64_eq (ah : Bool) (rm : Janus.Float.RM) (neg : Bool) (E Au : Int) (Eu : Rat)
    (hAu1 : 2 ^ 52 ≤ Au) (hAu2 : Au < 2 ^ 53) :
    rbTiny64 ah rm neg E Au Eu = (ah && decide ((if (if rbRU rm neg Eu Au then Au.toNat + 1 else Au.toNat) =
      2 ^ 53 then E + 1 else E) < -1022)) := by
  unfold rbTiny64
  rw [Bool.eq_iff_iff]
  cases rbRU rm neg Eu Au <;> cases ah <;>
    simp only [Bool.false_eq_true, ite_true, ite_false, Bool.false_and, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq, fdiv53b, Bool.false_eq_true, iff_self]
  · omega
  · by_cases h : Au + 1 = 2 ^ 53
    · have h1 : Au.toNat + 1 = 2 ^ 53 := by omega
      simp only [h, h1, ite_true, fdiv53b]; omega
    · have h1 : ¬ Au.toNat + 1 = 2 ^ 53 := by omega
      simp only [h, h1, ite_false]; omega


set_option maxHeartbeats 20000000 in
theorem rb64Of_eq (fpcr : Nat) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (m : Nat) (hm : m ≠ 0) (e : Int) :
    rb64Of fpcr rm neg m e =
      (BitVec.ofNat 64 (Janus.Arm64.FP.fpRound Janus.Float.binary64 fpcr rm neg m e).1,
        (Janus.Arm64.FP.fpRound Janus.Float.binary64 fpcr rm neg m e).2.proc,
        (Janus.Arm64.FP.fpRound Janus.Float.binary64 fpcr rm neg m e).2.direct) := by
  obtain ⟨hA0, hAn, hAs⟩ := A64_bounds m hm e
  obtain ⟨hAu1, hAu2⟩ := Au64_bounds m hm
  have hq1 := roundAt_rd rm hrm neg m e (max ((Nat.log2 m : Int) + e) Janus.Float.binary64.emin -
    (Janus.Float.binary64.fbits : Int)) (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)) (by
      simp only [Janus.Float.binary64, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias, Janus.Float.Fmt.fbits]; omega)
  have hq2 := roundAt_rd rm hrm neg m e ((Nat.log2 m : Int) + e - (Janus.Float.binary64.fbits : Int))
    (52 - (Nat.log2 m : Int)) (by simp only [Janus.Float.binary64, Janus.Float.Fmt.fbits]; omega)
  simp only [rb64Of, Janus.Arm64.FP.fpRound, Janus.Float.round, hq1, hq2, roundUnits64_rd rm hrm, rb64, bne_ite1,
    rbOTI_eq rm hrm, rbTiny64_eq _ _ _ _ _ _ hAu1 hAu2]
  clear hq1 hq2
  generalize sub_real ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52)))
    (to_real (round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))))) = Er at *
  generalize sub_real ((m : Rat) * 2 ^ (52 - (Nat.log2 m : Int)))
    (to_real (round_down ((m : Rat) * 2 ^ (52 - (Nat.log2 m : Int))))) = Eu at *
  generalize round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-1022) - 52))) = A at *
  generalize round_down ((m : Rat) * 2 ^ (52 - (Nat.log2 m : Int))) = Au at *
  generalize (Nat.log2 m : Int) + e = E at *
  generalize rbRU rm neg Er A = ru at *
  obtain ⟨hB, hM, hB0⟩ := rbBE2_64_biased ru E A hA0 hAn hAs
  generalize rbBE2_64 ru E A = P at *
  generalize ju64 ru E A = U at *
  generalize Janus.Float.biasedExp Janus.Float.binary64 U.1 U.2 = B at *
  obtain ⟨b2, i2⟩ := P
  simp only at hB hM hB0
  subst hB
  generalize (Er != 0) = er at *
  generalize Janus.Arm64.FP.ah fpcr = ah at *
  generalize Janus.Arm64.FP.fz fpcr = fz at *
  generalize Janus.Arm64.FP.ufe fpcr = ufe at *
  have hmax : (max (E + 1022 + 1) 0 = 0) = (E < -1022) := by apply propext; omega
  simp only [Janus.Float.binary64, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias, Janus.Float.Fmt.fbits,
    Janus.Float.Fmt.expMax, Janus.Float.pack, Janus.Float.Fmt.signBit, Janus.Arm64.FP.raise, Janus.Arm64.FP.UFC,
    Janus.Arm64.FP.OFC, Janus.Arm64.FP.IXC, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Int.reducePow,
    Int.reduceNeg, Int.reduceSub, Int.reduceAdd, Int.natCast_pow, ge_iff_le, Int.cast_ofNat_Int, Int.reduceToNat,
    hmax] at *
  by_cases hO : (2047 : Int) ≤ b2 <;> by_cases hE : E < -1022 <;> by_cases hT : E + 1 < -1022 <;>
    cases ah <;> cases fz <;> cases ufe <;> cases er <;>
    simp only [hO, hE, hT, ite_true, ite_false, decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false, Bool.true_or, Bool.false_or, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, apply_ite Janus.Float.Rounded.bits, apply_ite Janus.Float.Rounded.inexact,
      apply_ite Janus.Float.Rounded.overflow, apply_ite Janus.Float.Rounded.tinyBefore,
      apply_ite Janus.Float.Rounded.tinyAfter, apply_ite Janus.Float.Rounded.roundErr,
      apply_ite Janus.Arm64.FP.Exc.proc, apply_ite Janus.Arm64.FP.Exc.direct, exc_append_proc, exc_append_direct,
      Prod.mk.injEq, Nat.reduceOr, Nat.or_zero, Nat.zero_or, apply_ite Prod.fst, apply_ite Prod.snd]
  all_goals cases hR : rbRU rm neg Eu Au
  all_goals try simp only [hR, ite_true, ite_false, Bool.false_eq_true, decide_eq_true_eq]
  all_goals try simp only [hE, hT, hO, decide_true, decide_false, ite_true, ite_false, Bool.true_and, Bool.false_and,
    and_true, true_and, and_false, false_and, or_true, or_false, true_or, false_or, not_true_eq_false,
    not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false, Nat.reduceOr, Prod.mk.injEq]
  all_goals try (exact congrArg (BitVec.ofNat 64) (by omega))
  all_goals try refine ⟨?_, ?_, ?_⟩
  all_goals try refine ⟨?_, ?_⟩
  all_goals (repeat' split)
  all_goals try simp only [decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at *
  all_goals try simp only [Nat.reduceOr, Nat.or_zero, Nat.zero_or] at *
  all_goals first
    | with_reducible rfl
    | (exfalso; omega)
    | (exact congrArg (BitVec.ofNat 64) (by omega))
    | (simp only [Prod.mk.injEq, and_true]; exact congrArg (BitVec.ofNat 64) (by omega))
    | skip


theorem run_FPRoundBase64 {s : SState} (hc : LinuxEL0Config s) (hism : (InStreamingMode ()).run s = .ok false s)
    (fpcr : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (m : Nat) (hm : m ≠ 0) (e : Int)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs)
    (hOF : Nat.testBit (Janus.Arm64.FP.fpRound Janus.Float.binary64 fpcr.toNat rm neg m e).2.proc 2 = true →
      fpcr.getLsbD 10 = false)
    (hUF : Nat.testBit (Janus.Arm64.FP.fpRound Janus.Float.binary64 fpcr.toNat rm neg m e).2.proc 3 = true →
      fpcr.getLsbD 11 = false)
    (hIX : Nat.testBit (Janus.Arm64.FP.fpRound Janus.Float.binary64 fpcr.toNat rm neg m e).2.proc 4 = true →
      fpcr.getLsbD 12 = false) :
    (FPRoundBase__1 (sval neg m e) fpcr (aslRM rm) false true 64).run s =
      let r := Janus.Arm64.FP.fpRound Janus.Float.binary64 fpcr.toNat rm neg m e
      .ok (BitVec.ofNat 64 r.1) (s.set .FPSR (xs ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have h := rb64Of_eq fpcr.toNat rm hrm neg m hm e
  rw [run_FPRoundBase64_rb hc hism fpcr rm hrm neg m hm e hx (by rw [h]; exact hOF) (by rw [h]; exact hUF)
    (by rw [h]; exact hIX), h]


end JanusASL.Proofs
