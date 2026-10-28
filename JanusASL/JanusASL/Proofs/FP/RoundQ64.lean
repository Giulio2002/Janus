import JanusASL.Proofs.FP.RoundQ

/-! # `FPRoundBase` (binary64) on a rational operand with a known binade -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxHeartbeats 20000000 in
theorem run_FPRoundBase64_q {s : SState} (hc : LinuxEL0Config s) (hism : (InStreamingMode ()).run s = .ok false s)
    (fpcr : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (q : Rat) (E : Int) (h1 : (2 : Rat) ^ E ≤ q) (h2 : q < (2 : Rat) ^ (E + 1))
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs)
    (hOF : Nat.testBit (rbq64 fpcr.toNat rm neg q E).2.1 2 = true → fpcr.getLsbD 10 = false)
    (hUF : Nat.testBit (rbq64 fpcr.toNat rm neg q E).2.1 3 = true → fpcr.getLsbD 11 = false)
    (hIX : Nat.testBit (rbq64 fpcr.toNat rm neg q E).2.1 4 = true → fpcr.getLsbD 12 = false) :
    (FPRoundBase__1 (if neg then -q else q) fpcr (aslRM rm) false true 64).run s =
      let o := rbq64 fpcr.toNat rm neg q E
      .ok o.1 (s.set .FPSR (xs ||| BitVec.ofNat 64 (o.2.1 ||| o.2.2))) := by
  have hp : (0 : Rat) < q := rat_lt_of_lt_of_le (rat_pos_zpow E) h1
  have hne0 : (if neg then -q else q) ≠ 0 := by
    cases neg
    · simp only [Bool.false_eq_true, ite_false]; exact fun h => Rat.lt_irrefl (h ▸ hp)
    · simp only [ite_true]; intro h
      have : q = 0 := by rw [← Rat.neg_neg q, h, Rat.neg_zero]
      exact Rat.lt_irrefl (this ▸ hp)
  have hne : (((if neg then -q else q)) != 0) = true := by simpa using hne0
  have hr' : (aslRM rm != .FPRounding_TIEAWAY) = true := by cases rm <;> first | decide | exact absurd rfl hrm
  have hA0 : 0 ≤ round_down (q * 2 ^ (52 - max E (-1022))) := round_down_nonneg_q _ (Rat.le_of_lt (Rat.mul_pos hp (rat_pos_zpow _)))
  have hAu0 : 0 ≤ round_down (q * 2 ^ (52 - E)) := round_down_nonneg_q _ (Rat.le_of_lt (Rat.mul_pos hp (rat_pos_zpow _)))
  have e0 : s = s.set .FPSR xs := (SState.set_same s .FPSR xs hx).symm
  rw [e0] at hism
  conv => lhs; rw [e0]
  simp only [rbq64] at hOF hUF hIX ⊢
  unfold FPRoundBase__1
  rw [run_SailME_run]
  cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, undefined_real, undefined_FPRounding,
    hne, hr', q_sign neg q hp, fpr_loop1q q E h1 h2, fpr_loop2q q E h1 h2,
    HaveAltFP, run_IsFeatureImplemented hc, run_IsFeatureImplemented (hc.set_FPSR xs), run_UsingAArch32 (hc.set_FPSR xs), sc64q, su64q,
    ipow11, ipow52, ipow53, fst_ite, snd_ite]
  simp only [get_AH, get_FZ, get_UFE, ofBool_eq_one] at *
  generalize sub_real (q * 2 ^ (52 - max E (-1022))) (to_real (round_down (q * 2 ^ (52 - max E (-1022))))) = Er at *
  generalize sub_real (q * 2 ^ (52 - E)) (to_real (round_down (q * 2 ^ (52 - E)))) = Eu at *
  generalize round_down (q * 2 ^ (52 - max E (-1022))) = A at *
  generalize round_down (q * 2 ^ (52 - E)) = Au at *
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




end JanusASL.Proofs
