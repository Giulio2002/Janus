import JanusASL.Proofs.FP.Round64

/-! # `FPRoundBase` on a rational operand with a known binade

`run_FPRoundBase32_q` / `run_FPRoundBase64_q`: for a positive rational `q` with `2^E ≤ q < 2^(E+1)`,
`FPRoundBase(±q)` is `rb32`/`rb64` of the binade `E`, the scaled floors and errors of `q`. The dyadic theorems
(`run_FPRoundBase32_rb`) are the case `q = m * 2^e`. -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem rat_pos_zpow (E : Int) : (0 : Rat) < (2 : Rat) ^ E := Rat.zpow_pos two_pos_rat

theorem q_lt_pow (q : Rat) (E : Int) (h2 : q < (2 : Rat) ^ (E + 1)) (a : Int) :
    q * 2 ^ a < (2 : Rat) ^ (E + 1 + a) := by
  rw [Rat.zpow_add two_ne_zero_rat]
  exact Rat.mul_lt_mul_of_pos_right h2 (rat_pos_zpow _)

theorem pow_le_q (q : Rat) (E : Int) (h1 : (2 : Rat) ^ E ≤ q) (a : Int) :
    (2 : Rat) ^ (E + a) ≤ q * 2 ^ a := by
  rw [Rat.zpow_add two_ne_zero_rat]
  exact Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (rat_pos_zpow _))

theorem q_counts (q : Rat) (E : Int) (h1 : (2 : Rat) ^ E ≤ q) (h2 : q < (2 : Rat) ^ (E + 1)) :
    (∀ i < (-E).toNat, q * 2 ^ (i : Int) < 1) ∧ ¬ (q * 2 ^ ((-E).toNat : Int) < 1) ∧
    (∀ i < E.toNat, 2 ≤ q * 2 ^ ((-E).toNat : Int) * 2 ^ (-(i : Int))) ∧
    ¬ (2 ≤ q * 2 ^ ((-E).toNat : Int) * 2 ^ (-(E.toNat : Int))) := by
  have rw2 : ∀ a b : Int, q * 2 ^ a * 2 ^ b = q * 2 ^ (a + b) := fun a b => by
    rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
  have mono : ∀ {a b : Int}, a ≤ b → (2 : Rat) ^ a ≤ (2 : Rat) ^ b := fun h => zpow_le_zpow h
  refine ⟨fun i hi => ?_, ?_, fun i hi => ?_, ?_⟩
  · exact rat_lt_of_lt_of_le (q_lt_pow q E h2 i) (by rw [show (1 : Rat) = 2 ^ (0 : Int) by rfl]; exact mono (by omega))
  · intro hlt
    have := rat_lt_of_le_of_lt (pow_le_q q E h1 ((-E).toNat : Int)) hlt
    rw [show (1 : Rat) = 2 ^ (0 : Int) by rfl] at this
    exact (Rat.not_le.mpr this) (mono (by omega))
  · rw [rw2]
    exact Rat.le_trans (by rw [show (2 : Rat) = 2 ^ (1 : Int) by rfl]; exact mono (by omega))
      (pow_le_q q E h1 _)
  · rw [rw2]; intro hge
    have := rat_lt_of_le_of_lt hge (q_lt_pow q E h2 (((-E).toNat : Int) + -(E.toNat : Int)))
    rw [show (2 : Rat) = 2 ^ (1 : Int) by rfl] at this
    exact (Rat.not_le.mpr this) (mono (by omega))

theorem fpr_loop1q {β : Type} (q : Rat) (E : Int) (h1 : (2 : Rat) ^ E ≤ q) (h2 : q < (2 : Rat) ^ (E + 1)) :
    (forIn (m := SailME β) Lean.Loop.mk ((0 : Int), q) fun _ (r : Int × real) =>
        if lt_real r.2 1 = true then pure (ForInStep.yield (r.1 - 1, mult_real r.2 2)) else pure (ForInStep.done r)) =
      pure (-(((-E).toNat : Nat) : Int), q * 2 ^ (((-E).toNat : Nat) : Int)) := by
  obtain ⟨c1, c2, _, _⟩ := q_counts q E h1 h2
  exact loop_dbl _ (fun r => by by_cases h : r.2 < 1 <;> simp [lt_real, mult_real, h]) _ _ c1 c2

theorem fpr_loop2q {β : Type} (q : Rat) (E : Int) (h1 : (2 : Rat) ^ E ≤ q) (h2 : q < (2 : Rat) ^ (E + 1)) :
    (forIn (m := SailME β) Lean.Loop.mk (-max (-E) 0, q * 2 ^ max (-E) 0) fun _ (r : Int × real) =>
        if gteq_real r.2 2 = true then pure (ForInStep.yield (r.1 + 1, div_real r.2 2)) else pure (ForInStep.done r)) =
      pure (E, q * 2 ^ (-E)) := by
  obtain ⟨_, _, c3, c4⟩ := q_counts q E h1 h2
  have e1 : max (-E) 0 = (((-E).toNat : Nat) : Int) := by omega
  rw [e1, loop_half _ (fun r => by by_cases h : 2 ≤ r.2 <;> simp [gteq_real, div_real, h]) _ _ _ c3 c4]
  congr 2
  · omega
  · rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
    congr 2; omega

theorem sc32q (q : Rat) (E : Int) :
    mult_real (if max (E + 126 + 1) 0 = 0 then div_real (q * 2 ^ (-E)) (real_power 2 (-126 - E)) else q * 2 ^ (-E))
      (real_power 2 23) = q * 2 ^ (23 - max E (-126)) := by
  simp only [mult_real, div_real, real_power]
  split
  · rw [Rat.div_def, ← Rat.zpow_neg, Rat.mul_assoc, Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat,
      ← Rat.zpow_add two_ne_zero_rat]
    congr 2; omega
  · rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
    congr 2; omega

theorem su32q (q : Rat) (E : Int) :
    mult_real (q * 2 ^ (-E)) (real_power 2 23) = q * 2 ^ (23 - E) := by
  simp only [mult_real, real_power]
  rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
  congr 2; omega

theorem q_sign (neg : Bool) (q : Rat) (hq : 0 < q) :
    (if lt_real (if neg then -q else q) 0 = true then (neg_real (if neg then -q else q), 1#1)
      else ((if neg then -q else q), 0#1)) = (q, if neg then 1#1 else 0#1) := by
  cases neg
  · have : ¬ q < 0 := Rat.not_lt.mpr (Rat.le_of_lt hq)
    simp [lt_real, this]
  · have : -q < 0 := by have := Rat.neg_lt_neg hq; rwa [Rat.neg_zero] at this
    simp [lt_real, this, neg_real]

theorem round_down_nonneg_q (x : Rat) (hx : 0 ≤ x) : 0 ≤ round_down x := by
  simp only [round_down]
  have := Rat.le_floor_iff (x := 0) (a := x)
  exact this.mpr (by simpa using hx)

/-- `rb32` at the floors and errors `FPRoundBase` computes for the rational `q` in the binade `E`. -/
def rbq32 (fpcr : Nat) (rm : Janus.Float.RM) (neg : Bool) (q : Rat) (E : Int) : BitVec 32 × Nat × Nat :=
  rb32 (Janus.Arm64.FP.ah fpcr) (Janus.Arm64.FP.fz fpcr) (Janus.Arm64.FP.ufe fpcr) rm neg E
    (round_down (q * 2 ^ (23 - max E (-126)))) (round_down (q * 2 ^ (23 - E)))
    (sub_real (q * 2 ^ (23 - max E (-126))) (to_real (round_down (q * 2 ^ (23 - max E (-126))))))
    (sub_real (q * 2 ^ (23 - E)) (to_real (round_down (q * 2 ^ (23 - E)))))

/-- `rb64` at the floors and errors `FPRoundBase` computes for the rational `q` in the binade `E`. -/
def rbq64 (fpcr : Nat) (rm : Janus.Float.RM) (neg : Bool) (q : Rat) (E : Int) : BitVec 64 × Nat × Nat :=
  rb64 (Janus.Arm64.FP.ah fpcr) (Janus.Arm64.FP.fz fpcr) (Janus.Arm64.FP.ufe fpcr) rm neg E
    (round_down (q * 2 ^ (52 - max E (-1022)))) (round_down (q * 2 ^ (52 - E)))
    (sub_real (q * 2 ^ (52 - max E (-1022))) (to_real (round_down (q * 2 ^ (52 - max E (-1022))))))
    (sub_real (q * 2 ^ (52 - E)) (to_real (round_down (q * 2 ^ (52 - E)))))

theorem sc64q (q : Rat) (E : Int) :
    mult_real (if max (E + 1022 + 1) 0 = 0 then div_real (q * 2 ^ (-E)) (real_power 2 (-1022 - E)) else q * 2 ^ (-E))
      (real_power 2 52) = q * 2 ^ (52 - max E (-1022)) := by
  simp only [mult_real, div_real, real_power]
  split
  · rw [Rat.div_def, ← Rat.zpow_neg, Rat.mul_assoc, Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat,
      ← Rat.zpow_add two_ne_zero_rat]
    congr 2; omega
  · rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
    congr 2; omega

theorem su64q (q : Rat) (E : Int) :
    mult_real (q * 2 ^ (-E)) (real_power 2 52) = q * 2 ^ (52 - E) := by
  simp only [mult_real, real_power]
  rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
  congr 2; omega


set_option maxHeartbeats 20000000 in
theorem run_FPRoundBase32_q {s : SState} (hc : LinuxEL0Config s) (hism : (InStreamingMode ()).run s = .ok false s)
    (fpcr : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (q : Rat) (E : Int) (h1 : (2 : Rat) ^ E ≤ q) (h2 : q < (2 : Rat) ^ (E + 1))
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs)
    (hOF : Nat.testBit (rbq32 fpcr.toNat rm neg q E).2.1 2 = true → fpcr.getLsbD 10 = false)
    (hUF : Nat.testBit (rbq32 fpcr.toNat rm neg q E).2.1 3 = true → fpcr.getLsbD 11 = false)
    (hIX : Nat.testBit (rbq32 fpcr.toNat rm neg q E).2.1 4 = true → fpcr.getLsbD 12 = false) :
    (FPRoundBase__1 (if neg then -q else q) fpcr (aslRM rm) false true 32).run s =
      let o := rbq32 fpcr.toNat rm neg q E
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
  have hA0 : 0 ≤ round_down (q * 2 ^ (23 - max E (-126))) := round_down_nonneg_q _ (Rat.le_of_lt (Rat.mul_pos hp (rat_pos_zpow _)))
  have hAu0 : 0 ≤ round_down (q * 2 ^ (23 - E)) := round_down_nonneg_q _ (Rat.le_of_lt (Rat.mul_pos hp (rat_pos_zpow _)))
  have e0 : s = s.set .FPSR xs := (SState.set_same s .FPSR xs hx).symm
  rw [e0] at hism
  conv => lhs; rw [e0]
  simp only [rbq32] at hOF hUF hIX ⊢
  unfold FPRoundBase__1
  rw [run_SailME_run]
  cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, undefined_real, undefined_FPRounding,
    hne, hr', q_sign neg q hp, fpr_loop1q q E h1 h2, fpr_loop2q q E h1 h2,
    HaveAltFP, run_IsFeatureImplemented hc, run_IsFeatureImplemented (hc.set_FPSR xs), run_UsingAArch32 (hc.set_FPSR xs), sc32q, su32q,
    ipow8, ipow23, ipow24, fst_ite, snd_ite]
  simp only [get_AH, get_FZ, get_UFE, ofBool_eq_one] at *
  generalize sub_real (q * 2 ^ (23 - max E (-126))) (to_real (round_down (q * 2 ^ (23 - max E (-126))))) = Er at *
  generalize sub_real (q * 2 ^ (23 - E)) (to_real (round_down (q * 2 ^ (23 - E)))) = Eu at *
  generalize round_down (q * 2 ^ (23 - max E (-126))) = A at *
  generalize round_down (q * 2 ^ (23 - E)) = Au at *
  simp only [Janus.Arm64.FP.ah, Janus.Arm64.FP.fz, Janus.Arm64.FP.ufe, Janus.Arm64.FP.fpcrBit] at *
  have hT0 : ∀ rm, rbTiny false rm neg E Au Eu = false := fun rm => by simp [rbTiny]
  by_cases hT : rbTiny true rm neg E Au Eu = true
  all_goals cases rm
  all_goals try exact absurd rfl hrm
  all_goals
    by_cases hAH : fpcr.toNat / 2 ^ 1 % 2 = 1 <;> by_cases hFZ : fpcr.toNat / 2 ^ 24 % 2 = 1 <;>
      by_cases hUFE : fpcr.toNat / 2 ^ 11 % 2 = 1 <;> by_cases hE : E < -126
  all_goals
    fp_simp [aslRM, rbRU, rbOTI, rbTiny, rbBE2, hAH, hFZ, hUFE, hism, hE, hT0, testBit_ite, Nat.testBit_or, upd_bit3,
      fst_ite, snd_ite, ipow8, ipow23, ipow24] at hT
  all_goals
    fp_simp [aslRM, rb32, rbRU, rbOTI, rbTiny, rbBE2, hAH, hFZ, hUFE, hism, hE, hT0, run_ME_bind, run_ME_lift, run_ME_pure,
        run_ME_map, run_ME_throw, testBit_ite, Nat.testBit_or, upd_bit3, fst_ite, snd_ite, ipow8, ipow23, ipow24,
        FPInf32_pure, FPMax32_pure, FPZero32_pure, FPInf32_0, FPInf32_1, FPMax32_0, FPMax32_1, FPZero32_0, FPZero32_1,
        liftM_pure_ME, ite_pure_ME]
      at hOF hUF hIX ⊢
  all_goals try simp only [ite_t hT, hT, true_implies, false_implies, imp_false, not_true_eq_false,
    not_false_eq_true, Classical.not_not, and_true, true_and, and_false, false_and] at hOF hUF hIX ⊢
  all_goals try (have hT' := fun (h : _ ∧ ¬ _) => h.2 (hT h.1)
                 simp only [ite_f hT', eq_true hT, eq_false hT', true_implies, false_and, and_false, false_or,
                   or_false, ↓reduceIte] at hOF hUF hIX ⊢)
  all_goals
    rb_leaf_simp
  all_goals try (rw [run_readReg_FPSR_set]; rb_leaf_simp)
  all_goals try refine ⟨?_, ?_⟩
  all_goals try (first
         | rfl
         | (apply bits_ite
            erw [BitVec.toNat_append, BitVec.toNat_append]
            refine enc_fin neg _ _ _ _ (by decide) (by decide) _ rfl _ _ (isub7 _ ?_) (isub22 _ ?_)
            all_goals (repeat' split) <;> first | omega | (apply fdiv_nonneg; omega) | decide)
         | (congr 1
            simp only [ofNat_or, ofNat_ite, BitVec.or_assoc, Nat.or_zero, BitVec.ofNat_eq_ofNat, BitVec.or_zero]
            try ac_rfl))


end JanusASL.Proofs
