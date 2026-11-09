import JanusASL.Proofs.FP.RoundBase
/-! # `FPRoundBase` (binary32) equals Janus' `fpRound`

`rb32Of_eq`: the pure transcription `rb32` (FP/RoundBase) at the floors and errors the ASL
computes is Janus' `fpRound binary32` (result, raised and directly set cumulative bits), by
`roundAt_rd` (Janus' `roundAt` through the same floor and error), the floor bounds, the biased
exponent/mantissa correspondence `rbBE2_biased` and the tininess-after-rounding test
`rbTiny_eq`. `run_FPRoundBase32` composes it with `run_FPRoundBase32_rb`. -/
set_option linter.unusedSimpArgs false
namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem rbRU_zero (rm : Janus.Float.RM) (neg : Bool) (A : Int) : rbRU rm neg 0 A = false := by
  cases rm <;> simp [rbRU, gt_zero_half, eq_zero_half]

theorem rbRU_frac (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (k r s : Nat) :
    rbRU rm neg ((r : Rat) * 2 ^ (-(s : Int))) (k : Int) = Janus.Float.roundUp rm neg k r s := by
  have hk : integer_access (k : Int) 0 = 1#1 ↔ k % 2 = 1 := by
    rw [← eq_iff_iff, integer_access0 _ (Int.natCast_nonneg k)]; apply propext; omega
  have hk' : (integer_access (k : Int) 0 == 1#1) = decide (k % 2 = 1) := by
    by_cases h : k % 2 = 1 <;> simp [h, hk]
  cases rm
  · by_cases hr : r = 0
    · subst hr; simp [rbRU, Janus.Float.roundUp, gt_zero_half, eq_zero_half]
    · simp [rbRU, Janus.Float.roundUp, gt_frac_half, eq_frac_half, hr, hk']
  · cases neg <;> simp [rbRU, Janus.Float.roundUp, bne_frac_zero]
  · cases neg <;> simp [rbRU, Janus.Float.roundUp, bne_frac_zero]
  · simp [rbRU, Janus.Float.roundUp]
  · exact absurd rfl hrm

/-- Janus' `roundAt` through the floor and error `FPRoundBase` computes. -/
theorem roundAt_rd (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (m : Nat) (e q d : Int) (hd : e - q = d) :
    Janus.Float.roundAt rm neg m e q =
      (if rbRU rm neg (sub_real ((m : Rat) * 2 ^ d) (to_real (round_down ((m : Rat) * 2 ^ d))))
          (round_down ((m : Rat) * 2 ^ d)) then (round_down ((m : Rat) * 2 ^ d)).toNat + 1
        else (round_down ((m : Rat) * 2 ^ d)).toNat,
       sub_real ((m : Rat) * 2 ^ d) (to_real (round_down ((m : Rat) * 2 ^ d))) != 0) := by
  unfold Janus.Float.roundAt
  by_cases hq : q ≤ e
  · obtain ⟨h1, h2⟩ := (rd_split m d).1 (by omega)
    rw [h2, rbRU_zero, h1, ite_t hq]
    simp only [Int.toNat_natCast, bne_self_eq_false, Bool.false_eq_true, ite_false]
    congr 3; omega
  · obtain ⟨h1, h2⟩ := (rd_split m d).2 (by omega)
    rw [h2, h1, ite_f hq]
    have hs : (-d).toNat = (q - e).toNat := by omega
    rw [hs, rbRU_frac rm hrm, bne_frac_zero, Int.toNat_natCast]

theorem nb_mul (m L t : Nat) (h1 : 2 ^ L ≤ m) (h2 : m < 2 ^ (L + 1)) :
    2 ^ (L + t) ≤ m * 2 ^ t ∧ m * 2 ^ t < 2 ^ (L + 1 + t) := by
  rw [Nat.pow_add, Nat.pow_add]
  exact ⟨Nat.mul_le_mul_right _ h1, Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos t)⟩

theorem nb_div (m L s : Nat) (h1 : 2 ^ L ≤ m) (h2 : m < 2 ^ (L + 1)) (hs : s ≤ L) :
    2 ^ (L - s) ≤ m / 2 ^ s ∧ m / 2 ^ s < 2 ^ (L + 1 - s) := by
  constructor
  · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add, show L - s + s = L by omega]; exact h1
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show L + 1 - s + s = L + 1 by omega]; exact h2

theorem A_bounds (m : Nat) (hm : m ≠ 0) (e : Int) :
    0 ≤ round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23))) ∧
    (-126 ≤ (Nat.log2 m : Int) + e →
      2 ^ 23 ≤ round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23))) ∧
      round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23))) < 2 ^ 24) ∧
    ((Nat.log2 m : Int) + e < -126 →
      round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23))) < 2 ^ 23) := by
  have h1 : 2 ^ Nat.log2 m ≤ m := Nat.log2_self_le hm
  have h2 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  refine ⟨rd_nonneg _ _, ?_, ?_⟩
  · intro hn
    by_cases hd : 0 ≤ e - (max ((Nat.log2 m : Int) + e) (-126) - 23)
    · rw [((rd_split m _).1 hd).1]
      have ht : (e - (max ((Nat.log2 m : Int) + e) (-126) - 23)).toNat = 23 - Nat.log2 m := by omega
      rw [ht]
      obtain ⟨b1, b2⟩ := nb_mul m (Nat.log2 m) (23 - Nat.log2 m) h1 h2
      rw [show Nat.log2 m + (23 - Nat.log2 m) = 23 by omega] at b1
      rw [show Nat.log2 m + 1 + (23 - Nat.log2 m) = 24 by omega] at b2
      constructor <;> omega
    · rw [((rd_split m _).2 (by omega)).1]
      have ht : (-(e - (max ((Nat.log2 m : Int) + e) (-126) - 23))).toNat = Nat.log2 m - 23 := by omega
      rw [ht]
      obtain ⟨b1, b2⟩ := nb_div m (Nat.log2 m) (Nat.log2 m - 23) h1 h2 (by omega)
      rw [show Nat.log2 m - (Nat.log2 m - 23) = 23 by omega] at b1
      rw [show Nat.log2 m + 1 - (Nat.log2 m - 23) = 24 by omega] at b2
      constructor <;> omega
  · intro hs
    by_cases hd : 0 ≤ e - (max ((Nat.log2 m : Int) + e) (-126) - 23)
    · rw [((rd_split m _).1 hd).1]
      obtain ⟨_, b2⟩ := nb_mul m (Nat.log2 m) (e - (max ((Nat.log2 m : Int) + e) (-126) - 23)).toNat h1 h2
      have : 2 ^ (Nat.log2 m + 1 + (e - (max ((Nat.log2 m : Int) + e) (-126) - 23)).toNat) ≤ 2 ^ 23 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · rw [((rd_split m _).2 (by omega)).1]
      have : m / 2 ^ (-(e - (max ((Nat.log2 m : Int) + e) (-126) - 23))).toNat < 2 ^ 23 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
        exact Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))
      omega

theorem Au_bounds (m : Nat) (hm : m ≠ 0) :
    2 ^ 23 ≤ round_down ((m : Rat) * 2 ^ (23 - (Nat.log2 m : Int))) ∧
      round_down ((m : Rat) * 2 ^ (23 - (Nat.log2 m : Int))) < 2 ^ 24 := by
  have h1 : 2 ^ Nat.log2 m ≤ m := Nat.log2_self_le hm
  have h2 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  by_cases hd : 0 ≤ 23 - (Nat.log2 m : Int)
  · rw [((rd_split m _).1 hd).1]
    have ht : (23 - (Nat.log2 m : Int)).toNat = 23 - Nat.log2 m := by omega
    rw [ht]
    obtain ⟨b1, b2⟩ := nb_mul m (Nat.log2 m) (23 - Nat.log2 m) h1 h2
    rw [show Nat.log2 m + (23 - Nat.log2 m) = 23 by omega] at b1
    rw [show Nat.log2 m + 1 + (23 - Nat.log2 m) = 24 by omega] at b2
    constructor <;> omega
  · rw [((rd_split m _).2 (by omega)).1]
    have ht : (-(23 - (Nat.log2 m : Int))).toNat = Nat.log2 m - 23 := by omega
    rw [ht]
    obtain ⟨b1, b2⟩ := nb_div m (Nat.log2 m) (Nat.log2 m - 23) h1 h2 (by omega)
    rw [show Nat.log2 m - (Nat.log2 m - 23) = 23 by omega] at b1
    rw [show Nat.log2 m + 1 - (Nat.log2 m - 23) = 24 by omega] at b2
    constructor <;> omega

theorem rbOTI_eq (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) :
    rbOTI rm neg = Janus.Float.overflowToInf rm neg := by
  cases rm <;> cases neg <;> first | rfl | exact absurd rfl hrm

theorem bne_ite1 (c : Prop) [Decidable c] (x : Rat) :
    ((if c then (1 : Rat) else x) != 0) = (decide c || (x != 0)) := by
  by_cases h : c <;> simp [h]

/-- Janus' `roundUnits binary32` from the rounding decision `ru` and floor `A` at the normalised
exponent `E`. -/
theorem ite_t' {α : Sort _} {c : Prop} {_ : Decidable c} (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]
theorem ite_f' {α : Sort _} {c : Prop} {_ : Decidable c} (h : ¬c) (a b : α) : (if c then a else b) = b := by
  simp [h]

def ju32 (ru : Bool) (E A : Int) : Nat × Int :=
  let k : Nat := if ru then A.toNat + 1 else A.toNat
  let q : Int := max E (-126) - 23
  if k = 2 ^ 24 then (k / 2, q + 1) else (k, q)

theorem roundUnits_rd (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (m : Nat) (e : Int) :
    Janus.Float.roundUnits Janus.Float.binary32 rm neg m e =
      ju32 (rbRU rm neg (sub_real ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23)))
          (to_real (round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23))))))
          (round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23)))))
        ((Nat.log2 m : Int) + e) (round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23)))) := by
  unfold Janus.Float.roundUnits ju32
  simp only [roundAt_rd rm hrm neg m e (max ((Nat.log2 m : Int) + e) Janus.Float.binary32.emin -
    (Janus.Float.binary32.fbits : Int)) (e - (max ((Nat.log2 m : Int) + e) (-126) - 23)) (by
      simp only [Janus.Float.binary32, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias, Janus.Float.Fmt.fbits]; omega)]
  simp only [Janus.Float.binary32, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias, Janus.Float.Fmt.fbits]
  rfl

theorem fdiv24 : fdiv_int (2 ^ 24) 2 = 2 ^ 23 := by decide

theorem rbBE2_biased (ru : Bool) (E A : Int) (hA0 : 0 ≤ A) (hAn : -126 ≤ E → 2 ^ 23 ≤ A ∧ A < 2 ^ 24)
    (hAs : E < -126 → A < 2 ^ 23) :
    (rbBE2 ru E A).1 = Janus.Float.biasedExp Janus.Float.binary32 (ju32 ru E A).1 (ju32 ru E A).2 ∧
      (rbBE2 ru E A).2.toNat % 2 ^ 23 = (ju32 ru E A).1 % 2 ^ 23 ∧ 0 ≤ (rbBE2 ru E A).1 := by
  unfold rbBE2 ju32 Janus.Float.biasedExp
  simp only [Janus.Float.binary32, Janus.Float.Fmt.bias, Janus.Float.Fmt.fbits]
  by_cases hE : E < -126
  · have := hAs hE
    cases ru <;> simp only [Bool.false_eq_true, ite_true, ite_false]
    · have h1 : ¬ A.toNat = 2 ^ 24 := by omega
      simp only [h1, ite_false]
      refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial
    · by_cases h23 : A + 1 = 2 ^ 23
      · have h1 : ¬ A.toNat + 1 = 2 ^ 24 := by omega
        have h2 : ¬ A + 1 = 2 ^ 24 := by omega
        simp only [h1, h2, h23, ite_true, ite_false]
        refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial
      · have h1 : ¬ A.toNat + 1 = 2 ^ 24 := by omega
        have h2 : ¬ A + 1 = 2 ^ 24 := by omega
        simp only [h1, h2, h23, ite_true, ite_false]
        refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial
  · have := hAn (by omega)
    cases ru <;> simp only [Bool.false_eq_true, ite_true, ite_false]
    · have h1 : ¬ A.toNat = 2 ^ 24 := by omega
      simp only [h1, ite_false]
      refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial
    · have h23 : ¬ A + 1 = 2 ^ 23 := by omega
      by_cases h24 : A + 1 = 2 ^ 24
      · have h1 : A.toNat + 1 = 2 ^ 24 := by omega
        simp only [h1, h24, h23, ite_true, ite_false, fdiv24]
        refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial
      · have h1 : ¬ A.toNat + 1 = 2 ^ 24 := by omega
        simp only [h1, h24, h23, ite_true, ite_false]
        refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> first | omega | trivial

theorem rbTiny_eq (ah : Bool) (rm : Janus.Float.RM) (neg : Bool) (E Au : Int) (Eu : Rat)
    (hAu1 : 2 ^ 23 ≤ Au) (hAu2 : Au < 2 ^ 24) :
    rbTiny ah rm neg E Au Eu = (ah && decide ((if (if rbRU rm neg Eu Au then Au.toNat + 1 else Au.toNat) =
      2 ^ 24 then E + 1 else E) < -126)) := by
  unfold rbTiny
  rw [Bool.eq_iff_iff]
  cases rbRU rm neg Eu Au <;> cases ah <;>
    simp only [Bool.false_eq_true, ite_true, ite_false, Bool.false_and, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq, fdiv24, Bool.false_eq_true, iff_self]
  · omega
  · by_cases h : Au + 1 = 2 ^ 24
    · have h1 : Au.toNat + 1 = 2 ^ 24 := by omega
      simp only [h, h1, ite_true, fdiv24]; omega
    · have h1 : ¬ Au.toNat + 1 = 2 ^ 24 := by omega
      simp only [h, h1, ite_false]; omega

set_option maxHeartbeats 20000000 in
theorem rb32Of_eq (fpcr : Nat) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (m : Nat) (hm : m ≠ 0) (e : Int) :
    rb32Of fpcr rm neg m e =
      (BitVec.ofNat 32 (Janus.Arm64.FP.fpRound Janus.Float.binary32 fpcr rm neg m e).1,
        (Janus.Arm64.FP.fpRound Janus.Float.binary32 fpcr rm neg m e).2.proc,
        (Janus.Arm64.FP.fpRound Janus.Float.binary32 fpcr rm neg m e).2.direct) := by
  obtain ⟨hA0, hAn, hAs⟩ := A_bounds m hm e
  obtain ⟨hAu1, hAu2⟩ := Au_bounds m hm
  have hq1 := roundAt_rd rm hrm neg m e (max ((Nat.log2 m : Int) + e) Janus.Float.binary32.emin -
    (Janus.Float.binary32.fbits : Int)) (e - (max ((Nat.log2 m : Int) + e) (-126) - 23)) (by
      simp only [Janus.Float.binary32, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias, Janus.Float.Fmt.fbits]; omega)
  have hq2 := roundAt_rd rm hrm neg m e ((Nat.log2 m : Int) + e - (Janus.Float.binary32.fbits : Int))
    (23 - (Nat.log2 m : Int)) (by simp only [Janus.Float.binary32, Janus.Float.Fmt.fbits]; omega)
  simp only [rb32Of, Janus.Arm64.FP.fpRound, Janus.Float.round, hq1, hq2, roundUnits_rd rm hrm, rb32, bne_ite1,
    rbOTI_eq rm hrm, rbTiny_eq _ _ _ _ _ _ hAu1 hAu2]
  clear hq1 hq2
  generalize sub_real ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23)))
    (to_real (round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23))))) = Er at *
  generalize sub_real ((m : Rat) * 2 ^ (23 - (Nat.log2 m : Int)))
    (to_real (round_down ((m : Rat) * 2 ^ (23 - (Nat.log2 m : Int))))) = Eu at *
  generalize round_down ((m : Rat) * 2 ^ (e - (max ((Nat.log2 m : Int) + e) (-126) - 23))) = A at *
  generalize round_down ((m : Rat) * 2 ^ (23 - (Nat.log2 m : Int))) = Au at *
  generalize (Nat.log2 m : Int) + e = E at *
  generalize rbRU rm neg Er A = ru at *
  obtain ⟨hB, hM, hB0⟩ := rbBE2_biased ru E A hA0 hAn hAs
  generalize rbBE2 ru E A = P at *
  generalize ju32 ru E A = U at *
  generalize Janus.Float.biasedExp Janus.Float.binary32 U.1 U.2 = B at *
  obtain ⟨b2, i2⟩ := P
  simp only at hB hM hB0
  subst hB
  generalize (Er != 0) = er at *
  generalize Janus.Arm64.FP.ah fpcr = ah at *
  generalize Janus.Arm64.FP.fz fpcr = fz at *
  generalize Janus.Arm64.FP.ufe fpcr = ufe at *
  have hmax : (max (E + 126 + 1) 0 = 0) = (E < -126) := by apply propext; omega
  simp only [Janus.Float.binary32, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias, Janus.Float.Fmt.fbits,
    Janus.Float.Fmt.expMax, Janus.Float.pack, Janus.Float.Fmt.signBit, Janus.Arm64.FP.raise, Janus.Arm64.FP.UFC,
    Janus.Arm64.FP.OFC, Janus.Arm64.FP.IXC, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Int.reducePow,
    Int.reduceNeg, Int.reduceSub, Int.reduceAdd, Int.natCast_pow, ge_iff_le, Int.cast_ofNat_Int, Int.reduceToNat,
    hmax] at *
  by_cases hO : (255 : Int) ≤ b2 <;> by_cases hE : E < -126 <;> by_cases hT : E + 1 < -126 <;>
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
  all_goals try (exact congrArg (BitVec.ofNat 32) (by omega))
  all_goals try refine ⟨?_, ?_, ?_⟩
  all_goals try refine ⟨?_, ?_⟩
  all_goals (repeat' split)
  all_goals try simp only [decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at *
  all_goals try simp only [Nat.reduceOr, Nat.or_zero, Nat.zero_or] at *
  all_goals first
    | with_reducible rfl
    | (exfalso; omega)
    | (exact congrArg (BitVec.ofNat 32) (by omega))
    | (simp only [Prod.mk.injEq, and_true]; exact congrArg (BitVec.ofNat 32) (by omega))
    | skip

/-- **FPRoundBase (binary32) = Janus' `fpRound`.** Under `LinuxEL0Config`, outside streaming mode,
for the non-zero value `(-1)^neg * m * 2^e` and a rounding mode other than ties-away, the
generated `FPRoundBase(op, fpcr, rounding, FALSE, TRUE, 32)` returns Janus' rounded encoding and
ORs Janus' raised and directly set cumulative bits into FPSR, provided the trap of every
exception it raises is disabled. -/
theorem run_FPRoundBase32 {s : SState} (hc : LinuxEL0Config s) (hism : (InStreamingMode ()).run s = .ok false s)
    (fpcr : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (m : Nat) (hm : m ≠ 0) (e : Int)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs)
    (hOF : Nat.testBit (Janus.Arm64.FP.fpRound Janus.Float.binary32 fpcr.toNat rm neg m e).2.proc 2 = true →
      fpcr.getLsbD 10 = false)
    (hUF : Nat.testBit (Janus.Arm64.FP.fpRound Janus.Float.binary32 fpcr.toNat rm neg m e).2.proc 3 = true →
      fpcr.getLsbD 11 = false)
    (hIX : Nat.testBit (Janus.Arm64.FP.fpRound Janus.Float.binary32 fpcr.toNat rm neg m e).2.proc 4 = true →
      fpcr.getLsbD 12 = false) :
    (FPRoundBase__1 (sval neg m e) fpcr (aslRM rm) false true 32).run s =
      let r := Janus.Arm64.FP.fpRound Janus.Float.binary32 fpcr.toNat rm neg m e
      .ok (BitVec.ofNat 32 r.1) (s.set .FPSR (xs ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have h := rb32Of_eq fpcr.toNat rm hrm neg m hm e
  rw [run_FPRoundBase32_rb hc hism fpcr rm hrm neg m hm e hx (by rw [h]; exact hOF) (by rw [h]; exact hUF)
    (by rw [h]; exact hIX), h]

end JanusASL.Proofs
