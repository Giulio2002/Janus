import Janus.Float.Lemmas
import Janus.Amd64.Float

/-!
# The SSE model in IEEE mode (proved, not trusted)

With `MXCSR.DAZ = MXCSR.FTZ = 0` and every exception masked (`IEEEMode`, e.g. the default
`0x1F80`), the SSE operations of `Janus.Amd64.FP` never trap and compute the IEEE 754
operations of `Janus.Float.Spec` in the rounding direction `MXCSR.RC`, delivering a NaN
exactly when the specification's result is a NaN.
-/

set_option linter.unusedSimpArgs false

namespace Janus.Amd64.FP

open Janus.Float

/-- The controls select plain IEEE 754 behaviour: no `DAZ`, no `FTZ` (any `RC`). -/
def IEEEMode (c : Ctl) : Prop := c.daz = false ∧ c.ftz = false

theorem IEEEMode.default : IEEEMode (ctl 0x1F80) := by refine ⟨?_, ?_⟩ <;> decide

/-- With every exception masked nothing traps. -/
theorem trap_masked {c : Nat} (h : unmasked c = 0) (o : XR) : o.trap c = false := by
  simp [XR.trap, h]

variable {c : Ctl}

theorem kindOf_ieee (h : IEEEMode c) (f : Fmt) (x : Nat) : kindOf f c x = classify f x := by
  unfold kindOf; cases classify f x <;> simp [h.1]

theorem valOf_ieee (h : IEEEMode c) (f : Fmt) (x : Nat) : valOf f c x = valueOf f x := by
  unfold valOf; rw [kindOf_ieee h]
  split
  · rename_i hz; unfold valueOf; rw [hz]
  · rfl


theorem roundX_ieee (h : IEEEMode c) (f : Fmt) (rm : RM) (pre : Nat) (neg : Bool) (m : Nat)
    (e : Int) : (roundX f c rm pre neg m e).res = (round f rm neg m e).bits := by
  unfold roundX
  simp only [check, h.2]
  split <;> (try split) <;> (try split) <;> (try split) <;> simp_all [apply_ite]

theorem indefinite_classify (f : Fmt) (hf : f.Std) : classify f (indefinite f) = .qnan := by
  rcases hf with rfl | rfl <;> decide

theorem indefinite_lt (f : Fmt) (hf : f.Std) : indefinite f < 2 ^ f.width := by
  rcases hf with rfl | rfl <;> decide

theorem rmi_beq {rm : RM} : (rm == .rmi) = decide (rm = .rmi) := by cases rm <;> rfl

/-- `ADDSD`/`ADDSS` in IEEE mode. -/
theorem binop_add_ieee (h : IEEEMode c) (f : Fmt) (hf : f.Std) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (binop .add f c a b).res < 2 ^ f.width ∧
    ResultIs f (add f (c.rc) a b) (binop .add f c a b).res := by
  have hi := indefinite_classify f hf
  have hil := indefinite_lt f hf
  simp only [ResultIs, add, binop, kindOf_ieee h, valOf_ieee h, nanResult, check]
  cases hx : addExact (valueOf f a).n (valueOf f a).e (valueOf f b).n (valueOf f b).e <;>
  cases h1 : classify f a <;> cases h2 : classify f b <;>
    cases hsa : signOf f a <;> cases hsb : signOf f b <;>
    simp [h1, h2, hsa, hsb, isNaN, isSNaN, roundX_ieee h, rmi_beq, zero_lt, inf_lt, round_bits_lt, ha, hb,
      or_quiet_lt f hf, hi, hil, quiet]
  all_goals (try (rw [valueOf_of_zero h1, valueOf_of_zero h2] at hx; simp [Val.n, Val.e, addExact_zero] at hx))
  all_goals first
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h1])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h2])
    | (unfold isNaN; rw [h1]) | (unfold isNaN; rw [h2])

/-- `MULSD`/`MULSS` in IEEE mode. -/
theorem binop_mul_ieee (h : IEEEMode c) (f : Fmt) (hf : f.Std) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (binop .mul f c a b).res < 2 ^ f.width ∧
    ResultIs f (mul f (c.rc) a b) (binop .mul f c a b).res := by
  have hi := indefinite_classify f hf
  have hil := indefinite_lt f hf
  simp only [ResultIs, mul, binop, kindOf_ieee h, valOf_ieee h, nanResult, check]
  cases hx : mulExact (valueOf f a).n (valueOf f a).e (valueOf f b).n (valueOf f b).e <;>
  cases h1 : classify f a <;> cases h2 : classify f b <;>
    cases hsa : signOf f a <;> cases hsb : signOf f b <;>
    simp [h1, h2, hsa, hsb, isNaN, isSNaN, roundX_ieee h, zero_lt, inf_lt, round_bits_lt, ha, hb,
      or_quiet_lt f hf, hi, hil, quiet]
  all_goals first
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h1])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h2])
    | (unfold isNaN; rw [h1]) | (unfold isNaN; rw [h2])

/-- When `FP.fma` is defined in IEEE mode: at most one NaN operand, and not `0 × ∞ + NaN`
(the cases the model leaves to the implementation, see `FP.fma`). -/
def FmaDefined (f : Fmt) (a b d : Nat) : Prop :=
  (isNaN f a).toNat + (isNaN f b).toNat + (isNaN f d).toNat ≤ 1 ∧
  ¬ (isNaN f d = true ∧ (classify f a = .inf ∨ classify f b = .inf) ∧
    (classify f a = .zero ∨ classify f b = .zero))

theorem addExact_zero_zero (e e' : Int) : addExact 0 e 0 e' = none := by
  simp [addExact, align, Janus.Float.ofInt]

set_option maxHeartbeats 4000000 in
/-- `VFMADD{132,213,231}SD/SS` in IEEE mode, with the multiplicands `a`, `b` and the addend `d`:
defined (the instruction does not fault) and `a × b + d` rounded once, as IEEE 754
`fusedMultiplyAdd` (`Janus.Float.fma`). -/
theorem fma_ieee (h : IEEEMode c) (f : Fmt) (hf : f.Std) (a b d : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) (hd : d < 2 ^ f.width) (hdef : FmaDefined f a b d) :
    match FP.fma f c false false a b d with
    | some o => o.res < 2 ^ f.width ∧ ResultIs f (Janus.Float.fma f c.rc a b d) o.res
    | none => False := by
  have hi := indefinite_classify f hf
  have hil := indefinite_lt f hf
  unfold FmaDefined at hdef
  simp only [ResultIs, Janus.Float.fma, FP.fma, kindOf_ieee h, valOf_ieee h, check, fmaExact,
    Bool.false_eq_true, ite_false, Bool.bne_false] at hdef ⊢
  cases hx : addExact (valueOf f d).n (valueOf f d).e ((valueOf f a).n * (valueOf f b).n)
      ((valueOf f a).e + (valueOf f b).e) <;>
  cases h0 : classify f d <;> cases h1 : classify f a <;> cases h2 : classify f b <;>
    simp [h0, h1, h2, isNaN, isSNaN, roundX_ieee h, rmi_beq, zero_lt, inf_lt, round_bits_lt, ha, hb, hd,
      or_quiet_lt f hf, hi, hil, quiet] at hdef ⊢
  all_goals try (cases hsd : signOf f d <;> cases hsa : signOf f a <;> cases hsb : signOf f b <;>
    simp [hsd, hsa, hsb, h0, h1, h2, zero_lt, inf_lt, hi, hil, roundX_ieee h, round_bits_lt, rmi_beq])
  all_goals (try (rw [valueOf_of_zero h0, valueOf_of_zero h1] at hx; simp [Val.n, Val.e, addExact_zero_zero] at hx))
  all_goals (try (rw [valueOf_of_zero h0, valueOf_of_zero h2] at hx; simp [Val.n, Val.e, addExact_zero_zero] at hx))
  all_goals first
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h0])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h1])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h2])
    | (unfold isNaN; rw [h0]) | (unfold isNaN; rw [h1]) | (unfold isNaN; rw [h2])

theorem toInt_num (f : Fmt) (c : Ctl) (rm : RM) (iw b : Nat) (n e i : Int) (ex : Bool)
    (h : isNaN f b = false) (hv : valOf f c b = .num n e) (hn : n ≠ 0)
    (hi : roundToInt rm (signOf f b) n.natAbs e = (i, ex))
    (hr1 : -(2 ^ (iw - 1) : Int) ≤ i) (hr2 : i < 2 ^ (iw - 1)) :
    (toInt f c rm iw b).res = (i % (2 ^ iw : Int)).toNat := by
  unfold toInt
  simp only [h, hv, hn, hi, Bool.false_eq_true, ite_false]
  simp [check, show ¬ i < -(2 ^ (iw - 1) : Int) by omega, show ¬ i ≥ 2 ^ (iw - 1) by omega]

theorem toInt_exact64 (c : Ctl) (hc : IEEEMode c) (f : Nat) (hf0 : 0 < f) (hf : f < 2 ^ 52) :
    (toInt binary64 c .rz 64
      ((Nat.log2 f + 1034) * 2 ^ 52 + (f * 2 ^ (52 - Nat.log2 f) - 2 ^ 52))).res = f * 2 ^ 11 := by
  have hL1 : 2 ^ Nat.log2 f ≤ f := Nat.log2_self_le (by omega)
  have hL2 : f < 2 ^ (Nat.log2 f + 1) := Nat.lt_log2_self
  have hL : Nat.log2 f < 52 := (Nat.log2_lt (by omega)).2 hf
  generalize Nat.log2 f = L at *
  have hk1 : 2 ^ 52 ≤ f * 2 ^ (52 - L) := by
    calc 2 ^ 52 = 2 ^ L * 2 ^ (52 - L) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ f * 2 ^ (52 - L) := Nat.mul_le_mul_right _ hL1
  have hk2 : f * 2 ^ (52 - L) < 2 ^ 53 := by
    calc f * 2 ^ (52 - L) < 2 ^ (L + 1) * 2 ^ (52 - L) := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
      _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
  -- the value f * 2^11 = k * 2^(L - 41)
  have hv : ∀ k, k = f * 2 ^ (52 - L) →
      (roundToInt .rz false k ((L : Int) - 41)).1 = (f * 2 ^ 11 : Nat) ∧
      (roundToInt .rz false k ((L : Int) - 41)).2 = false := by
    intro k hk
    unfold roundToInt
    by_cases h41 : 41 ≤ L
    · have : ((L : Int) - 41).toNat = L - 41 := by omega
      simp only [show (0 : Int) ≤ (L : Int) - 41 by omega, ite_true, this]
      refine ⟨?_, by simp⟩
      rw [hk, Nat.mul_assoc, ← Nat.pow_add, show 52 - L + (L - 41) = 11 by omega]; simp
    · have : (-((L : Int) - 41)).toNat = 41 - L := by omega
      have hdiv : k = f * 2 ^ 11 * 2 ^ (41 - L) := by
        rw [hk, Nat.mul_assoc, ← Nat.pow_add, show 11 + (41 - L) = 52 - L by omega]
      simp only [show ¬ (0 : Int) ≤ (L : Int) - 41 by omega, ite_false, this, hdiv,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.mul_mod_left, roundUp]
      simp
  obtain ⟨hv1, hv2⟩ := hv _ rfl
  generalize f * 2 ^ (52 - L) = k at *
  have hx : ((L + 1034) * 2 ^ 52 + (k - 2 ^ 52)) / 2 ^ 52 = L + 1034 := by omega
  have hfr : ((L + 1034) * 2 ^ 52 + (k - 2 ^ 52)) % 2 ^ 52 = k - 2 ^ 52 := by omega
  have hlt : (L + 1034) * 2 ^ 52 + (k - 2 ^ 52) < 2 ^ 63 := by omega
  generalize hX : (L + 1034) * 2 ^ 52 + (k - 2 ^ 52) = X at *
  have hexp : expOf binary64 X = L + 1034 := by
    unfold expOf; simp only [binary64]; rw [hx]; omega
  have hfrac : fracOf binary64 X = k - 2 ^ 52 := by unfold fracOf; simp only [binary64]; exact hfr
  have hsign : signOf binary64 X = false := by
    have : X / 2 ^ 63 = 0 := Nat.div_eq_of_lt hlt
    simp [signOf, Fmt.signBit, binary64, this]
  have hcl : classify binary64 X = .normal := by
    unfold classify; rw [hexp, hfrac]; simp [Fmt.expMax, binary64]; intro h; omega
  have hval : valueOf binary64 X = .num k ((L : Int) - 41) := by
    have hm : mantOf binary64 X = k := by
      unfold mantOf; rw [hexp, hfrac, b64_fbits]; simp only [show L + 1034 ≠ 0 by omega, ite_false]
      exact Nat.add_sub_of_le hk1
    have hu : ulpExpOf binary64 X = (L : Int) - 41 := by
      unfold ulpExpOf; rw [hexp, b64_bias, b64_fbits]; simp only [show L + 1034 ≠ 0 by omega, ite_false]
      omega
    rw [valueOf_normal hcl, hm, hu, hsign]; rfl
  have hn : isNaN binary64 X = false := not_isNaN_of_classify hcl (by simp)
  have hv' : valOf binary64 c X = .num (k : Int) ((L : Int) - 41) := by
    rw [valOf_ieee hc, hval]
  have hi : roundToInt .rz (signOf binary64 X) (k : Int).natAbs ((L : Int) - 41) =
      (((f * 2 ^ 11 : Nat) : Int), false) := by
    rw [hsign, Int.natAbs_natCast]; exact Prod.ext hv1 hv2
  rw [toInt_num binary64 c .rz 64 X k _ _ false hn hv' (by omega) hi (by omega) (by omega)]
  omega

theorem comis_res {c : Ctl} (h : IEEEMode c) (f : Fmt) (s : Bool) (a b : Nat)
    (ha : isNaN f a = false) (hb : isNaN f b = false) :
    (comis s f c a b).res =
      if Val.eq (valueOf f a) (valueOf f b) then 4 else if Val.lt (valueOf f a) (valueOf f b) then 1 else 0 := by
  unfold comis relation
  simp only [ha, hb, Bool.or_false, Bool.false_eq_true, ite_false, valOf_ieee h, check]
  split <;> split <;> simp_all


/-- `SUBSD` of `2^63` from a binary64 number in `[2^63, 2^64)` is exact. -/
theorem binop_sub_2p63 {c : Ctl} (h : IEEEMode c) (fr : Nat) (hf : fr < 2 ^ 52) :
    (binop .sub binary64 c (1086 * 2 ^ 52 + fr) (1086 * 2 ^ 52 + 0)).res =
      if fr = 0 then zero binary64 (c.rc = .rmi) else (round binary64 c.rc false fr 11).bits := by
  obtain ⟨hca, hsa, hva, -, -⟩ := b64_normal 1086 fr (by omega) (by omega) hf
  obtain ⟨hcb, hsb, hvb, -, -⟩ := b64_normal 1086 0 (by omega) (by omega) (by decide)
  generalize 1086 * 2 ^ 52 + fr = a at *
  generalize 1086 * 2 ^ 52 + 0 = b at *
  have hna : isNaN binary64 a = false := not_isNaN_of_classify hca (by simp)
  have hnb : isNaN binary64 b = false := not_isNaN_of_classify hcb (by simp)
  unfold binop
  simp only [kindOf_ieee h, valOf_ieee h, hca, hcb, hsa, hsb, hna, hnb, hva, hvb, Bool.or_false,
    Bool.false_eq_true, ite_false, Val.n, Val.e]
  rw [show ((1086 : Nat) : Int) - 1075 = 11 by omega]
  have hx : addExact ((2 ^ 52 + fr : Nat) : Int) 11 (-((2 ^ 52 + 0 : Nat) : Int)) 11 =
      Janus.Float.ofInt (fr : Int) 11 := by
    simp only [addExact, align, Int.min_self, Int.sub_self, Int.toNat_zero, Nat.pow_zero,
      Int.pow_zero, Int.mul_one]
    congr 1; omega
  rw [hx]
  unfold Janus.Float.ofInt
  by_cases h0 : fr = 0
  · simp [h0, check]
  · simp [show ¬ (fr : Int) = 0 by omega, h0]
    rw [roundX_ieee h, show decide ((fr : Int) < 0) = false from by simp]


end Janus.Amd64.FP
