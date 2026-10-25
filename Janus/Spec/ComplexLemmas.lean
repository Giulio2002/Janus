import Janus.Spec.Complex
import Janus.Arm64.FloatLemmas
import Janus.Amd64.FloatLemmas

/-!
# The machine models compute the operations of `Janus.Spec.Complex` (proved, not trusted)

`FP.fpSub`, `FP.fpDiv` (arm64, `FPCR` in IEEE mode) and `FP.binop .sub`, `.div` (amd64, `MXCSR`
in IEEE mode) deliver the IEEE results `Float.sub`, `Float.div` (a NaN exactly when the
specification's result is a NaN), as `fpAdd_ieee`, `fpMul_ieee` (`Janus.Arm64.FloatLemmas`) and
`binop_add_ieee`, `binop_mul_ieee` (`Janus.Amd64.FloatLemmas`) do for addition and
multiplication.
-/

set_option linter.unusedSimpArgs false

namespace Janus.Arm64.FP

open Janus.Float

variable {fpcr : Nat}

/-- `FPSub` in IEEE mode. -/
theorem fpSub_ieee (h : IEEEMode fpcr) (f : Fmt) (hf : f.Std) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (fpSub f fpcr a b).1 < 2 ^ f.width ∧
    ResultIs f (sub f (roundingMode fpcr) a b) (fpSub f fpcr a b).1 := by
  have hd := classify_defaultNaN f hf
  have hdl := defaultNaN_lt f hf
  have hdn : dn fpcr = false := h.2.2.2
  have hah : ah fpcr = false := h.2.1
  simp only [ResultIs, sub, fpSub, unpack_ieee h, processNaNs, processNaN, hah, hdn, defaultNaN_ieee h]
  cases hx : addExact (valueOf f a).n (valueOf f a).e (-(valueOf f b).n) (valueOf f b).e <;>
  cases h1 : classify f a <;> cases h2 : classify f b <;>
    cases hsa : signOf f a <;> cases hsb : signOf f b <;>
    simp [h1, h2, hsa, hsb, typeOf, isNaN, fpRound_ieee h, rne_ne_rmi, zero_lt, inf_lt,
      round_bits_lt, ha, hb, or_quiet_lt f hf, hd, hdl]
  all_goals first
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h1])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h2])
    | (unfold isNaN; rw [h1]) | (unfold isNaN; rw [h2])

/-- `FPDiv` in IEEE mode. -/
theorem fpDiv_ieee (h : IEEEMode fpcr) (f : Fmt) (hf : f.Std) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (fpDiv f fpcr a b).1 < 2 ^ f.width ∧
    ResultIs f (div f (roundingMode fpcr) a b) (fpDiv f fpcr a b).1 := by
  have hd := classify_defaultNaN f hf
  have hdl := defaultNaN_lt f hf
  have hdn : dn fpcr = false := h.2.2.2
  have hah : ah fpcr = false := h.2.1
  simp only [ResultIs, div, fpDiv, unpack_ieee h, processNaNs, processNaN, hah, hdn, defaultNaN_ieee h]
  cases h1 : classify f a <;> cases h2 : classify f b <;>
    cases hsa : signOf f a <;> cases hsb : signOf f b <;>
    simp [h1, h2, hsa, hsb, typeOf, isNaN, fpRound_ieee h, zero_lt, inf_lt,
      round_bits_lt, ha, hb, or_quiet_lt f hf, hd, hdl]
  all_goals first
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h1])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h2])
    | (unfold isNaN; rw [h1]) | (unfold isNaN; rw [h2])

end Janus.Arm64.FP

namespace Janus.Amd64.FP

open Janus.Float

variable {c : Ctl}

/-- `SUBSD`/`SUBSS` in IEEE mode. -/
theorem binop_sub_ieee (h : IEEEMode c) (f : Fmt) (hf : f.Std) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (binop .sub f c a b).res < 2 ^ f.width ∧
    ResultIs f (sub f (c.rc) a b) (binop .sub f c a b).res := by
  have hi := indefinite_classify f hf
  have hil := indefinite_lt f hf
  simp only [ResultIs, sub, binop, kindOf_ieee h, valOf_ieee h, nanResult, check]
  cases hx : addExact (valueOf f a).n (valueOf f a).e (-(valueOf f b).n) (valueOf f b).e <;>
  cases h1 : classify f a <;> cases h2 : classify f b <;>
    cases hsa : signOf f a <;> cases hsb : signOf f b <;>
    simp [h1, h2, hsa, hsb, isNaN, isSNaN, roundX_ieee h, rmi_beq, zero_lt, inf_lt, round_bits_lt, ha, hb,
      or_quiet_lt f hf, hi, hil, quiet]
  all_goals (try (rw [valueOf_of_zero h1, valueOf_of_zero h2] at hx; simp [Val.n, Val.e, addExact_zero] at hx))
  all_goals first
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h1])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h2])
    | (unfold isNaN; rw [h1]) | (unfold isNaN; rw [h2])

/-- `DIVSD`/`DIVSS` in IEEE mode. -/
theorem binop_div_ieee (h : IEEEMode c) (f : Fmt) (hf : f.Std) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (binop .div f c a b).res < 2 ^ f.width ∧
    ResultIs f (div f (c.rc) a b) (binop .div f c a b).res := by
  have hi := indefinite_classify f hf
  have hil := indefinite_lt f hf
  simp only [ResultIs, div, binop, kindOf_ieee h, valOf_ieee h, nanResult, check]
  cases h1 : classify f a <;> cases h2 : classify f b <;>
    cases hsa : signOf f a <;> cases hsb : signOf f b <;>
    simp [h1, h2, hsa, hsb, isNaN, isSNaN, roundX_ieee h, zero_lt, inf_lt, round_bits_lt, ha, hb,
      or_quiet_lt f hf, hi, hil, quiet]
  all_goals first
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h1])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h2])
    | (unfold isNaN; rw [h1]) | (unfold isNaN; rw [h2])

end Janus.Amd64.FP

/-! ## The results of the operations are never NaNs (binary64) -/

namespace Janus.Float

theorem b64_expOf_pack (s : Bool) (e fr : Nat) (he : e < 2 ^ 11) (hf : fr < 2 ^ 52) :
    expOf binary64 (pack binary64 s e fr) = e := by
  unfold expOf pack
  simp only [binary64, Fmt.signBit]
  cases s <;> simp <;> omega

theorem b64_isNaN_pack (s : Bool) (e fr : Nat) (he : e < 2047) (hf : fr < 2 ^ 52) :
    isNaN binary64 (pack binary64 s e fr) = false := by
  have h1 := b64_expOf_pack s e fr (by omega) hf
  cases h : isNaN binary64 (pack binary64 s e fr)
  · rfl
  · have := ((isNaN_iff binary64 (by decide) _).1 h).1
    rw [h1] at this
    simp [binary64, Fmt.expMax] at this; omega

theorem b64_isNaN_inf (s : Bool) : isNaN binary64 (inf binary64 s) = false := by cases s <;> decide
theorem b64_isNaN_zero (s : Bool) : isNaN binary64 (zero binary64 s) = false := by cases s <;> decide
theorem b64_isNaN_maxNormal (s : Bool) : isNaN binary64 (maxNormal binary64 s) = false := by
  cases s <;> decide

theorem b64_isNaN_round (rm : RM) (neg : Bool) (m : Nat) (e : Int) :
    isNaN binary64 (round binary64 rm neg m e).bits = false := by
  unfold round
  simp only
  split
  · split
    · exact b64_isNaN_inf _
    · exact b64_isNaN_maxNormal _
  · rename_i h
    rw [show ((binary64.expMax : Nat) : Int) = 2047 from rfl] at h
    exact b64_isNaN_pack _ _ _ (by omega) (Nat.mod_lt _ (by decide))

end Janus.Float
