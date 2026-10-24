import Janus.Float.Lemmas
import Janus.Arm64.Float

/-!
# The Arm floating-point model in IEEE mode (proved, not trusted)

With `FPCR.{FIZ, AH, FZ, DN} = 0` (`IEEEMode`) the ASL functions compute the IEEE 754
operations of `Janus.Float.Spec` in the rounding direction `FPCR.RMode`, and deliver a NaN
exactly when the specification's result is a NaN. These lemmas connect the theorems about
compiled code (stated with the IEEE specifications) to the model.
-/

set_option linter.unusedSimpArgs false

namespace Janus.Arm64.FP

open Janus.Float

/-- `FPCR` selects plain IEEE 754 behaviour: no input or output flushing, no alternate
handling, NaNs propagate (any rounding mode, any trap enables, any `NEP`). -/
def IEEEMode (fpcr : Nat) : Prop :=
  fiz fpcr = false ∧ ah fpcr = false ∧ fz fpcr = false ∧ dn fpcr = false

theorem IEEEMode.zero : IEEEMode 0 := by refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `FPType` of an encoding when nothing is flushed. -/
def typeOf (f : Fmt) (x : Nat) : FPType :=
  match classify f x with
  | .zero => .zero | .subnormal => .denormal | .normal => .nonzero | .inf => .infinity
  | .qnan => .qnan | .snan => .snan

variable {fpcr : Nat}

theorem unpack_ieee (h : IEEEMode fpcr) (f : Fmt) (fpexc : Bool) (x : Nat) :
    unpack f fpcr fpexc x = ((typeOf f x, signOf f x, valueOf f x), {}) := by
  obtain ⟨h1, h2, h3, _⟩ := h
  unfold unpack typeOf valueOf
  cases classify f x <;> simp [h1, h2, h3]

theorem fpRound_ieee (h : IEEEMode fpcr) (f : Fmt) (rm : RM) (neg : Bool) (m : Nat) (e : Int) :
    (fpRound f fpcr rm neg m e).1 = (round f rm neg m e).bits := by
  obtain ⟨_, h2, h3, _⟩ := h
  simp [fpRound, h2, h3]

theorem defaultNaN_ieee (h : IEEEMode fpcr) (f : Fmt) : defaultNaN f fpcr = defaultNaN f 0 := by
  obtain ⟨_, h2, _, _⟩ := h; rw [defaultNaN, h2]; rfl

theorem defaultNaN_isNaN (f : Fmt) (hf : f.Std) : isNaN f (defaultNaN f 0) = true := by
  rcases hf with rfl | rfl <;> decide

theorem classify_defaultNaN (f : Fmt) (hf : f.Std) : classify f (defaultNaN f 0) = .qnan := by
  rcases hf with rfl | rfl <;> decide

theorem defaultNaN_lt (f : Fmt) (hf : f.Std) : defaultNaN f 0 < 2 ^ f.width := by
  rcases hf with rfl | rfl <;> decide

theorem rne_ne_rmi {rm : RM} : (rm == .rmi) = decide (rm = .rmi) := by cases rm <;> rfl

/-- `FPAdd` in IEEE mode: an encoding, the IEEE sum when that is not a NaN, else a NaN. -/
theorem fpAdd_ieee (h : IEEEMode fpcr) (f : Fmt) (hf : f.Std) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (fpAdd f fpcr a b).1 < 2 ^ f.width ∧
    ResultIs f (add f (roundingMode fpcr) a b) (fpAdd f fpcr a b).1 := by
  have hd := classify_defaultNaN f hf
  have hdl := defaultNaN_lt f hf
  have hdn : dn fpcr = false := h.2.2.2
  have hah : ah fpcr = false := h.2.1
  simp only [ResultIs, add, fpAdd, unpack_ieee h, processNaNs, processNaN, hah, hdn, defaultNaN_ieee h]
  cases hx : addExact (valueOf f a).n (valueOf f a).e (valueOf f b).n (valueOf f b).e <;>
  cases h1 : classify f a <;> cases h2 : classify f b <;>
    cases hsa : signOf f a <;> cases hsb : signOf f b <;>
    simp [h1, h2, hsa, hsb, typeOf, isNaN, fpRound_ieee h, rne_ne_rmi, zero_lt, inf_lt,
      round_bits_lt, ha, hb, or_quiet_lt f hf, hd, hdl]
  all_goals first
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h1])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h2])
    | (unfold isNaN; rw [h1]) | (unfold isNaN; rw [h2])

/-- `FPMul` in IEEE mode. -/
theorem fpMul_ieee (h : IEEEMode fpcr) (f : Fmt) (hf : f.Std) (a b : Nat)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (fpMul f fpcr a b).1 < 2 ^ f.width ∧
    ResultIs f (mul f (roundingMode fpcr) a b) (fpMul f fpcr a b).1 := by
  have hd := classify_defaultNaN f hf
  have hdl := defaultNaN_lt f hf
  have hdn : dn fpcr = false := h.2.2.2
  have hah : ah fpcr = false := h.2.1
  simp only [ResultIs, mul, fpMul, unpack_ieee h, processNaNs, processNaN, hah, hdn, defaultNaN_ieee h]
  cases hx : mulExact (valueOf f a).n (valueOf f a).e (valueOf f b).n (valueOf f b).e <;>
  cases h1 : classify f a <;> cases h2 : classify f b <;>
    cases hsa : signOf f a <;> cases hsb : signOf f b <;>
    simp [h1, h2, hsa, hsb, typeOf, isNaN, fpRound_ieee h, zero_lt, inf_lt,
      round_bits_lt, ha, hb, or_quiet_lt f hf, hd, hdl]
  all_goals first
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h1])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h2])
    | (unfold isNaN; rw [h1]) | (unfold isNaN; rw [h2])

set_option maxHeartbeats 2000000 in
/-- `FPMulAdd(addend, op1, op2)` in IEEE mode: `op1 × op2 + addend` rounded once. -/
theorem fpMulAdd_ieee (h : IEEEMode fpcr) (f : Fmt) (hf : f.Std) (c a b : Nat)
    (hc : c < 2 ^ f.width) (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (fpMulAdd f fpcr c a b).1 < 2 ^ f.width ∧
    ResultIs f (fma f (roundingMode fpcr) a b c) (fpMulAdd f fpcr c a b).1 := by
  have hd := classify_defaultNaN f hf
  have hdl := defaultNaN_lt f hf
  have hdn : dn fpcr = false := h.2.2.2
  have hah : ah fpcr = false := h.2.1
  simp only [ResultIs, fma, fpMulAdd, unpack_ieee h, processNaNs3, processNaN, hah, hdn, defaultNaN_ieee h]
  cases hx : fmaExact (valueOf f c).n (valueOf f c).e (valueOf f a).n (valueOf f a).e
      (valueOf f b).n (valueOf f b).e <;>
  cases h0 : classify f c <;> cases h1 : classify f a <;> cases h2 : classify f b <;>
    simp [h0, h1, h2, typeOf, isNaN, fpRound_ieee h, rne_ne_rmi, zero_lt, inf_lt,
      round_bits_lt, ha, hb, hc, or_quiet_lt f hf, hd, hdl]
  all_goals try (cases hsc : signOf f c <;> cases hsa : signOf f a <;> cases hsb : signOf f b <;>
    simp [hsc, hsa, hsb, h0, h1, h2, zero_lt, inf_lt, hd, hdl, fpRound_ieee h, round_bits_lt, rne_ne_rmi])
  all_goals first
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h0])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h1])
    | exact isNaN_or_quiet f hf _ (by unfold isNaN; rw [h2])
    | (unfold isNaN; rw [h0]) | (unfold isNaN; rw [h1]) | (unfold isNaN; rw [h2])

theorem roundToInt_zero (rm : RM) (s : Bool) (e : Int) : (roundToInt rm s 0 e).1 = 0 := by
  unfold roundToInt; split <;> simp [roundUp]

theorem natAbs_signed (s : Bool) (m : Nat) : (if s = true then -(m : Int) else m).natAbs = m := by
  cases s <;> simp

theorem signed_eq_zero (s : Bool) (m : Nat) : (if s = true then -(m : Int) else m) = 0 ↔ m = 0 := by
  cases s <;> simp

theorem satQ_unsigned (M : Nat) (i : Int) (h0 : 0 ≤ i) (h1 : i < 2 ^ M) :
    (satQ M true i).1 = i.toNat := by
  unfold satQ; simp; split
  · omega
  · split <;> omega

/-- `FPToFixed(op, 0, TRUE, fpcr, RZ, 64)` (`FCVTZU Xd, Dn`) in IEEE mode on a value whose
truncation is a 64-bit unsigned integer: that integer. -/
theorem fpToFixed_rzu_ieee (h : IEEEMode fpcr) (f : Fmt) (x : Nat) (i : Int)
    (hi : truncInt f x = some i) (h0 : 0 ≤ i) (h1 : i < 2 ^ 64) :
    (fpToFixed f fpcr true .rz 64 x).1 = i.toNat := by
  have hah : ah fpcr = false := h.2.1
  simp only [fpToFixed, unpack_ieee h, hah]
  unfold truncInt at hi
  unfold valueOf
  cases hc : classify f x <;> simp [hc] at hi ⊢
  · subst hi; exact satQ_unsigned 64 0 (by omega) (by omega)
  all_goals
    rw [natAbs_signed]
    by_cases hm : mantOf f x = 0
    · simp only [signed_eq_zero, hm, if_true]
      rw [hm, roundToInt_zero] at hi; subst hi; exact satQ_unsigned 64 0 (by omega) (by omega)
    · simp only [signed_eq_zero, hm, if_false]
      rw [hi]; exact satQ_unsigned 64 i h0 h1

end Janus.Arm64.FP
