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

end Janus.Amd64.FP
