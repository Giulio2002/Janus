import Janus.Spec.ComplexLemmas
import Janus.Arm64.ExecFloat

/-!
# Complex division on the machine models: lifted operations and comparisons (proved)

`NoNaN`: every IEEE operation's numeric result is a non-NaN encoding, so a register that holds a
result is a NaN exactly when the specification's result is `none` (`resultIs_nan_iff`). The
arm64 instructions with `FPCR = 0` deliver the operations of `Janus.Float.O` lifted to results
(`r_div`, `r_sub`, `r_mul`, `r_fma`, `r_neg`), and `FCMP` sets the flags by IEEE comparison
(`fcmp_flags`).
-/

set_option linter.unusedSimpArgs false

/-! ## Results that are numbers are not NaNs; the operations lifted to results -/

namespace Janus.Float

/-- A result that, when it is a number, is not a NaN encoding: every IEEE operation's result. -/
def NoNaN (X : Option Nat) : Prop := ∀ r, X = some r → isNaN binary64 r = false

theorem NoNaN.none : NoNaN none := fun _ h => by cases h

theorem resultIs_nan_iff {X : Option Nat} {x : Nat} (h : ResultIs binary64 X x) (hX : NoNaN X) :
    isNaN binary64 x = X.isNone := by
  cases X with
  | none => simpa [ResultIs] using h
  | some r => simp only [ResultIs] at h; subst h; simpa using hX x rfl

theorem noNaN_fin {r : Nat} (h : (∃ s, r = inf binary64 s) ∨ (∃ s, r = zero binary64 s) ∨
    ∃ rm neg m e, r = (round binary64 rm neg m e).bits) :
    isNaN binary64 r = false := by
  rcases h with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨rm, neg, m, e, rfl⟩
  · exact b64_isNaN_inf _
  · exact b64_isNaN_zero _
  · exact b64_isNaN_round _ _ _ _

macro "nonan_tac" : tactic => `(tactic| (
  intro r h; apply noNaN_fin
  simp only [Janus.Float.add, Janus.Float.sub, Janus.Float.mul, Janus.Float.div, Janus.Float.fma] at h
  repeat' split at h
  all_goals cases h
  all_goals first
    | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr ⟨_, _, _, _, rfl⟩)))

theorem add_noNaN (rm : RM) (a b : Nat) : NoNaN (add binary64 rm a b) := by nonan_tac
theorem sub_noNaN (rm : RM) (a b : Nat) : NoNaN (sub binary64 rm a b) := by nonan_tac
theorem mul_noNaN (rm : RM) (a b : Nat) : NoNaN (mul binary64 rm a b) := by nonan_tac
theorem div_noNaN (rm : RM) (a b : Nat) : NoNaN (div binary64 rm a b) := by nonan_tac
theorem fma_noNaN (rm : RM) (a b c : Nat) : NoNaN (fma binary64 rm a b c) := by nonan_tac

namespace O

theorem add2_noNaN (X Y : Option Nat) : NoNaN (add2 X Y) := by
  cases X <;> cases Y <;> simp [add2, NoNaN.none, add_noNaN]
theorem sub2_noNaN (X Y : Option Nat) : NoNaN (sub2 X Y) := by
  cases X <;> cases Y <;> simp [sub2, NoNaN.none, sub_noNaN]
theorem mul2_noNaN (X Y : Option Nat) : NoNaN (mul2 X Y) := by
  cases X <;> cases Y <;> simp [mul2, NoNaN.none, mul_noNaN]
theorem div2_noNaN (X Y : Option Nat) : NoNaN (div2 X Y) := by
  cases X <;> cases Y <;> simp [div2, NoNaN.none, div_noNaN]
theorem fma3_noNaN (X Y Z : Option Nat) : NoNaN (fma3 X Y Z) := by
  cases X <;> cases Y <;> cases Z <;> simp [fma3, NoNaN.none, fma_noNaN]
theorem mac_noNaN (u : Bool) (X Y Z : Option Nat) : NoNaN (mac u X Y Z) := by
  cases u <;> simp [mac, add2_noNaN, fma3_noNaN]
theorem msc_noNaN (u : Bool) (X Y Z : Option Nat) : NoNaN (msc u X Y Z) := by
  cases u <;> simp [msc, sub2_noNaN, fma3_noNaN]
theorem nms_noNaN (u : Bool) (X Y Z : Option Nat) : NoNaN (nms u X Y Z) := by
  cases u <;> simp [nms, sub2_noNaN, fma3_noNaN]

end O

theorem smith_noNaN (u : Bool) (a b c d : Nat) :
    NoNaN (smith u a b c d).1 ∧ NoNaN (smith u a b c d).2 := by
  unfold smith; split <;> exact ⟨O.div2_noNaN _ _, O.div2_noNaN _ _⟩

theorem b64_signBit : binary64.signBit = 2 ^ 63 := rfl

theorem isNaN_flipSign (x : Nat) :
    isNaN binary64 (flipSign binary64 x) = isNaN binary64 x := by
  have he : expOf binary64 (flipSign binary64 x) = expOf binary64 x := by
    unfold flipSign; rw [b64_signBit]
    cases signOf binary64 x <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      (show _ / 2 ^ 52 % 2 ^ 11 = _ / 2 ^ 52 % 2 ^ 11; omega)
  have hf : fracOf binary64 (flipSign binary64 x) = fracOf binary64 x := by
    unfold flipSign; rw [b64_signBit]
    cases signOf binary64 x <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      (show _ % 2 ^ 52 = _ % 2 ^ 52; omega)
  apply Bool.eq_iff_iff.2
  rw [isNaN_iff _ (by decide), isNaN_iff _ (by decide), he, hf]

theorem fma_comm (rm : RM) (a b c : Nat) : fma binary64 rm a b c = fma binary64 rm b a c := by
  unfold fma
  have hx : fmaExact (valueOf binary64 c).n (valueOf binary64 c).e (valueOf binary64 a).n
      (valueOf binary64 a).e (valueOf binary64 b).n (valueOf binary64 b).e =
      fmaExact (valueOf binary64 c).n (valueOf binary64 c).e (valueOf binary64 b).n
      (valueOf binary64 b).e (valueOf binary64 a).n (valueOf binary64 a).e := by
    simp [fmaExact, Int.mul_comm, Int.add_comm]
  rw [hx]
  cases isNaN binary64 a <;> cases isNaN binary64 b <;> cases signOf binary64 a <;>
    cases signOf binary64 b <;> cases classify binary64 a <;> cases classify binary64 b <;> simp

theorem expOf_flipSign (x : Nat) : expOf binary64 (flipSign binary64 x) = expOf binary64 x := by
  unfold flipSign; rw [b64_signBit]
  cases signOf binary64 x <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    (show _ / 2 ^ 52 % 2 ^ 11 = _ / 2 ^ 52 % 2 ^ 11; omega)

theorem fracOf_flipSign (x : Nat) : fracOf binary64 (flipSign binary64 x) = fracOf binary64 x := by
  unfold flipSign; rw [b64_signBit]
  cases signOf binary64 x <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    (show _ % 2 ^ 52 = _ % 2 ^ 52; omega)

theorem signOf_flipSign (x : Nat) : signOf binary64 (flipSign binary64 x) = !signOf binary64 x := by
  unfold flipSign
  cases h : signOf binary64 x <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false,
    Bool.not_true] <;> rw [b64_signBit] <;> unfold signOf <;> rw [b64_signBit] <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] <;> omega

theorem classify_flipSign (x : Nat) : classify binary64 (flipSign binary64 x) = classify binary64 x := by
  unfold classify; rw [expOf_flipSign, fracOf_flipSign]

theorem valueOf_flipSign_n (x : Nat) : (valueOf binary64 (flipSign binary64 x)).n = -(valueOf binary64 x).n := by
  unfold valueOf mantOf; rw [classify_flipSign, signOf_flipSign, expOf_flipSign, fracOf_flipSign]
  cases classify binary64 x <;> cases signOf binary64 x <;> simp [Val.n]

theorem valueOf_flipSign_e (x : Nat) : (valueOf binary64 (flipSign binary64 x)).e = (valueOf binary64 x).e := by
  unfold valueOf ulpExpOf; rw [classify_flipSign, expOf_flipSign]
  cases classify binary64 x <;> cases signOf binary64 (flipSign binary64 x) <;> simp [Val.e]

theorem fmaExact_neg (na ea n1 e1 n2 e2 : Int) :
    fmaExact na ea (-n1) e1 n2 e2 = fmaExact na ea n1 e1 (-n2) e2 := by
  simp [fmaExact, Int.neg_mul, Int.mul_neg]

/-- `(-x) × y + z = x × (-y) + z`. -/
theorem fma_negswap (rm : RM) (x y z : Nat) :
    fma binary64 rm (flipSign binary64 x) y z = fma binary64 rm x (flipSign binary64 y) z := by
  unfold fma
  simp only [isNaN_flipSign, classify_flipSign, signOf_flipSign, valueOf_flipSign_n,
    valueOf_flipSign_e, fmaExact_neg]
  cases signOf binary64 x <;> cases signOf binary64 y <;> rfl

end Janus.Float

/-! ## arm64: the instructions deliver the lifted operations (`FPCR = 0`) -/

namespace Janus.Arm64.FP

open Janus.Float

theorem b64Std : binary64.Std := Or.inr rfl
theorem rm0 : roundingMode 0 = .rne := rfl

variable {X Y Z : Option Nat} {x y z : Nat}

theorem fpDiv_lt (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : (fpDiv binary64 0 x y).1 < 2 ^ 64 :=
  (fpDiv_ieee IEEEMode.zero binary64 b64Std x y hx hy).1
theorem fpSub_lt (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : (fpSub binary64 0 x y).1 < 2 ^ 64 :=
  (fpSub_ieee IEEEMode.zero binary64 b64Std x y hx hy).1
theorem fpMul_lt (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : (fpMul binary64 0 x y).1 < 2 ^ 64 :=
  (fpMul_ieee IEEEMode.zero binary64 b64Std x y hx hy).1
theorem fpMulAdd_lt (z x y : Nat) (hz : z < 2 ^ 64) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (fpMulAdd binary64 0 z x y).1 < 2 ^ 64 :=
  (fpMulAdd_ieee IEEEMode.zero binary64 b64Std z x y hz hx hy).1
theorem fpNeg_ieee (x : Nat) : fpNeg binary64 0 x = flipSign binary64 x := by
  simp [fpNeg, ah, fpcrBit]

theorem fpNeg_lt (x : Nat) : fpNeg binary64 0 x < 2 ^ 64 := by
  rw [fpNeg_ieee]; unfold flipSign; rw [b64_signBit]
  cases signOf binary64 x <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem r_div (hx : ResultIs binary64 X x) (hy : ResultIs binary64 Y y) (hxl : x < 2 ^ 64)
    (hyl : y < 2 ^ 64) : ResultIs binary64 (O.div2 X Y) (fpDiv binary64 0 x y).1 := by
  have h := (fpDiv_ieee IEEEMode.zero binary64 b64Std x y hxl hyl).2
  rw [rm0] at h
  cases X with
  | none => simp only [ResultIs] at hx; simp only [O.div2, Option.bind_none]
            rwa [show div binary64 .rne x y = none by simp [div, hx]] at h
  | some a =>
    simp only [ResultIs] at hx; subst hx
    cases Y with
    | none => simp only [ResultIs] at hy; simp only [O.div2, Option.bind_some, Option.bind_none]
              rwa [show div binary64 .rne x y = none by simp [div, hy]] at h
    | some b => simp only [ResultIs] at hy; subst hy; simpa [O.div2] using h

theorem r_sub (hx : ResultIs binary64 X x) (hy : ResultIs binary64 Y y) (hxl : x < 2 ^ 64)
    (hyl : y < 2 ^ 64) : ResultIs binary64 (O.sub2 X Y) (fpSub binary64 0 x y).1 := by
  have h := (fpSub_ieee IEEEMode.zero binary64 b64Std x y hxl hyl).2
  rw [rm0] at h
  cases X with
  | none => simp only [ResultIs] at hx; simp only [O.sub2, Option.bind_none]
            rwa [show sub binary64 .rne x y = none by simp [sub, hx]] at h
  | some a =>
    simp only [ResultIs] at hx; subst hx
    cases Y with
    | none => simp only [ResultIs] at hy; simp only [O.sub2, Option.bind_some, Option.bind_none]
              rwa [show sub binary64 .rne x y = none by simp [sub, hy]] at h
    | some b => simp only [ResultIs] at hy; subst hy; simpa [O.sub2] using h

theorem r_mul (hx : ResultIs binary64 X x) (hy : ResultIs binary64 Y y) (hxl : x < 2 ^ 64)
    (hyl : y < 2 ^ 64) : ResultIs binary64 (O.mul2 X Y) (fpMul binary64 0 x y).1 := by
  have h := (fpMul_ieee IEEEMode.zero binary64 b64Std x y hxl hyl).2
  rw [rm0] at h
  cases X with
  | none => simp only [ResultIs] at hx; simp only [O.mul2, Option.bind_none]
            rwa [show mul binary64 .rne x y = none by simp [mul, hx]] at h
  | some a =>
    simp only [ResultIs] at hx; subst hx
    cases Y with
    | none => simp only [ResultIs] at hy; simp only [O.mul2, Option.bind_some, Option.bind_none]
              rwa [show mul binary64 .rne x y = none by simp [mul, hy]] at h
    | some b => simp only [ResultIs] at hy; subst hy; simpa [O.mul2] using h

/-- `FPMulAdd(z, x, y)` is `x × y + z` rounded once. -/
theorem r_fma (hx : ResultIs binary64 X x) (hy : ResultIs binary64 Y y) (hz : ResultIs binary64 Z z)
    (hxl : x < 2 ^ 64) (hyl : y < 2 ^ 64) (hzl : z < 2 ^ 64) :
    ResultIs binary64 (O.fma3 X Y Z) (fpMulAdd binary64 0 z x y).1 := by
  have h := (fpMulAdd_ieee IEEEMode.zero binary64 b64Std z x y hzl hxl hyl).2
  rw [rm0] at h
  cases X with
  | none => simp only [ResultIs] at hx; simp only [O.fma3, Option.bind_none]
            rwa [show fma binary64 .rne x y z = none by simp [fma, hx]] at h
  | some a =>
    simp only [ResultIs] at hx; subst hx
    cases Y with
    | none => simp only [ResultIs] at hy; simp only [O.fma3, Option.bind_some, Option.bind_none]
              rwa [show fma binary64 .rne x y z = none by simp [fma, hy]] at h
    | some b =>
      simp only [ResultIs] at hy; subst hy
      cases Z with
      | none => simp only [ResultIs] at hz; simp only [O.fma3, Option.bind_some, Option.bind_none]
                rwa [show fma binary64 .rne x y z = none by simp [fma, hz]] at h
      | some c => simp only [ResultIs] at hz; subst hz; simpa [O.fma3] using h

theorem r_neg (hx : ResultIs binary64 X x) :
    ResultIs binary64 (O.neg X) (fpNeg binary64 0 x) := by
  rw [fpNeg_ieee]
  cases X with
  | none => simp only [ResultIs] at hx; simp only [O.neg, Option.map_none, ResultIs]
            rw [isNaN_flipSign x]; exact hx
  | some a => simp only [ResultIs] at hx; subst hx; rfl

theorem r_some (x : Nat) : ResultIs binary64 (some x) x := rfl

/-- `FCMP x, y` as flags (`FPCR = 0`): `N` for less, `Z` for equal, `C` unless less, `V` for
unordered. -/
def cmpN (x y : Nat) : Bool :=
  !(isNaN binary64 x || isNaN binary64 y) && !Val.eq (valueOf binary64 x) (valueOf binary64 y) &&
    Val.lt (valueOf binary64 x) (valueOf binary64 y)

theorem fcmp_flags (sig : Bool) (x y : Nat) :
    flagsOfNzcv (fpCompare binary64 0 sig x y).1 =
      { n := cmpN x y, z := eq64 x y, c := !cmpN x y, v := isNaN binary64 x || isNaN binary64 y } := by
  rw [fpCompare_ieee IEEEMode.zero]
  unfold cmpN eq64
  cases hn : (isNaN binary64 x || isNaN binary64 y) <;>
    cases he : Val.eq (valueOf binary64 x) (valueOf binary64 y) <;>
    cases hl : Val.lt (valueOf binary64 x) (valueOf binary64 y) <;> simp [flagsOfNzcv]

theorem Val.eq_refl' (v : Val) : Val.eq v v = true := by
  cases v <;> simp [Val.eq, align]

theorem Val.eq_comm' (v w : Val) : Val.eq v w = Val.eq w v := by
  cases v with
  | num n e => cases w with
    | num n' e' => simp only [Val.eq, align]; rw [Int.min_comm e' e]; exact Bool.beq_comm
    | inf _ => rfl
  | inf s => cases w with
    | num _ _ => rfl
    | inf t => simp only [Val.eq]; exact Bool.beq_comm

theorem eq64_self (x : Nat) : eq64 x x = !isNaN binary64 x := by
  simp [eq64, Val.eq_refl']

theorem cmpN_self (x : Nat) : cmpN x x = false := by
  simp [cmpN, Val.eq_refl']

/-- `FCMP |d|, |c|` then `B.HI`: taken exactly when not `|c| >= |d|`. -/
theorem hi_ge (x y : Nat) : (!cmpN y x && !eq64 y x) = !ge64 x y := by
  unfold cmpN eq64 ge64
  rw [Val.eq_comm' (valueOf binary64 y)]
  cases isNaN binary64 x <;> cases isNaN binary64 y <;>
    cases Val.eq (valueOf binary64 x) (valueOf binary64 y) <;>
    cases Val.lt (valueOf binary64 y) (valueOf binary64 x) <;> rfl

end Janus.Arm64.FP
