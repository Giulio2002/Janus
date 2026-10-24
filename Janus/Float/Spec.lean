import Janus.Float.Core

/-!
# IEEE 754 operations as specifications

Architecture-independent statements of the IEEE 754-2019 operations the examples use, in a
form that theorems can state results with: the encoding of the correctly rounded result
(§4.3, §5.4.1, §6.1, §6.3), or `none` when the result is a NaN (a NaN operand, or an invalid
operation, §7.2). Which NaN an architecture delivers differs (Arm: the first signalling, else
the first quiet operand, quieted; x86: the first operand that is a NaN; both: a default NaN
of their own for invalid operations), and IEEE 754 does not fix it (§6.2.3), so the
specifications only say "a NaN" there. The exception flags are not part of these
specifications.

The definitions are built from the same core as the architecture models (`Janus.Float`), so a
theorem stated with them says: the machine computed exactly the IEEE result.
-/

namespace Janus.Float

/-- The encoding `x` delivered by a machine is the result `spec` of an IEEE operation: exactly
`r` when the IEEE result is the number (or infinity) encoded by `r`, and some NaN when the IEEE
result is a NaN (`spec = none`). -/
def ResultIs (f : Fmt) (spec : Option Nat) (x : Nat) : Prop :=
  match spec with
  | some r => x = r
  | none => isNaN f x = true

/-- `a + b` (IEEE 754 `addition`, §5.4.1) in rounding direction `rm`: the encoding of the
result, or `none` for a NaN result (a NaN operand, or `+∞ + -∞`, §7.2). Infinities give an
infinity of their sign (§6.1); the sum of two zeros of the same sign is that zero, any other
exact zero sum is `+0`, or `-0` under `roundTowardNegative` (§6.3); otherwise the exact sum is
rounded (§4.3). -/
def add (f : Fmt) (rm : RM) (a b : Nat) : Option Nat :=
  if isNaN f a || isNaN f b then none else
  let inf1 := classify f a = .inf
  let inf2 := classify f b = .inf
  let s1 := signOf f a
  let s2 := signOf f b
  if inf1 && inf2 && s1 != s2 then none
  else if (inf1 && !s1) || (inf2 && !s2) then some (inf f false)
  else if (inf1 && s1) || (inf2 && s2) then some (inf f true)
  else if classify f a = .zero && classify f b = .zero && s1 == s2 then some (zero f s1)
  else match addExact (valueOf f a).n (valueOf f a).e (valueOf f b).n (valueOf f b).e with
    | none => some (zero f (rm == .rmi))
    | some (neg, m, e) => some (round f rm neg m e).bits

/-- `a × b` (IEEE 754 `multiplication`, §5.4.1): `none` for a NaN result (a NaN operand or
`0 × ∞`); an infinite or zero operand gives an infinity or a zero with the exclusive-or of the
signs; otherwise the exact product is rounded. -/
def mul (f : Fmt) (rm : RM) (a b : Nat) : Option Nat :=
  if isNaN f a || isNaN f b then none else
  let inf1 := classify f a = .inf
  let inf2 := classify f b = .inf
  let zero1 := classify f a = .zero
  let zero2 := classify f b = .zero
  let s := signOf f a != signOf f b
  if (inf1 && zero2) || (zero1 && inf2) then none
  else if inf1 || inf2 then some (inf f s)
  else if zero1 || zero2 then some (zero f s)
  else match mulExact (valueOf f a).n (valueOf f a).e (valueOf f b).n (valueOf f b).e with
    | none => some (zero f s)
    | some (neg, m, e) => some (round f rm neg m e).bits

/-- `a × b + c` computed with a single rounding (IEEE 754 `fusedMultiplyAdd`, §5.4.1): `none`
for a NaN result (a NaN operand, `0 × ∞`, or an infinite product and an infinite `c` of
opposite signs). An exact zero result is the zero of the common sign when the product and `c`
are zeros of the same sign, and otherwise `+0` (`-0` under `roundTowardNegative`). -/
def fma (f : Fmt) (rm : RM) (a b c : Nat) : Option Nat :=
  if isNaN f c || isNaN f a || isNaN f b then none else
  let inf1 := classify f a = .inf
  let inf2 := classify f b = .inf
  let zero1 := classify f a = .zero
  let zero2 := classify f b = .zero
  let infA := classify f c = .inf
  let zeroA := classify f c = .zero
  let sA := signOf f c
  let sP := signOf f a != signOf f b
  let infP := inf1 || inf2
  let zeroP := zero1 || zero2
  if (inf1 && zero2) || (zero1 && inf2) || (infA && infP && sA != sP) then none
  else if (infA && !sA) || (infP && !sP) then some (inf f false)
  else if (infA && sA) || (infP && sP) then some (inf f true)
  else if zeroA && zeroP && sA == sP then some (zero f sA)
  else match fmaExact (valueOf f c).n (valueOf f c).e (valueOf f a).n (valueOf f a).e
      (valueOf f b).n (valueOf f b).e with
    | none => some (zero f (rm == .rmi))
    | some (neg, m, e) => some (round f rm neg m e).bits

/-- `|x|` (IEEE 754 `abs`, §5.5.1): the encoding with the sign bit cleared, for every `x`,
NaNs included. -/
def abs (f : Fmt) (x : Nat) : Nat := clearSign f x

/-- The value of a finite encoding `x` truncated toward zero to an integer
(`convertToIntegerTowardZero`, §5.8), or `none` for a NaN or an infinity. -/
def truncInt (f : Fmt) (x : Nat) : Option Int :=
  match classify f x with
  | .qnan | .snan | .inf => none
  | .zero => some 0
  | _ => some (roundToInt .rz (signOf f x) (mantOf f x) (ulpExpOf f x)).1

end Janus.Float
