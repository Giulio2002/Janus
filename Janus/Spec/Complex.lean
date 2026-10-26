import Janus.Float.Lemmas

/-!
# Complex division as Go implements it, as a specification

Go 1.26 compiles `n / m` on `complex128` to a call of `runtime.complex128div` (`runtime/complex.go`):
Smith's algorithm (R. L. Smith, Algorithm 116, CACM 5(8), 1962), followed by the recovery of
infinities and zeros of C99 Annex G.5.1 when both parts come out NaN. `cdiv` is that algorithm
over the IEEE 754 operations of `Janus.Float.Spec` (round to nearest even), with `none` standing
for a NaN (`ResultIs`): the theorems about the machine code say that the two result registers
hold exactly these results.

**Fused operations.** The Go specification lets an implementation fuse `x*y + z` ("An
implementation may combine multiple floating-point operations into a single fused operation,
possibly across statements"), and the arm64 compiler does (`FMADDD`, `FMSUBD`, `FNMSUBD`) where
amd64 (`GOAMD64=v1`, no FMA) rounds the product and the sum separately. `cdiv true` is the
arm64 algorithm, `cdiv false` the amd64 one; the fused sites are exactly those of the compiled
code (`mac`, `msc`, `nms`).

**Annex G.** `annexG_by_zero`, `annexG_by_inf` and `annexG_inf_by` evaluate (in the kernel) the
three recoveries that motivate the fixup, for both forms: `1 / 0 = (+∞, NaN)` (a finite non-zero
numerator over a zero gives an infinite part), `(1 + i) / ∞ = (0, 0)` (a finite numerator over an
infinite denominator gives zeros) and `∞ / (1 + i) = (+∞, -∞)` (an infinite numerator over a finite
non-zero denominator gives infinite parts). Smith's algorithm alone gives two NaNs in each case.
-/

namespace Janus.Float

/-! ## Subtraction and division (IEEE 754 §5.4.1) -/

/-- `a - b` (IEEE 754 `subtraction`, §5.4.1): `a + (-b)`, written out as `add` with the sign of
`b` flipped (§6.3): `none` for a NaN result (a NaN operand, or `∞ - ∞` of equal signs). -/
def sub (f : Fmt) (rm : RM) (a b : Nat) : Option Nat :=
  if isNaN f a || isNaN f b then none else
  let inf1 := classify f a = .inf
  let inf2 := classify f b = .inf
  let s1 := signOf f a
  let s2 := !signOf f b
  if inf1 && inf2 && s1 != s2 then none
  else if (inf1 && !s1) || (inf2 && !s2) then some (inf f false)
  else if (inf1 && s1) || (inf2 && s2) then some (inf f true)
  else if classify f a = .zero && classify f b = .zero && s1 == s2 then some (zero f s1)
  else match addExact (valueOf f a).n (valueOf f a).e (-(valueOf f b).n) (valueOf f b).e with
    | none => some (zero f (rm == .rmi))
    | some (neg, m, e) => some (round f rm neg m e).bits

/-- `a / b` (IEEE 754 `division`, §5.4.1): `none` for a NaN result (a NaN operand, `0/0`,
`∞/∞`, §7.2); `x/0` for non-zero `x` and `∞/x` give an infinity, `0/x` and `x/∞` a zero, both
with the exclusive-or of the signs (§6.1, §7.3); otherwise the exact quotient rounded (the
quotient's round-to-odd form `divOdd`, which rounds like the exact value, `Janus.Float.Core`). -/
def div (f : Fmt) (rm : RM) (a b : Nat) : Option Nat :=
  if isNaN f a || isNaN f b then none else
  let inf1 := classify f a = .inf
  let inf2 := classify f b = .inf
  let zero1 := classify f a = .zero
  let zero2 := classify f b = .zero
  let s := signOf f a != signOf f b
  if (inf1 && inf2) || (zero1 && zero2) then none
  else if inf1 || zero2 then some (inf f s)
  else if zero1 || inf2 then some (zero f s)
  else
    let (m1, e1) := (valueOf f a).mag
    let (m2, e2) := (valueOf f b).mag
    let (m, e) := divOdd f.fbits m1 e1 m2 e2
    some (round f rm s m e).bits

/-! ## Operations on results (`none` = a NaN)

A NaN operand gives a NaN result in every IEEE operation (§6.2), so the operations extend to
results by `none ↦ none`. -/

namespace O

def add2 (x y : Option Nat) : Option Nat := x.bind fun a => y.bind fun b => add binary64 .rne a b
def sub2 (x y : Option Nat) : Option Nat := x.bind fun a => y.bind fun b => sub binary64 .rne a b
def mul2 (x y : Option Nat) : Option Nat := x.bind fun a => y.bind fun b => mul binary64 .rne a b
def div2 (x y : Option Nat) : Option Nat := x.bind fun a => y.bind fun b => div binary64 .rne a b
/-- `x × y + z` rounded once. -/
def fma3 (x y z : Option Nat) : Option Nat :=
  x.bind fun a => y.bind fun b => z.bind fun c => fma binary64 .rne a b c
/-- `-x` (the sign flipped; a NaN stays a NaN). -/
def neg (x : Option Nat) : Option Nat := x.map (flipSign binary64)

/-- `x × y + z`, fused or not. -/
def mac (fused : Bool) (x y z : Option Nat) : Option Nat :=
  if fused then fma3 x y z else add2 (mul2 x y) z
/-- `z - x × y`, fused (`FMSUB`: `(-x) × y + z`) or not. -/
def msc (fused : Bool) (x y z : Option Nat) : Option Nat :=
  if fused then fma3 (neg x) y z else sub2 z (mul2 x y)
/-- `x × y - z`, fused (`FNMSUB`: `x × y + (-z)`) or not. -/
def nms (fused : Bool) (x y z : Option Nat) : Option Nat :=
  if fused then fma3 x y (neg z) else sub2 (mul2 x y) z

end O

/-! ## The predicates of `runtime/float.go`, on encodings -/

/-- `x != x`. -/
def isNaN64 (x : Nat) : Bool := isNaN binary64 x
/-- `isFinite(x) = !isNaN(x - x)`. -/
def isFinite64 (x : Nat) : Bool := (sub binary64 .rne x x).isSome
/-- `isInf(x) = !isNaN(x) && !isFinite(x)`. -/
def isInf64 (x : Nat) : Bool := !isNaN64 x && !isFinite64 x
/-- `x == y`, IEEE equality (false when either is a NaN; `+0 == -0`). -/
def eq64 (x y : Nat) : Bool :=
  !(isNaN binary64 x || isNaN binary64 y) && Val.eq (valueOf binary64 x) (valueOf binary64 y)
/-- `x == 0` (IEEE equality with `+0`: true exactly for the two zeros, `isZero64_iff`). -/
def isZero64 (x : Nat) : Bool := eq64 x (zero binary64 false)
/-- `x >= y`, IEEE ordered comparison (false when either is a NaN). -/
def ge64 (x y : Nat) : Bool :=
  !(isNaN binary64 x || isNaN binary64 y) &&
    (Val.eq (valueOf binary64 x) (valueOf binary64 y) || Val.lt (valueOf binary64 y) (valueOf binary64 x))
/-- `copysign(x, y)`: the magnitude of `x`, the sign of `y` (bit operations). -/
def copysign (x y : Nat) : Nat := clearSign binary64 x + (if signOf binary64 y then binary64.signBit else 0)
/-- `inf2one(f)`: a signed 1 if `f` is an infinity, a signed 0 otherwise, the sign of `f`. -/
def inf2one (x : Nat) : Nat := copysign (if isInf64 x then 0x3FF0000000000000 else 0) x
/-- `runtime.inf`. -/
def infE : Nat := 0x7FF0000000000000

/-! ## `runtime.complex128div` -/

/-- Smith's algorithm, the first half of `complex128div`: the quotient `(e, f)` before the
Annex G recovery, fused (arm64) or not (amd64). -/
def smith (fused : Bool) (a b c d : Nat) : Option Nat × Option Nat :=
  let A := some a
  let B := some b
  let C := some c
  let D := some d
  if ge64 (abs binary64 c) (abs binary64 d) then
    let ratio := O.div2 D C
    let denom := O.mac fused D ratio C
    (O.div2 (O.mac fused B ratio A) denom, O.div2 (O.msc fused A ratio B) denom)
  else
    let ratio := O.div2 C D
    let denom := O.mac fused C ratio D
    (O.div2 (O.mac fused A ratio B) denom, O.div2 (O.nms fused B ratio A) denom)

/-- The recovery of infinities and zeros (C99 Annex G.5.1) when both parts of Smith's quotient
are NaNs: the result for numerator `a + bi`, denominator `c + di` and Smith's `(e, f)`. -/
def recover (fused : Bool) (a b c d : Nat) (ef : Option Nat × Option Nat) : Option Nat × Option Nat :=
  let A := some a
  let B := some b
  let C := some c
  let D := some d
  match ef with
  | (none, none) =>
    if isZero64 c && isZero64 d && (!isNaN64 a || !isNaN64 b) then
      (O.mul2 (some (copysign infE c)) A, O.mul2 (some (copysign infE c)) B)
    else if (isInf64 a || isInf64 b) && isFinite64 c && isFinite64 d then
      let a' := some (inf2one a)
      let b' := some (inf2one b)
      (O.mul2 (some infE) (O.mac fused b' D (O.mul2 a' C)),
       O.mul2 (some infE) (O.msc fused a' D (O.mul2 b' C)))
    else if (isInf64 c || isInf64 d) && isFinite64 a && isFinite64 b then
      let c' := some (inf2one c)
      let d' := some (inf2one d)
      (O.mul2 (some 0) (O.mac fused B d' (O.mul2 A c')),
       O.mul2 (some 0) (O.msc fused A d' (O.mul2 B c')))
    else (none, none)
  | ef => ef

/-- `complex128div(complex(a, b), complex(c, d))` (`runtime/complex.go`), fused (arm64) or not
(amd64): the real and imaginary parts. -/
def cdiv (fused : Bool) (a b c d : Nat) : Option Nat × Option Nat :=
  recover fused a b c d (smith fused a b c d)

/-! ## The Annex G recoveries, evaluated -/

theorem annexG_by_zero (u : Bool) :
    cdiv u 0x3FF0000000000000 0 0 0 = (some 0x7FF0000000000000, none) := by
  cases u <;> decide +kernel

theorem annexG_by_inf (u : Bool) :
    cdiv u 0x3FF0000000000000 0x3FF0000000000000 0x7FF0000000000000 0 = (some 0, some 0) := by
  cases u <;> decide +kernel

theorem annexG_inf_by (u : Bool) :
    cdiv u 0x7FF0000000000000 0 0x3FF0000000000000 0x3FF0000000000000 =
      (some 0x7FF0000000000000, some 0xFFF0000000000000) := by
  cases u <;> decide +kernel

theorem smith_by_zero (u : Bool) : smith u 0x3FF0000000000000 0 0 0 = (none, none) := by
  cases u <;> decide +kernel

end Janus.Float
