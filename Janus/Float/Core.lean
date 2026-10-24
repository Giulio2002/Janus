/-!
# A bit-exact IEEE 754 binary32/binary64 core (trusted)

This file is the architecture-independent part of Janus's floating-point model: decoding an
encoding into its exact value, exact arithmetic on those values, and rounding an exact value
to a format. It is written from IEEE 754-2019 §§3–4 and §7 and shaped after Arm's ASL
`FPUnpackBase`/`FPRoundBase` (`shared/functions/float`), so that the per-ISA wrappers
(`Janus.Arm64.Float`, `Janus.Amd64.Float`) can transcribe the architecture pseudocode on top
of it. Everything that differs between architectures (NaN selection and default NaN,
flush-to-zero, the order of exception signalling, conversion of out-of-range values to
integers) is left to the wrappers; the core only computes the facts they need.

Only `Nat`/`Int` arithmetic and structural recursion are used (no `Float`, no well-founded
recursion), so the kernel evaluates everything on literals (`decide +kernel`; the kernel has
GMP acceleration for `Nat` arithmetic and `Nat.log2`).

## Representation

* A format `Fmt` has `ebits` exponent bits and `fbits` fraction bits; an encoding is the
  natural number `sign * 2^(ebits+fbits) + exp * 2^fbits + frac` below `2^width`.
* A finite non-zero value is `(-1)^sign * m * 2^e` with `m > 0` a natural number and `e` an
  integer (not normalised). Exact sums, products and fused multiply-adds of such values are
  again of this form; quotients and square roots are represented by a "round-to-odd"
  approximation with at least `fbits + 3` significant bits, which rounds to the same result,
  with the same inexactness and tininess, as the exact value in every rounding mode (see
  `divExact`, `sqrtExact`).
-/

namespace Janus.Float

/-! ## Formats -/

/-- An IEEE 754 binary interchange format. -/
structure Fmt where
  /-- Exponent field width `w`. -/
  ebits : Nat
  /-- Trailing significand (fraction) width `t = p - 1`. -/
  fbits : Nat
deriving DecidableEq, Repr, Inhabited

/-- binary32 (`float32`, `S` registers). -/
def binary32 : Fmt := ⟨8, 23⟩
/-- binary64 (`float64`, `D` registers). -/
def binary64 : Fmt := ⟨11, 52⟩

namespace Fmt
variable (f : Fmt)
/-- Total width `1 + w + t`. -/
def width : Nat := 1 + f.ebits + f.fbits
/-- Exponent bias `2^(w-1) - 1`. -/
def bias : Nat := 2 ^ (f.ebits - 1) - 1
/-- The all-ones exponent field (infinities and NaNs). -/
def expMax : Nat := 2 ^ f.ebits - 1
/-- `emin = 1 - bias`: the exponent of the smallest normal number `2^emin`. -/
def emin : Int := 1 - (f.bias : Int)
/-- The sign bit `2^(width-1)`. -/
def signBit : Nat := 2 ^ (f.ebits + f.fbits)
/-- The quiet bit (most significant fraction bit) `2^(t-1)`. -/
def quietBit : Nat := 2 ^ (f.fbits - 1)
end Fmt

/-- The encoding `sign : exp : frac`. -/
def pack (f : Fmt) (sign : Bool) (exp frac : Nat) : Nat :=
  (if sign then f.signBit else 0) + exp * 2 ^ f.fbits + frac

/-- `FPZero(sign)`. -/
def zero (f : Fmt) (sign : Bool) : Nat := pack f sign 0 0
/-- `FPInfinity(sign)`. -/
def inf (f : Fmt) (sign : Bool) : Nat := pack f sign f.expMax 0
/-- `FPMaxNormal(sign)`. -/
def maxNormal (f : Fmt) (sign : Bool) : Nat := pack f sign (f.expMax - 1) (2 ^ f.fbits - 1)

/-- The fields of an encoding `x < 2^width`. -/
def signOf (f : Fmt) (x : Nat) : Bool := x / f.signBit % 2 = 1
def expOf (f : Fmt) (x : Nat) : Nat := x / 2 ^ f.fbits % 2 ^ f.ebits
def fracOf (f : Fmt) (x : Nat) : Nat := x % 2 ^ f.fbits

/-- The encoding with the sign bit cleared / flipped (bit operations on the encoding). -/
def clearSign (f : Fmt) (x : Nat) : Nat := x % f.signBit
def flipSign (f : Fmt) (x : Nat) : Nat := if signOf f x then x % f.signBit else x % f.signBit + f.signBit

/-! ## Classification and exact values -/

/-- The class of an encoding (`FPType` in the ASL, with normal and subnormal numbers apart). -/
inductive Kind where
  | zero | subnormal | normal | inf | qnan | snan
deriving DecidableEq, Repr, Inhabited

def classify (f : Fmt) (x : Nat) : Kind :=
  let e := expOf f x
  let m := fracOf f x
  if e = 0 then (if m = 0 then .zero else .subnormal)
  else if e = f.expMax then
    (if m = 0 then .inf else if m / f.quietBit % 2 = 1 then .qnan else .snan)
  else .normal

def isNaN (f : Fmt) (x : Nat) : Bool :=
  match classify f x with
  | .qnan | .snan => true
  | _ => false

def isSNaN (f : Fmt) (x : Nat) : Bool := classify f x == .snan

/-- The integer significand of a finite encoding: `2^t + frac` for a normal number, `frac`
for a subnormal one (and 0 for a zero). -/
def mantOf (f : Fmt) (x : Nat) : Nat :=
  if expOf f x = 0 then fracOf f x else 2 ^ f.fbits + fracOf f x

/-- The exponent of the unit in the last place of a finite encoding: the value is
`mantOf * 2^ulpExpOf`. -/
def ulpExpOf (f : Fmt) (x : Nat) : Int :=
  (if expOf f x = 0 then f.emin else (expOf f x : Int) - f.bias) - f.fbits

/-- An exact real value that an operation can produce or consume: an infinity, or the
dyadic rational `n * 2^e` (`n` may be zero; its sign is carried separately where a zero's
sign matters). -/
inductive Val where
  | num (n : Int) (e : Int)
  | inf (neg : Bool)
deriving DecidableEq, Repr, Inhabited

/-- The magnitude and exponent of a finite non-zero `Val`. -/
def Val.mag : Val → Nat × Int
  | .num n e => (n.natAbs, e)
  | .inf _ => (1, 0)

def Val.n : Val → Int
  | .num n _ => n
  | .inf _ => 0

def Val.e : Val → Int
  | .num _ e => e
  | .inf _ => 0

/-- The value of a non-NaN encoding (`FPUnpack`'s `value`; a NaN gives `0`, as in the ASL). -/
def valueOf (f : Fmt) (x : Nat) : Val :=
  match classify f x with
  | .inf => .inf (signOf f x)
  | .zero | .qnan | .snan => .num 0 0
  | _ => .num (if signOf f x then -(mantOf f x : Int) else mantOf f x) (ulpExpOf f x)

/-- `n * 2^e` and `n' * 2^e'` brought to the common exponent `min e e'`. -/
def align (n e n' e' : Int) : Int × Int :=
  let m := min e e'
  (n * 2 ^ (e - m).toNat, n' * 2 ^ (e' - m).toNat)

/-- `a < b` on values (`-∞ < every number < +∞`). -/
def Val.lt : Val → Val → Bool
  | .inf true, .inf true => false
  | .inf true, _ => true
  | _, .inf true => false
  | .inf false, _ => false
  | _, .inf false => true
  | .num n e, .num n' e' => let (a, b) := align n e n' e'; decide (a < b)

/-- `a = b` on values. -/
def Val.eq : Val → Val → Bool
  | .inf s, .inf s' => s == s'
  | .num n e, .num n' e' => let (a, b) := align n e n' e'; a == b
  | _, _ => false

/-! ## Rounding -/

/-- Rounding direction (ASL `FPRounding`; `rna` is round-to-nearest, ties away from zero, used
by `FRINTA`/`FCVTA*` only). -/
inductive RM where
  /-- roundTiesToEven -/
  | rne
  /-- roundTowardPositive -/
  | rpi
  /-- roundTowardNegative -/
  | rmi
  /-- roundTowardZero -/
  | rz
  /-- roundTiesToAway -/
  | rna
deriving DecidableEq, Repr, Inhabited

/-- Whether to add one unit when the magnitude `k * 2^s + rem` (with `0 ≤ rem < 2^s`) of a
value of sign `neg` is rounded down to `k` units: the rounding decision of `FPRoundBase`. -/
def roundUp (rm : RM) (neg : Bool) (k rem s : Nat) : Bool :=
  if rem = 0 then false else
  match rm with
  | .rne => 2 * rem > 2 ^ s || (2 * rem = 2 ^ s && k % 2 = 1)
  | .rna => 2 * rem ≥ 2 ^ s
  | .rpi => !neg
  | .rmi => neg
  | .rz => false

/-- `m * 2^e` rounded to a multiple of `2^q`, in units of `2^q`, by `rm`: the rounded unit
count and whether the result is inexact. -/
def roundAt (rm : RM) (neg : Bool) (m : Nat) (e q : Int) : Nat × Bool :=
  if q ≤ e then (m * 2 ^ (e - q).toNat, false) else
  let s := (q - e).toNat
  let k := m / 2 ^ s
  let rem := m % 2 ^ s
  (if roundUp rm neg k rem s then k + 1 else k, rem ≠ 0)

/-- Whether an overflow of a value of sign `neg` delivers an infinity (`overflow_to_inf`). -/
def overflowToInf (rm : RM) (neg : Bool) : Bool :=
  match rm with
  | .rne | .rna => true
  | .rpi => !neg
  | .rmi => neg
  | .rz => false

/-- What rounding the exact non-zero value `(-1)^neg * m * 2^e` (`m > 0`) to a format
produces, with every fact an architecture's exception rules may depend on. -/
structure Rounded where
  /-- The encoding of the correctly rounded result, an infinity or the largest finite number
  on overflow (by the rounding direction). -/
  bits : Nat
  /-- The rounded result differs from the exact value (also on overflow). -/
  inexact : Bool
  /-- The rounded result's exponent exceeds the format's range (`biased_exp >= 2^E - 1`). -/
  overflow : Bool
  /-- Tiny before rounding: `|v| < 2^emin` (`biased_exp == 0` in `FPRoundBase`). -/
  tinyBefore : Bool
  /-- Tiny after rounding: `v` rounded to `p` significant bits with an unbounded exponent range
  is below `2^emin` in magnitude (`biased_exp_unconstrained < 1`). -/
  tinyAfter : Bool
  /-- The rounding error of the constrained (subnormal-aware) rounding is non-zero (`error !=
  0.0` before the overflow case sets it). -/
  roundErr : Bool
deriving DecidableEq, Repr, Inhabited

/-- The constrained rounding of `(-1)^neg * m * 2^e` (`m > 0`): the result is `k * 2^q` with
`q = max(E, emin) - t` (subnormals share `emin`'s unit) and `k` the rounded unit count, after a
carry out of the significand has moved it to the next binade (`k = 2^(t+1)` becomes
`2^t * 2^(q+1)`). -/
def roundUnits (f : Fmt) (rm : RM) (neg : Bool) (m : Nat) (e : Int) : Nat × Int :=
  let q : Int := max ((Nat.log2 m : Int) + e) f.emin - f.fbits
  let k := (roundAt rm neg m e q).1
  if k = 2 ^ (f.fbits + 1) then (k / 2, q + 1) else (k, q)

/-- The biased exponent field of `k * 2^q` (`k < 2^(t+1)`): 0 for a subnormal (`k < 2^t`). -/
def biasedExp (f : Fmt) (k : Nat) (q : Int) : Int :=
  if k < 2 ^ f.fbits then 0 else q + f.fbits + f.bias

/-- Round `(-1)^neg * m * 2^e` (`m > 0`) to `f` by `rm` (IEEE 754 §4.3; `FPRoundBase` without
its flush-to-zero and exception handling, which the wrappers add). -/
def round (f : Fmt) (rm : RM) (neg : Bool) (m : Nat) (e : Int) : Rounded :=
  let E : Int := (Nat.log2 m : Int) + e
  let tinyBefore := decide (E < f.emin)
  let err := (roundAt rm neg m e (max E f.emin - f.fbits)).2
  let u := roundUnits f rm neg m e
  let biased := biasedExp f u.1 u.2
  -- unconstrained: p = t + 1 significant bits, unbounded exponent
  let ku := (roundAt rm neg m e (E - f.fbits)).1
  let Eu : Int := if ku = 2 ^ (f.fbits + 1) then E + 1 else E
  let tinyAfter := decide (Eu < f.emin)
  if biased ≥ (f.expMax : Int) then
    { bits := if overflowToInf rm neg then inf f neg else maxNormal f neg,
      inexact := true, overflow := true, tinyBefore, tinyAfter, roundErr := err }
  else
    { bits := pack f neg biased.toNat (u.1 % 2 ^ f.fbits), inexact := err, overflow := false,
      tinyBefore, tinyAfter, roundErr := err }

/-! ## Exact arithmetic

Results are `none` for an exact zero (whose sign the caller determines) and otherwise
`some (neg, m, e)` with `m > 0`. -/

/-- The sign and magnitude of the signed significand `n * 2^e`. -/
def ofInt (n e : Int) : Option (Bool × Nat × Int) :=
  if n = 0 then none else some (decide (n < 0), n.natAbs, e)

/-- `a + b` exactly, for the finite values `n * 2^e`, `n' * 2^e'`. -/
def addExact (n e n' e' : Int) : Option (Bool × Nat × Int) :=
  let (a, b) := align n e n' e'
  ofInt (a + b) (min e e')

/-- `a * b` exactly. -/
def mulExact (n e n' e' : Int) : Option (Bool × Nat × Int) := ofInt (n * n') (e + e')

/-- `a + b * c` exactly (the fused multiply-add). -/
def fmaExact (na ea n1 e1 n2 e2 : Int) : Option (Bool × Nat × Int) :=
  addExact na ea (n1 * n2) (e1 + e2)

/-- The quotient `|n * 2^e| / |n' * 2^e'|` (`n, n' ≠ 0`) as `(m, e)` in round-to-odd form with
at least `fbits + 4` significant bits (see the module documentation). -/
def divOdd (fbits : Nat) (m : Nat) (e : Int) (m' : Nat) (e' : Int) : Nat × Int :=
  let k := fbits + 5 + Nat.log2 m'
  let num := m * 2 ^ k
  let q := num / m'
  ((if num % m' = 0 then q else q ||| 1), e - e' - k)

/-- Integer square root `⌊√n⌋`, one result bit per step from bit `k - 1` down. -/
def isqrtGo (n : Nat) : Nat → Nat → Nat
  | 0, r => r
  | k + 1, r =>
    let c := r + 2 ^ k
    isqrtGo n k (if c * c ≤ n then c else r)

def isqrt (n : Nat) : Nat := isqrtGo n (Nat.log2 n / 2 + 1) 0

/-- `√(m * 2^e)` (`m > 0`) as `(m', e')` in round-to-odd form with at least `fbits + 4`
significant bits. -/
def sqrtOdd (fbits : Nat) (m : Nat) (e : Int) : Nat × Int :=
  let odd := e % 2   -- 0 or 1
  let m1 := m * 2 ^ odd.toNat
  let e1 := e - odd  -- even
  let k := fbits + 4
  let M := m1 * 2 ^ (2 * k)
  let r := isqrt M
  ((if r * r = M then r else r ||| 1), e1 / 2 - k)

/-- The magnitude `m * 2^e` of a signed value rounded to an integer by `rm`, as a signed
integer, with the sign `neg` of the value: `(result, inexact)` (`FPRoundInt`/`FPToFixed`:
`RoundDown(value)` plus the `round_up` correction). -/
def roundToInt (rm : RM) (neg : Bool) (m : Nat) (e : Int) : Int × Bool :=
  if 0 ≤ e then ((if neg then -1 else 1) * ((m * 2 ^ e.toNat : Nat) : Int), false) else
  let s := (-e).toNat
  let k := m / 2 ^ s
  let rem := m % 2 ^ s
  -- `roundUp` decides on the magnitude; for a negative value "up" in magnitude is toward -∞
  let r := if roundUp rm neg k rem s then k + 1 else k
  ((if neg then -1 else 1) * (r : Int), rem ≠ 0)

end Janus.Float
