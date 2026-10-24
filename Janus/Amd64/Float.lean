import Janus.Float.Core

/-!
# x86-64 SSE scalar floating point (trusted)

The SSE/SSE2/SSE4.1 scalar floating-point operations on top of the IEEE core `Janus.Float`,
written from the Intel SDM (Vol. 1 §4.8.3.5–§4.9 and §11.5, and the Vol. 2 `Operation` and
"SIMD Floating-Point Exceptions" sections of each instruction). What is specific to x86:

* **NaNs.** An operation with a NaN operand returns the *first* source operand if it is a NaN,
  else the second one, quieted (quiet bit set; the payload is kept). Any signalling NaN raises
  `IE`. An invalid operation without a NaN operand returns the *QNaN floating-point
  indefinite*, sign 1 (`0xFFF8000000000000`, `0xFFC00000`). `MINSD`/`MAXSD` return the second
  operand unchanged (even a signalling NaN) when either operand is a NaN, and raise `IE` for any
  NaN. Conversions to integers of a NaN or an out-of-range value return the *integer
  indefinite* `2^(w-1)` and raise `IE`.
* **Exception precedence** (§4.9.2): a signalling NaN (`IE`) or a quiet NaN operand, then the
  other invalid operations and division by zero (`ZE`), then a denormal operand (`DE`), then
  overflow/underflow with inexact, then inexact. A NaN, invalid or divide-by-zero case produces
  its result without computing, so it raises nothing below it.
* **`MXCSR`.** `RC` (bits 14:13: 00 nearest, 01 down, 10 up, 11 toward zero) is the rounding
  direction; `DAZ` (bit 6) reads subnormal operands as zeros of the same sign, without `DE`;
  `FTZ` (bit 15) returns a zero of the result's sign, raising `UE` and `PE`, for a tiny result
  when underflow is masked. Tininess is detected **after** rounding. The flags are bits 5:0
  (`IE DE ZE OE UE PE`), the masks bits 12:7.
* **Unmasked exceptions** trap (`#XM`, `SIGFPE` on Linux) before anything is written. The
  result of an operation is therefore an `XR`: the result and the flags of the masked
  response, and `traps`, the exceptions that make it trap when unmasked (the executor faults
  when `traps AND NOT masks ≠ 0`). `traps` is `flags`, plus `UE` for a tiny result: an
  unmasked underflow traps on every tiny result (exact or not), while a masked one is flagged
  only for a tiny *inexact* result.

`f` is the format (`binary32` for the `SS` forms, `binary64` for `SD`); `c` is the `RC`/`DAZ`/`FTZ` part of
`MXCSR` (`ctl`). Operand order follows the SDM: `a` is the first source (the destination
register), `b` the second.
-/

namespace Janus.Amd64.FP

open Janus.Float

/-! ## MXCSR -/

def IE : Nat := 0x01
def DE : Nat := 0x02
def ZE : Nat := 0x04
def OE : Nat := 0x08
def UE : Nat := 0x10
def PE : Nat := 0x20

def mxBit (mx i : Nat) : Bool := mx / 2 ^ i % 2 = 1
/-- `MXCSR.DAZ`. -/
def daz (mx : Nat) : Bool := mxBit mx 6
/-- `MXCSR.FTZ`. -/
def ftz (mx : Nat) : Bool := mxBit mx 15
/-- The unmasked exceptions (`NOT MXCSR<12:7>`, aligned with the flags). -/
def unmasked (mx : Nat) : Nat := 0x3F - mx / 2 ^ 7 % 2 ^ 6

/-- The rounding direction of a 2-bit `RC` (or `ROUNDSD` `imm8<1:0>`) field. -/
def decodeRC (rc : Nat) : RM :=
  if rc = 0 then .rne else if rc = 1 then .rmi else if rc = 2 then .rpi else .rz

/-- `MXCSR.RC`. -/
def rounding (mx : Nat) : RM := decodeRC (mx / 2 ^ 13 % 4)

/-- The outcome of an SSE floating-point operation: the result and the flags raised (masked
response), and the exceptions that trap (`#XM`) when unmasked. -/
structure XR where
  res : Nat
  flags : Nat
  traps : Nat
deriving DecidableEq, Repr, Inhabited

/-- The result `r` with the masked-response flags `fl`, which are also the trapping ones. -/
def check (r fl : Nat) : XR := ⟨r, fl, fl⟩

/-- Whether `o` traps under `MXCSR` `mx`. -/
def XR.trap (o : XR) (mx : Nat) : Bool := o.traps &&& unmasked mx ≠ 0

/-- The control bits of `MXCSR` the operations read: `RC`, `DAZ`, `FTZ` (the masks only decide
whether an operation traps, `XR.trap`). -/
structure Ctl where
  rc : RM
  daz : Bool
  ftz : Bool
deriving DecidableEq, Repr, Inhabited

/-- The controls of `MXCSR` `mx`. -/
def ctl (mx : Nat) : Ctl := ⟨rounding mx, daz mx, ftz mx⟩

/-! ## Operands -/

/-- An operand's class after `DAZ`: a subnormal reads as a zero when `MXCSR.DAZ = 1`. -/
def kindOf (f : Fmt) (c : Ctl) (x : Nat) : Kind :=
  match classify f x with
  | .subnormal => if c.daz then .zero else .subnormal
  | k => k

/-- The operand value after `DAZ` (a zero keeps its sign in `signOf`). -/
def valOf (f : Fmt) (c : Ctl) (x : Nat) : Val :=
  if kindOf f c x = .zero then .num 0 0 else valueOf f x

/-- The operand as delivered by `MINSD`/`MAXSD` (a subnormal read as a zero by `DAZ` is that
zero). -/
def dazBits (f : Fmt) (c : Ctl) (x : Nat) : Nat :=
  if kindOf f c x = .zero then zero f (signOf f x) else x

/-- `x` with its quiet bit set. -/
def quiet (f : Fmt) (x : Nat) : Nat := x ||| f.quietBit

/-- The QNaN floating-point indefinite. -/
def indefinite (f : Fmt) : Nat := pack f true f.expMax f.quietBit

/-- The NaN result of an operation with a NaN operand (first source first), and `IE` for a
signalling one. -/
def nanResult (f : Fmt) (a b : Nat) : Nat × Nat :=
  (if isNaN f a then quiet f a else quiet f b, if isSNaN f a || isSNaN f b then IE else 0)

/-! ## Rounding -/

/-- Round the exact non-zero value `(-1)^neg * m * 2^e` to `f` under `MXCSR`, with the flags
`pre` already raised (`DE`): overflow (`OE PE`), underflow (tininess after rounding; masked:
`UE PE` when inexact, flushed to a zero with `UE PE` under `FTZ`; unmasked: a trap for every
tiny result), inexact (`PE`). -/
def roundX (f : Fmt) (c : Ctl) (rm : RM) (pre : Nat) (neg : Bool) (m : Nat) (e : Int) :
    XR :=
  let r := round f rm neg m e
  if r.overflow then check r.bits (pre ||| OE ||| PE)
  else if r.tinyAfter then
    -- masked response, and `UE` traps (when unmasked) for every tiny result
    if c.ftz then ⟨zero f neg, pre ||| UE ||| PE, pre ||| UE ||| PE⟩
    else if r.inexact then ⟨r.bits, pre ||| UE ||| PE, pre ||| UE ||| PE⟩
    else ⟨r.bits, pre, pre ||| UE⟩
  else if r.inexact then check r.bits (pre ||| PE)
  else check r.bits pre

/-! ## Arithmetic -/

/-- The arithmetic operations of `ADDSD SUBSD MULSD DIVSD` (and `SS`). -/
inductive BinOp where
  | add | sub | mul | div
deriving DecidableEq, Repr, Inhabited

/-- `a op b` (`ADDSD`/`SUBSD`/`MULSD`/`DIVSD` and the `SS` forms). -/
def binop (op : BinOp) (f : Fmt) (c : Ctl) (a b : Nat) : XR :=
  let rm := c.rc
  let ka := kindOf f c a
  let kb := kindOf f c b
  let sa := signOf f a
  -- the subtrahend's sign is flipped, so that `a - b = a + (-b)` in the rules below
  let sb := if op = .sub then !signOf f b else signOf f b
  if isNaN f a || isNaN f b then let (r, fl) := nanResult f a b; check r fl else
  let infA := ka = .inf
  let infB := kb = .inf
  let zA := ka = .zero
  let zB := kb = .zero
  let invalid := match op with
    | .add | .sub => infA && infB && sa != sb
    | .mul => (infA && zB) || (zA && infB)
    | .div => (infA && infB) || (zA && zB)
  if invalid then check (indefinite f) IE else
  if op = .div && zB && !infA then check (inf f (sa != sb)) ZE else
  let de := if ka = .subnormal || kb = .subnormal then DE else 0
  let va := valOf f c a
  let vb := valOf f c b
  -- `a + nb * 2^vb.e`: the sum of `ADDSD`, and the difference of `SUBSD` with `nb = -vb.n`
  let sum (nb : Int) : XR :=
    if infA then check (inf f sa) de
    else if infB then check (inf f sb) de
    else if zA && zB then check (zero f (if sa == sb then sa else rm = .rmi)) de
    else
      match addExact va.n va.e nb vb.e with
      | none => check (zero f (rm = .rmi)) de
      | some (neg, m, e) => roundX f c rm de neg m e
  match op with
  | .add => sum vb.n
  | .sub => sum (-vb.n)
  | .mul =>
    if infA || infB then check (inf f (sa != sb)) de
    else if zA || zB then check (zero f (sa != sb)) de
    else match mulExact va.n va.e vb.n vb.e with
      | none => check (zero f (sa != sb)) de
      | some (neg, m, e) => roundX f c rm de neg m e
  | .div =>
    if infA then check (inf f (sa != sb)) de
    else if infB || zA then check (zero f (sa != sb)) de
    else
      let (m1, e1) := va.mag
      let (m2, e2) := vb.mag
      let (m, e) := divOdd f.fbits m1 e1 m2 e2
      roundX f c rm de (sa != sb) m e

/-- `SQRTSD`/`SQRTSS` of `b`. -/
def sqrt (f : Fmt) (c : Ctl) (b : Nat) : XR :=
  let kb := kindOf f c b
  let s := signOf f b
  if isNaN f b then check (quiet f b) (if isSNaN f b then IE else 0)
  else if kb = .zero then check (zero f s) 0
  else if s then check (indefinite f) IE
  else if kb = .inf then check (inf f false) 0
  else
    let de := if kb = .subnormal then DE else 0
    let (m, e) := (valOf f c b).mag
    let (m', e') := sqrtOdd f.fbits m e
    roundX f c (c.rc) de false m' e'

/-- `MINSD`/`MAXSD` (`max`) and the `SS` forms: `IF (a = 0.0 and b = 0.0) THEN b ELSE IF a = NaN
THEN b ELSE IF b = NaN THEN b ELSE IF a < b (a > b) THEN a ELSE b`, `IE` for any NaN operand,
`DE` for a subnormal one. The operand delivered is the one read through `DAZ` (a subnormal
second operand comes back as a zero under `DAZ`, also when the other operand is a NaN). -/
def minmax (max : Bool) (f : Fmt) (c : Ctl) (a b : Nat) : XR :=
  if isNaN f a || isNaN f b then check (dazBits f c b) IE else
  let de := if kindOf f c a = .subnormal || kindOf f c b = .subnormal then DE else 0
  let va := valOf f c a
  let vb := valOf f c b
  let pickA := if max then Val.lt vb va else Val.lt va vb
  check (if kindOf f c a = .zero && kindOf f c b = .zero then dazBits f c b
    else if pickA then dazBits f c a else dazBits f c b) de

/-! ## Comparisons -/

/-- The relation of `a` and `b`: `none` = unordered, else `some (-1 | 0 | 1)`. -/
def relation (f : Fmt) (c : Ctl) (a b : Nat) : Option Int :=
  if isNaN f a || isNaN f b then none else
  let va := valOf f c a
  let vb := valOf f c b
  some (if Val.eq va vb then 0 else if Val.lt va vb then -1 else 1)

/-- `UCOMISD`/`COMISD` (`signal`) and the `SS` forms: `ZF:PF:CF` as the 3-bit result (`OF AF SF`
are cleared by the caller): unordered `111`, greater `000`, less `001`, equal `100`. `IE` for a
signalling NaN (`UCOMIS`) or any NaN (`COMIS`); `DE` for a subnormal operand. -/
def comis (signal : Bool) (f : Fmt) (c : Ctl) (a b : Nat) : XR :=
  match relation f c a b with
  | none => check 0b111 (if isSNaN f a || isSNaN f b || signal then IE else 0)
  | some r =>
    let de := if kindOf f c a = .subnormal || kindOf f c b = .subnormal then DE else 0
    check ((if r = 0 then 4 else 0) + (if r < 0 then 1 else 0)) de

/-- `CMPSD`/`CMPSS` with predicate `p < 8`: `EQ LT LE UNORD NEQ NLT NLE ORD` (`LT LE NLT NLE`
signal on quiet NaNs): all ones (`2^w - 1`) if the predicate holds, else 0. -/
def cmp (f : Fmt) (c : Ctl) (p : Nat) (a b : Nat) : XR :=
  let signal := p % 4 = 1 || p % 4 = 2
  let rel := relation f c a b
  let holds : Bool := match rel with
    | none => p = 3 || p = 4 || p = 5 || p = 6
    | some r =>
      if p = 0 then r = 0 else if p = 1 then r < 0 else if p = 2 then r ≤ 0
      else if p = 3 then false else if p = 4 then r ≠ 0 else if p = 5 then ¬ r < 0
      else if p = 6 then ¬ r ≤ 0 else true
  let ones := 2 ^ f.width - 1
  match rel with
  | none => check (if holds then ones else 0)
      (if isSNaN f a || isSNaN f b || signal then IE else 0)
  | some _ =>
    let de := if kindOf f c a = .subnormal || kindOf f c b = .subnormal then DE else 0
    check (if holds then ones else 0) de

/-! ## Conversions -/

/-- `CVTSI2SD`/`CVTSI2SS` of the `iw`-bit integer `x` (two's complement, `x < 2^iw`). -/
def ofInt (f : Fmt) (c : Ctl) (iw x : Nat) : XR :=
  let i : Int := if x < 2 ^ (iw - 1) then x else (x : Int) - 2 ^ iw
  if i = 0 then check (zero f false) 0 else roundX f c (c.rc) 0 (decide (i < 0)) i.natAbs 0

/-- `CVTTSD2SI` (`rm = .rz`) / `CVTSD2SI` (`rm` from `MXCSR`) and the `SS` forms to an
`iw`-bit integer (as an `iw`-bit pattern). A NaN or a result outside `[-2^(iw-1), 2^(iw-1))`
gives the integer indefinite `2^(iw-1)` with `IE`; an inexact one raises `PE`. Subnormal
inputs follow `DAZ` but never raise `DE`. -/
def toInt (f : Fmt) (c : Ctl) (rm : RM) (iw : Nat) (b : Nat) : XR :=
  let indef := 2 ^ (iw - 1)
  if isNaN f b then check indef IE else
  match valOf f c b with
  | .inf _ => check indef IE
  | .num n e =>
    let (i, inexact) := if n = 0 then ((0 : Int), false) else roundToInt rm (signOf f b) n.natAbs e
    if i < -(2 ^ (iw - 1) : Int) || i ≥ 2 ^ (iw - 1) then check indef IE
    else check ((i % (2 ^ iw : Int)).toNat) (if inexact then PE else 0)

/-- A NaN converted between formats: sign kept, quieted, payload left-aligned (truncated or
zero-extended), as `CVTSD2SS`/`CVTSS2SD` do. -/
def convertNaN (f g : Fmt) (x : Nat) : Nat :=
  let frac51 := (x % f.quietBit) * 2 ^ 51 / f.quietBit
  pack g (signOf f x) g.expMax (g.quietBit + frac51 * g.quietBit / 2 ^ 51)

/-- `CVTSD2SS` (`f = binary64`, `g = binary32`) / `CVTSS2SD`. -/
def convert (f g : Fmt) (c : Ctl) (b : Nat) : XR :=
  let kb := kindOf f c b
  let s := signOf f b
  if isNaN f b then check (convertNaN f g b) (if isSNaN f b then IE else 0)
  else if kb = .inf then check (inf g s) 0
  else if kb = .zero then check (zero g s) 0
  else
    let de := if kb = .subnormal then DE else 0
    let (m, e) := (valOf f c b).mag
    roundX g c (c.rc) de s m e

/-- `ROUNDSD`/`ROUNDSS` of `b` with `imm8`: `imm8<2>` selects `MXCSR.RC`, else `imm8<1:0>`;
`imm8<3>` suppresses `PE`. A signalling NaN is quieted (`IE`), `DE` is never raised (`DAZ`
applies). -/
def roundInt (f : Fmt) (c : Ctl) (imm : Nat) (b : Nat) : XR :=
  let rm := if imm / 4 % 2 = 1 then c.rc else decodeRC (imm % 4)
  let kb := kindOf f c b
  let s := signOf f b
  if isNaN f b then check (quiet f b) (if isSNaN f b then IE else 0)
  else if kb = .inf then check b 0
  else if kb = .zero then check (zero f s) 0
  else
    let (m, e) := (valOf f c b).mag
    let (i, inexact) := roundToInt rm s m e
    let r := if i = 0 then zero f s else (round f .rz s i.natAbs 0).bits
    check r (if inexact && imm / 8 % 2 = 0 then PE else 0)

end Janus.Amd64.FP
