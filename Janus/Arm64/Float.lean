import Janus.Float.Core
import Janus.Arm64.State

/-!
# AArch64 floating-point pseudocode (trusted)

A transcription of the Arm ASL library functions for scalar binary32/binary64 arithmetic
(`shared/functions/float/*` in the Armv9.4-A release, as translated in sail-arm's
`v8_base.sail`) on top of the IEEE core `Janus.Float`: `FPUnpackBase`, `FPRoundBase`,
`FPProcessNaN(s)(3)`, `FPProcessDenorm(s)`, `FPAdd`, `FPSub`, `FPMul`, `FPDiv`, `FPMulAdd`,
`FPMax`/`FPMin`/`FPMaxNum`/`FPMinNum`, `FPCompare`, `FPSqrt`, `FPRoundInt`, `FPConvert`
(with `FPConvertNaN`), `FPToFixed`, `FixedToFP`, `FPAbs`, `FPNeg`, `VFPExpandImm`. Each
function follows the ASL statement by statement; `real` values are `Janus.Float.Val`
(exact dyadic rationals), quotients and square roots are rounded through the round-to-odd
approximations of the core.

The model is of a CPU that implements FEAT_FP and FEAT_AFP (`HaveAltFP()`): `FPCR.FIZ`,
`FPCR.AH` and `FPCR.NEP` are honoured. With those three bits clear, every function reduces to
the Armv8.0 behaviour (`altfp` is false, the default NaN is positive, nothing merges), so the
model is also exact for CPUs without FEAT_AFP as long as those bits read as zero. Half
precision (FEAT_FP16, `FZ16`, `AHP`) and BFloat16 are not modelled; the decoder rejects them.

Exceptions. `FPProcessException(e, fpcr)` sets `FPSR` bit `e` unless the trap enable bit
`FPCR<e+8>` is set; then the instruction traps (on a CPU that supports trapping, which is
IMPLEMENTATION DEFINED; on others the enable bits are RAZ/WI and the case cannot occur). The
functions here return the exceptions they raise as an `Exc`: `proc`, the bits raised through
`FPProcessException` (they trap when enabled), and `direct`, the bits `FPRoundBase` writes
straight to `FPSR.UFC` when it flushes to zero (never trapped). The executor
(`Janus.Arm64.Exec`) faults with `Fault.fpTrapped` when `proc` meets an enable bit and
otherwise ORs both into `FPSR`.

`N` is the format: `binary32` (`S`) or `binary64` (`D`); encodings are natural numbers below
`2^N`, and `FPCR` is the 32-bit register value as a natural number.
-/

namespace Janus.Arm64.FP

open Janus.Float

/-! ## FPCR fields -/

/-- `fpcr<i>`. -/
def fpcrBit (fpcr i : Nat) : Bool := fpcr / 2 ^ i % 2 = 1
/-- `FPCR.FIZ` (FEAT_AFP): flush subnormal inputs to zero without `IDC`. -/
def fiz (fpcr : Nat) : Bool := fpcrBit fpcr 0
/-- `FPCR.AH` (FEAT_AFP): alternate handling (`altfp`). -/
def ah (fpcr : Nat) : Bool := fpcrBit fpcr 1
/-- `FPCR.NEP` (FEAT_AFP): scalar results merge into the upper part of the vector register. -/
def nep (fpcr : Nat) : Bool := fpcrBit fpcr 2
/-- `FPCR.FZ`. -/
def fz (fpcr : Nat) : Bool := fpcrBit fpcr 24
/-- `FPCR.DN`. -/
def dn (fpcr : Nat) : Bool := fpcrBit fpcr 25
/-- `FPCR.UFE`: the underflow trap enable (`trapped_UF` in `FPRoundBase`). -/
def ufe (fpcr : Nat) : Bool := fpcrBit fpcr 11
/-- The trap enable bits `IDE:0:0:IXE:UFE:OFE:DZE:IOE` (`FPCR<15:8>`), aligned with the
`FPSR` cumulative bits. -/
def trapEnables (fpcr : Nat) : Nat := fpcr / 2 ^ 8 % 2 ^ 8 &&& 0x9F

/-- `FPDecodeRounding(rmode)`. -/
def decodeRounding (rmode : Nat) : RM :=
  if rmode = 0 then .rne else if rmode = 1 then .rpi else if rmode = 2 then .rmi else .rz

/-- `FPRoundingMode(fpcr)`: `FPCR.RMode`, bits 23:22. -/
def roundingMode (fpcr : Nat) : RM := decodeRounding (fpcr / 2 ^ 22 % 4)

/-- `IsMerging(fpcr)`: scalar results keep the upper bits of a source register. -/
def isMerging (fpcr : Nat) : Bool := nep fpcr

/-! ## Exceptions -/

/-- The cumulative bits of `FPSR` (bit positions of the ASL `FPExc` values). -/
def IOC : Nat := 1
def DZC : Nat := 2
def OFC : Nat := 4
def UFC : Nat := 8
def IXC : Nat := 16
def IDC : Nat := 128

/-- The exceptions an operation raised: `proc` through `FPProcessException` (trap when
enabled), `direct` written to `FPSR` without a trap check. -/
structure Exc where
  proc : Nat := 0
  direct : Nat := 0
deriving DecidableEq, Repr, Inhabited

instance : Append Exc := ⟨fun a b => ⟨a.proc ||| b.proc, a.direct ||| b.direct⟩⟩

/-- `FPProcessException(e, fpcr)` for the bit `e`. -/
def raise (e : Nat) : Exc := ⟨e, 0⟩

/-! ## Unpacking -/

/-- `FPType`. -/
inductive FPType where
  | zero | denormal | nonzero | infinity | qnan | snan
deriving DecidableEq, Repr, Inhabited

def FPType.isNaN : FPType → Bool
  | .qnan | .snan => true
  | _ => false

/-- `FPUnpackBase(fpval, fpcr, fpexc)` (with `fpcr.AHP` irrelevant: no half precision):
`(fptype, sign, value)` and the input-denormal exception. A subnormal input is flushed to zero
when `FZ = 1` and `AH = 0` (raising `IDC`) or when `FIZ = 1` (without `IDC`). -/
def unpack (f : Fmt) (fpcr : Nat) (fpexc : Bool) (x : Nat) : (FPType × Bool × Val) × Exc :=
  let sign := signOf f x
  let fizF := fiz fpcr
  let fzF := fz fpcr && !ah fpcr
  match classify f x with
  | .zero => ((.zero, sign, .num 0 0), {})
  | .subnormal =>
    if fzF || fizF then ((.zero, sign, .num 0 0), if fzF && fpexc then raise IDC else {})
    else ((.denormal, sign, valueOf f x), {})
  | .normal => ((.nonzero, sign, valueOf f x), {})
  | .inf => ((.infinity, sign, .inf sign), {})
  | .qnan => ((.qnan, sign, .num 0 0), {})
  | .snan => ((.snan, sign, .num 0 0), {})

/-! ## Constants -/

/-- `FPDefaultNaN(fpcr, N)`: sign `FPCR.AH` (FEAT_AFP), exponent all ones, quiet bit only. -/
def defaultNaN (f : Fmt) (fpcr : Nat) : Nat := pack f (ah fpcr) f.expMax f.quietBit

/-- `VFPExpandImm(imm8, N)`: `imm8<7> : NOT(imm8<6>) : Replicate(imm8<6>, E-3) : imm8<5:4> :
imm8<3:0> : Zeros(F-4)`. -/
def vfpExpandImm (f : Fmt) (imm8 : Nat) : Nat :=
  let b6 := imm8 / 64 % 2
  let exp := (1 - b6) * 2 ^ (f.ebits - 1) + b6 * (2 ^ (f.ebits - 3) - 1) * 4 + imm8 / 16 % 4
  pack f (imm8 / 128 % 2 = 1) exp (imm8 % 16 * 2 ^ (f.fbits - 4))

/-! ## NaN and denormal processing -/

/-- `FPProcessNaN(fptype, op, fpcr)`: quiet a signalling NaN (raising `IOC`), then replace it by
the default NaN when `FPCR.DN = 1`. -/
def processNaN (f : Fmt) (fpcr : Nat) (t : FPType) (op : Nat) : Nat × Exc :=
  let (r, e) := if t = .snan then (op ||| f.quietBit, raise IOC) else (op, {})
  (if dn fpcr then defaultNaN f fpcr else r, e)

/-- `FPProcessNaNs(type1, type2, op1, op2, fpcr)`: `some` result when an operand is a NaN. -/
def processNaNs (f : Fmt) (fpcr : Nat) (t1 t2 : FPType) (op1 op2 : Nat) : Option (Nat × Exc) :=
  let altfp := ah fpcr
  let tnan : FPType := if t1 = .snan || t2 = .snan then .snan else .qnan
  if altfp && t1.isNaN && t2.isNaN then some (processNaN f fpcr tnan op1)
  else if t1 = .snan then some (processNaN f fpcr t1 op1)
  else if t2 = .snan then some (processNaN f fpcr t2 op2)
  else if t1 = .qnan then some (processNaN f fpcr t1 op1)
  else if t2 = .qnan then some (processNaN f fpcr t2 op2)
  else none

/-- `FPProcessNaNs3(type1, type2, type3, op1, op2, op3, fpcr)`. -/
def processNaNs3 (f : Fmt) (fpcr : Nat) (t1 t2 t3 : FPType) (op1 op2 op3 : Nat) :
    Option (Nat × Exc) :=
  let altfp := ah fpcr
  let tnan : FPType := if t1 = .snan || t2 = .snan || t3 = .snan then .snan else .qnan
  if altfp && t1.isNaN && t2.isNaN && t3.isNaN then some (processNaN f fpcr tnan op2)
  else if altfp && t2.isNaN && (t1.isNaN || t3.isNaN) then some (processNaN f fpcr tnan op2)
  else if altfp && t3.isNaN && t1.isNaN then some (processNaN f fpcr tnan op3)
  else if t1 = .snan then some (processNaN f fpcr t1 op1)
  else if t2 = .snan then some (processNaN f fpcr t2 op2)
  else if t3 = .snan then some (processNaN f fpcr t3 op3)
  else if t1 = .qnan then some (processNaN f fpcr t1 op1)
  else if t2 = .qnan then some (processNaN f fpcr t2 op2)
  else if t3 = .qnan then some (processNaN f fpcr t3 op3)
  else none

/-- `FPProcessDenorm(fptype, N, fpcr)`: with `AH = 1`, a subnormal input raises `IDC`. -/
def processDenorm (fpcr : Nat) (t : FPType) : Exc :=
  if ah fpcr && t = .denormal then raise IDC else {}

/-- `FPProcessDenorms(type1, type2, N, fpcr)`. -/
def processDenorms (fpcr : Nat) (t1 t2 : FPType) : Exc :=
  if ah fpcr && (t1 = .denormal || t2 = .denormal) then raise IDC else {}

/-- `FPProcessDenorms3(type1, type2, type3, N, fpcr)`. -/
def processDenorms3 (fpcr : Nat) (t1 t2 t3 : FPType) : Exc :=
  if ah fpcr && (t1 = .denormal || t2 = .denormal || t3 = .denormal) then raise IDC else {}

/-! ## Rounding -/

/-- `FPRoundBase(op, fpcr, rounding, FALSE, TRUE, N)` for the non-zero value
`(-1)^neg * m * 2^e` (`m > 0`).

* `AH = 0`: flush-to-zero (`FZ = 1`) happens *before* rounding, on the exact value: a result
  below `2^emin` becomes a zero of the same sign and sets `UFC` directly (no `IXC`, no trap).
  Otherwise underflow is signalled when the exact value is below `2^emin` and the rounding is
  inexact, or `FPCR.UFE` is set (`trapped_UF`).
* `AH = 1`: tininess is detected *after* rounding (with an unbounded exponent); a tiny result
  is flushed to zero when `FZ = 1` (setting `UFC` directly and raising `IXC`), and otherwise
  underflow is signalled when inexact or trapped.
* Overflow delivers an infinity or the largest normal by the rounding direction and raises
  `OFC` and `IXC`; any other inexact result raises `IXC`. -/
def fpRound (f : Fmt) (fpcr : Nat) (rm : RM) (neg : Bool) (m : Nat) (e : Int) : Nat × Exc :=
  let altfp := ah fpcr
  let r := round f rm neg m e
  let trappedUF := ufe fpcr
  if !altfp && fz fpcr && r.tinyBefore then (zero f neg, ⟨0, UFC⟩) else
  let uf1 : Exc := if !altfp && r.tinyBefore && (r.roundErr || trappedUF) then raise UFC else {}
  if altfp && r.tinyAfter && fz fpcr then (zero f neg, ⟨IXC, UFC⟩) else
  let uf2 : Exc := if altfp && r.tinyAfter && (r.roundErr || trappedUF) then raise UFC else {}
  let ovf : Exc := if r.overflow then raise OFC else {}
  let ix : Exc := if r.inexact then raise IXC else {}
  (r.bits, uf1 ++ uf2 ++ ovf ++ ix)

/-! ## Arithmetic -/

/-- `FPAdd(op1, op2, fpcr)`. -/
def fpAdd (f : Fmt) (fpcr : Nat) (op1 op2 : Nat) : Nat × Exc :=
  let rounding := roundingMode fpcr
  let ((t1, s1, v1), x1) := unpack f fpcr true op1
  let ((t2, s2, v2), x2) := unpack f fpcr true op2
  let pre := x1 ++ x2
  match processNaNs f fpcr t1 t2 op1 op2 with
  | some (r, e) => (r, pre ++ e)
  | none =>
    let inf1 := t1 = .infinity
    let inf2 := t2 = .infinity
    let zero1 := t1 = .zero
    let zero2 := t2 = .zero
    let (r, e) :=
      if inf1 && inf2 && s1 != s2 then (defaultNaN f fpcr, raise IOC)
      else if (inf1 && !s1) || (inf2 && !s2) then (inf f false, {})
      else if (inf1 && s1) || (inf2 && s2) then (inf f true, {})
      else if zero1 && zero2 && s1 == s2 then (zero f s1, {})
      else match addExact v1.n v1.e v2.n v2.e with
        | none => (zero f (rounding = .rmi), {})
        | some (neg, m, ex) => fpRound f fpcr rounding neg m ex
    (r, pre ++ e ++ processDenorms fpcr t1 t2)

/-- `FPSub(op1, op2, fpcr)`. -/
def fpSub (f : Fmt) (fpcr : Nat) (op1 op2 : Nat) : Nat × Exc :=
  let rounding := roundingMode fpcr
  let ((t1, s1, v1), x1) := unpack f fpcr true op1
  let ((t2, s2, v2), x2) := unpack f fpcr true op2
  let pre := x1 ++ x2
  match processNaNs f fpcr t1 t2 op1 op2 with
  | some (r, e) => (r, pre ++ e)
  | none =>
    let inf1 := t1 = .infinity
    let inf2 := t2 = .infinity
    let zero1 := t1 = .zero
    let zero2 := t2 = .zero
    let (r, e) :=
      if inf1 && inf2 && s1 == s2 then (defaultNaN f fpcr, raise IOC)
      else if (inf1 && !s1) || (inf2 && s2) then (inf f false, {})
      else if (inf1 && s1) || (inf2 && !s2) then (inf f true, {})
      else if zero1 && zero2 && s1 == !s2 then (zero f s1, {})
      else match addExact v1.n v1.e (-v2.n) v2.e with
        | none => (zero f (rounding = .rmi), {})
        | some (neg, m, ex) => fpRound f fpcr rounding neg m ex
    (r, pre ++ e ++ processDenorms fpcr t1 t2)

/-- `FPMul(op1, op2, fpcr)`. -/
def fpMul (f : Fmt) (fpcr : Nat) (op1 op2 : Nat) : Nat × Exc :=
  let ((t1, s1, v1), x1) := unpack f fpcr true op1
  let ((t2, s2, v2), x2) := unpack f fpcr true op2
  let pre := x1 ++ x2
  match processNaNs f fpcr t1 t2 op1 op2 with
  | some (r, e) => (r, pre ++ e)
  | none =>
    let inf1 := t1 = .infinity
    let inf2 := t2 = .infinity
    let zero1 := t1 = .zero
    let zero2 := t2 = .zero
    let (r, e) :=
      if (inf1 && zero2) || (zero1 && inf2) then (defaultNaN f fpcr, raise IOC)
      else if inf1 || inf2 then (inf f (s1 != s2), {})
      else if zero1 || zero2 then (zero f (s1 != s2), {})
      else match mulExact v1.n v1.e v2.n v2.e with
        | none => (zero f (s1 != s2), {})
        | some (neg, m, ex) => fpRound f fpcr (roundingMode fpcr) neg m ex
    (r, pre ++ e ++ processDenorms fpcr t1 t2)

/-- `FPDiv(op1, op2, fpcr)`. -/
def fpDiv (f : Fmt) (fpcr : Nat) (op1 op2 : Nat) : Nat × Exc :=
  let ((t1, s1, v1), x1) := unpack f fpcr true op1
  let ((t2, s2, v2), x2) := unpack f fpcr true op2
  let pre := x1 ++ x2
  match processNaNs f fpcr t1 t2 op1 op2 with
  | some (r, e) => (r, pre ++ e)
  | none =>
    let inf1 := t1 = .infinity
    let inf2 := t2 = .infinity
    let zero1 := t1 = .zero
    let zero2 := t2 = .zero
    let (r, e) :=
      if (inf1 && inf2) || (zero1 && zero2) then (defaultNaN f fpcr, raise IOC)
      else if inf1 || zero2 then (inf f (s1 != s2), if !inf1 then raise DZC else {})
      else if zero1 || inf2 then (zero f (s1 != s2), {})
      else
        let (m1, e1) := v1.mag
        let (m2, e2) := v2.mag
        let (m, ex) := divOdd f.fbits m1 e1 m2 e2
        fpRound f fpcr (roundingMode fpcr) (s1 != s2) m ex
    (r, pre ++ e ++ (if !zero2 then processDenorms fpcr t1 t2 else {}))

/-- `FPMulAdd(addend, op1, op2, fpcr)`: `addend + op1 * op2` with a single rounding. -/
def fpMulAdd (f : Fmt) (fpcr : Nat) (addend op1 op2 : Nat) : Nat × Exc :=
  let ((tA, sA, vA), xA) := unpack f fpcr true addend
  let ((t1, s1, v1), x1) := unpack f fpcr true op1
  let ((t2, s2, v2), x2) := unpack f fpcr true op2
  let pre := xA ++ x1 ++ x2
  let rounding := roundingMode fpcr
  let inf1 := t1 = .infinity
  let zero1 := t1 = .zero
  let inf2 := t2 = .infinity
  let zero2 := t2 = .zero
  let nans := processNaNs3 f fpcr tA t1 t2 addend op1 op2
  -- Arm: a quiet-NaN addend with an invalid product gives the default NaN and IOC
  let qnanInvalid := !ah fpcr && tA = .qnan && ((inf1 && zero2) || (zero1 && inf2))
  match nans with
  | some (r, e) =>
    if qnanInvalid then (defaultNaN f fpcr, pre ++ e ++ raise IOC) else (r, pre ++ e)
  | none =>
    let infA := tA = .infinity
    let zeroA := tA = .zero
    let signP := s1 != s2
    let infP := inf1 || inf2
    let zeroP := zero1 || zero2
    let invalidop := (inf1 && zero2) || (zero1 && inf2) || (infA && infP && sA != signP)
    let (r, e) :=
      if invalidop then (defaultNaN f fpcr, raise IOC)
      else if (infA && !sA) || (infP && !signP) then (inf f false, {})
      else if (infA && sA) || (infP && signP) then (inf f true, {})
      else if zeroA && zeroP && sA == signP then (zero f sA, {})
      else match fmaExact vA.n vA.e v1.n v1.e v2.n v2.e with
        | none => (zero f (rounding = .rmi), {})
        | some (neg, m, ex) => fpRound f fpcr rounding neg m ex
    (r, pre ++ e ++ (if !invalidop then processDenorms3 fpcr tA t1 t2 else {}))

/-- `FPMax(op1, op2, fpcr, altfp)` (`max = true`) / `FPMin` (`max = false`). -/
def fpMaxMin (max : Bool) (f : Fmt) (fpcr : Nat) (altfp : Bool) (op1 op2 : Nat) : Nat × Exc :=
  let ((t1, s1, v1), x1) := unpack f fpcr true op1
  let ((t2, s2, v2), x2) := unpack f fpcr true op2
  let pre := x1 ++ x2
  if altfp && t1 = .zero && t2 = .zero && s1 != s2 then (zero f s2, pre)
  else if altfp && (t1.isNaN || t2.isNaN) then
    (if t2 = .zero then zero f s2 else op2, pre ++ raise IOC)
  else
  match processNaNs f fpcr t1 t2 op1 op2 with
  | some (r, e) => (r, pre ++ e)
  | none =>
    let first := if max then Val.lt v2 v1 else Val.lt v1 v2
    let (t, s, v) := if first then (t1, s1, v1) else (t2, s2, v2)
    let (r, e) :=
      if t = .infinity then (inf f s, {})
      else if t = .zero then (zero f (if max then s1 && s2 else s1 || s2), {})
      else
        -- with `AH = 1` the result is never flushed (`fpcr.FZ = '0'`)
        let fpcr' := if altfp then fpcr &&& (0xFFFFFFFF - 2 ^ 24) else fpcr
        let (m, ex) := v.mag
        fpRound f fpcr' (roundingMode fpcr) s m ex
    (r, pre ++ e ++ processDenorms fpcr t1 t2)

/-- `FPMaxNum(op1, op2, fpcr)` (`max = true`) / `FPMinNum`: a single quiet NaN is treated as
`-∞` (max) / `+∞` (min). -/
def fpMaxMinNum (max : Bool) (f : Fmt) (fpcr : Nat) (op1 op2 : Nat) : Nat × Exc :=
  let ((t1, _, _), x1) := unpack f fpcr true op1
  let ((t2, _, _), x2) := unpack f fpcr true op2
  let both := ah fpcr && t1.isNaN && t2.isNaN
  let (op1, op2) :=
    if both then (op1, op2)
    else if t1 = .qnan && t2 != .qnan then (inf f max, op2)
    else if t1 != .qnan && t2 = .qnan then (op1, inf f max)
    else (op1, op2)
  let (r, e) := fpMaxMin max f fpcr false op1 op2
  (r, x1 ++ x2 ++ e)

/-- `FPCompare(op1, op2, signal_nans, fpcr)`: the `NZCV` result (`N = 8, Z = 4, C = 2, V = 1`). -/
def fpCompare (f : Fmt) (fpcr : Nat) (signalNaNs : Bool) (op1 op2 : Nat) : Nat × Exc :=
  let ((t1, _, v1), x1) := unpack f fpcr true op1
  let ((t2, _, v2), x2) := unpack f fpcr true op2
  let pre := x1 ++ x2
  if t1.isNaN || t2.isNaN then
    (0b0011, pre ++ (if t1 = .snan || t2 = .snan || signalNaNs then raise IOC else {}))
  else
    (if Val.eq v1 v2 then 0b0110 else if Val.lt v1 v2 then 0b1000 else 0b0010,
     pre ++ processDenorms fpcr t1 t2)

/-- `FPSqrt(op, fpcr)`. -/
def fpSqrt (f : Fmt) (fpcr : Nat) (op : Nat) : Nat × Exc :=
  let ((t, s, v), x) := unpack f fpcr true op
  let (r, e) :=
    if t.isNaN then processNaN f fpcr t op
    else if t = .zero then (zero f s, {})
    else if t = .infinity && !s then (inf f s, {})
    else if s then (defaultNaN f fpcr, raise IOC)
    else
      let (m, ex) := v.mag
      let (m', e') := sqrtOdd f.fbits m ex
      let (r, e) := fpRound f fpcr (roundingMode fpcr) false m' e'
      (r, e ++ processDenorm fpcr t)
  (r, x ++ e)

/-- `FPRoundInt(op, fpcr, rounding, exact)` (`FRINT*`). -/
def fpRoundInt (f : Fmt) (fpcr : Nat) (rounding : RM) (exact : Bool) (op : Nat) : Nat × Exc :=
  let ((t, s, v), x) := unpack f fpcr (!ah fpcr) op
  let (r, e) :=
    if t.isNaN then processNaN f fpcr t op
    else if t = .infinity then (inf f s, {})
    else if t = .zero then (zero f s, {})
    else
      let (m, ex) := v.mag
      let (i, inexact) := roundToInt rounding s m ex
      let (r, e) := if i = 0 then (zero f s, {}) else fpRound f fpcr .rz s i.natAbs 0
      (r, e ++ (if inexact && exact then raise IXC else {}))
  (r, x ++ e)

/-- `FPConvertNaN(op, M)` from format `f` to format `g` (`S`↔`D`): keep the sign, quiet the
NaN, and move the payload (the fraction below the quiet bit) left-aligned. -/
def convertNaN (f g : Fmt) (op : Nat) : Nat :=
  -- 51-bit payload `frac`, left-aligned as in the ASL
  let frac51 := (op % f.quietBit) * 2 ^ 51 / f.quietBit
  pack g (signOf f op) g.expMax (g.quietBit + frac51 * g.quietBit / 2 ^ 51)

/-- `FPConvert(op, fpcr, rounding, M)` from format `f` to format `g` (`FCVT` between `S` and
`D`; half precision is not modelled, so `alt_hp` is false). -/
def fpConvert (f g : Fmt) (fpcr : Nat) (rounding : RM) (op : Nat) : Nat × Exc :=
  let ((t, s, v), x) := unpack f fpcr true op
  let (r, e) :=
    if t.isNaN then
      (if dn fpcr then defaultNaN g fpcr else convertNaN f g op,
       if t = .snan then raise IOC else {})
    else if t = .infinity then (inf g s, {})
    else if t = .zero then (zero g s, {})
    else
      let (m, ex) := v.mag
      let (r, e) := fpRound g fpcr rounding s m ex
      (r, e ++ processDenorm fpcr t)
  (r, x ++ e)

/-- `SatQ(i, M, unsigned)`: the saturated `M`-bit result (as an `M`-bit pattern) and whether
it saturated. -/
def satQ (M : Nat) (unsigned : Bool) (i : Int) : Nat × Bool :=
  if unsigned then
    if i < 0 then (0, true)
    else if i ≥ 2 ^ M then (2 ^ M - 1, true)
    else (i.toNat, false)
  else
    if i < -(2 ^ (M - 1) : Int) then (2 ^ (M - 1), true)
    else if i ≥ 2 ^ (M - 1) then (2 ^ (M - 1) - 1, true)
    else ((i % (2 ^ M : Int)).toNat, false)

/-- `FPToFixed(op, 0, unsigned, fpcr, rounding, M)` (`FCVT{N,P,M,Z,A}{S,U}` to an `M`-bit
general register): round to an integer, saturate, `IOC` for a NaN or saturation, `IXC`
otherwise when inexact. A NaN converts to 0. -/
def fpToFixed (f : Fmt) (fpcr : Nat) (unsigned : Bool) (rounding : RM) (M : Nat) (op : Nat) :
    Nat × Exc :=
  let ((t, s, v), x) := unpack f fpcr (!ah fpcr) op
  let nanExc : Exc := if t.isNaN then raise IOC else {}
  match v with
  | .inf neg =>
    -- `RoundDown(2.0^1000000)` saturates
    let (r, _) := satQ M unsigned (if neg then -(2 ^ (M + 1) : Int) else 2 ^ (M + 1))
    (r, x ++ nanExc ++ raise IOC)
  | .num n ex =>
    let (i, inexact) := if n = 0 then ((0 : Int), false) else roundToInt rounding s n.natAbs ex
    let (r, ovf) := satQ M unsigned i
    (r, x ++ nanExc ++ (if ovf then raise IOC else if inexact then raise IXC else {}))

/-- `FixedToFP(op, 0, unsigned, fpcr, rounding, N)` (`SCVTF`/`UCVTF` from an `M`-bit general
register value `op < 2^M`). -/
def fixedToFP (f : Fmt) (fpcr : Nat) (unsigned : Bool) (rounding : RM) (M : Nat) (op : Nat) :
    Nat × Exc :=
  let i : Int := if unsigned || op < 2 ^ (M - 1) then op else (op : Int) - 2 ^ M
  if i = 0 then (zero f false, {}) else fpRound f fpcr rounding (decide (i < 0)) i.natAbs 0

/-- `FPAbs(op)`: clear the sign bit (with `AH = 1`, a NaN is returned unchanged). -/
def fpAbs (f : Fmt) (fpcr : Nat) (op : Nat) : Nat :=
  if ah fpcr && isNaN f op then op else clearSign f op

/-- `FPNeg(op)`: flip the sign bit (with `AH = 1`, a NaN is returned unchanged). -/
def fpNeg (f : Fmt) (fpcr : Nat) (op : Nat) : Nat :=
  if ah fpcr && isNaN f op then op else flipSign f op

end Janus.Arm64.FP
