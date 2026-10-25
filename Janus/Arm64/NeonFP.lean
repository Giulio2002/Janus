import Janus.Arm64.Neon

/-!
# Advanced SIMD floating point (trusted)

The Advanced SIMD (vector and scalar) floating-point instructions on single and double
precision, on top of the scalar ASL library `Janus.Arm64.Float` (`FP.fpAdd`, `FP.fpMulAdd`,
`FP.unpack`, `FP.fpRound`, ...), which every lane reuses unchanged. What is added here is
transcribed from the Arm ASL (`shared/functions/float/*`, Armv9.4-A, sail-arm `v8_base.sail`):
`FPCompareEQ`/`GE`/`GT`, `FPMulX`, `FPRecipStepFused`, `FPRSqrtStepFused`, `FPRecipEstimate`,
`FPRSqrtEstimate`, `FPRecpX`, `UnsignedRecipEstimate`, `UnsignedRSqrtEstimate` (with
`RecipEstimate`/`RecipSqrtEstimate`), `FPToFixed`/`FixedToFP` with fraction bits, the
round-to-odd `FPConvert` of `FCVTXN`, and the halving tree of `Reduce` for the across-lanes and
pairwise reductions.

**Per-lane FPCR and exceptions.** Every lane calls the scalar function with the same `FPCR`
(rounding mode, `FZ`, `DN`, `FIZ`/`AH` of FEAT_AFP), exactly as the ASL element loops do
(`FPAdd(element1, element2, FPCR[])`). The lanes' exceptions are ORed (`excLanes`): the
cumulative `FPSR` bits do not depend on the lane order, and the executor faults when any lane
raises an exception whose trap is enabled (`fpCommit`), which is where the ASL would take the
trap. `FPCR.NEP` merging applies only to the scalar forms (`elements == 1 && IsMerging(FPCR)`)
and is done by the executor.

**Not modelled** (rejected by the decoder): half precision (FEAT_FP16, and the `FCVTL`/`FCVTN`
forms to and from half precision), BFloat16, `FRINT32*/64*`, `FMLAL`/`FMLSL` (FEAT_FHM),
`FCMLA`/`FCADD`. The increased-precision estimates of FEAT_RPRES (`FPCR.AH = 1`, single
precision) are IMPLEMENTATION DEFINED; the executor faults there instead of choosing.
-/

namespace Janus.Arm64.NeonFP

open Janus.Float Janus.Arm64 Janus.Arm64.FP

/-- The format of the `sz` bit: single (`0`) or double (`1`) precision. -/
def fmtOf (sz : Nat) : Fmt := if sz = 0 then binary32 else binary64

/-- The element size of `sz`: `32 << UInt(sz)`. -/
def fesize (sz : Nat) : Nat := if sz = 0 then 32 else 64

/-- The exceptions of lanes `0 .. n-1`, ORed. -/
def excLanes (f : Nat → Exc) : Nat → Exc
  | 0 => {}
  | k + 1 => excLanes f k ++ f k

/-- The element loop of a floating-point operation: element `i` of the result is `(f i).1`, and
the exceptions are those of every lane. -/
def fpLanes (esize n : Nat) (f : Nat → Nat × Exc) : Nat × Exc :=
  (ofElems esize n fun i => (f i).1, excLanes (fun i => (f i).2) n)

/-- `Ones(esize)` / `Zeros(esize)` of a comparison. -/
def mask (esize : Nat) (b : Bool) : Nat := if b then 2 ^ esize - 1 else 0

/-! ## Comparisons -/

/-- `FPCompareEQ(op1, op2, fpcr)`: false for a NaN operand (`IOC` only for a signalling NaN). -/
def fpCmpEQ (f : Fmt) (fpcr op1 op2 : Nat) : Bool × Exc :=
  let ((t1, _, v1), x1) := unpack f fpcr true op1
  let ((t2, _, v2), x2) := unpack f fpcr true op2
  if t1.isNaN || t2.isNaN then
    (false, x1 ++ x2 ++ (if t1 = .snan || t2 = .snan then raise IOC else {}))
  else (Val.eq v1 v2, x1 ++ x2 ++ processDenorms fpcr t1 t2)

/-- `FPCompareGE(op1, op2, fpcr)` (`gt = false`) / `FPCompareGT` (`gt = true`): false and `IOC`
for any NaN operand. -/
def fpCmpG (gt : Bool) (f : Fmt) (fpcr op1 op2 : Nat) : Bool × Exc :=
  let ((t1, _, v1), x1) := unpack f fpcr true op1
  let ((t2, _, v2), x2) := unpack f fpcr true op2
  if t1.isNaN || t2.isNaN then (false, x1 ++ x2 ++ raise IOC)
  else (if gt then Val.lt v2 v1 else !Val.lt v1 v2, x1 ++ x2 ++ processDenorms fpcr t1 t2)

/-! ## Arithmetic -/

/-- `FPTwo(sign, N)`. -/
def two (f : Fmt) (sign : Bool) : Nat := pack f sign (f.bias + 1) 0

/-- `FPOnePointFive(sign, N)`. -/
def onePointFive (f : Fmt) (sign : Bool) : Nat := pack f sign f.bias (2 ^ (f.fbits - 1))

/-- `FPMulX(op1, op2, fpcr)`: `FPMul` except that `0 × ∞` is `±2.0`. -/
def fpMulX (f : Fmt) (fpcr : Nat) (op1 op2 : Nat) : Nat × Exc :=
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
      if (inf1 && zero2) || (zero1 && inf2) then (two f (s1 != s2), {})
      else if inf1 || inf2 then (inf f (s1 != s2), {})
      else if zero1 || zero2 then (zero f (s1 != s2), {})
      else match mulExact v1.n v1.e v2.n v2.e with
        | none => (zero f (s1 != s2), {})
        | some (neg, m, ex) => fpRound f fpcr (roundingMode fpcr) neg m ex
    (r, pre ++ e ++ processDenorms fpcr t1 t2)

/-- The `FPCR` of the estimate and step functions under `FPCR.AH = 1`:
`fpcr.<FIZ,FZ> = '11'` and, for the step functions, `fpcr.RMode = '00'`. -/
def altFpcr (rmode : Bool) (fpcr : Nat) : Nat :=
  let v := fpcr ||| 1 ||| 2 ^ 24
  if rmode then v &&& (0xFFFFFFFF - 3 * 2 ^ 22) else v

/-- `FPRecipStepFused(op1, op2)` (`step = false`: `2.0 + op1' * op2`) and
`FPRSqrtStepFused(op1, op2)` (`step = true`: `(3.0 + op1' * op2) / 2.0`), with
`op1' = FPNeg(op1)`, read with the current `FPCR`. Under `AH = 1` (`altfp`) inputs and outputs
flush, rounding is to nearest and no exception is signalled (`fpexc = FALSE`). -/
def fpStepFused (rsqrt : Bool) (f : Fmt) (fpcr0 : Nat) (op1 op2 : Nat) : Nat × Exc :=
  let op1 := fpNeg f fpcr0 op1
  let altfp := ah fpcr0
  let fpcr := if altfp then altFpcr true fpcr0 else fpcr0
  let ((t1, s1, v1), x1) := unpack f fpcr true op1
  let ((t2, s2, v2), x2) := unpack f fpcr true op2
  let rounding := roundingMode fpcr
  let (r, e) : Nat × Exc :=
    match processNaNs f fpcr t1 t2 op1 op2 with
    | some (r, e) => (r, x1 ++ x2 ++ e)
    | none =>
      let inf1 := t1 = .infinity
      let inf2 := t2 = .infinity
      let zero1 := t1 = .zero
      let zero2 := t2 = .zero
      if (inf1 && zero2) || (zero1 && inf2) then
        ((if rsqrt then onePointFive f false else two f false), x1 ++ x2)
      else if inf1 || inf2 then (inf f (s1 != s2), x1 ++ x2)
      else
        match fmaExact (if rsqrt then 3 else 1) (if rsqrt then 0 else 1) v1.n v1.e v2.n v2.e with
        | none => (zero f (rounding = .rmi), x1 ++ x2)
        | some (neg, m, ex) =>
          let (r, e) := fpRound f fpcr rounding neg m (if rsqrt then ex - 1 else ex)
          (r, x1 ++ x2 ++ e)
  (r, if altfp then {} else e)

/-! ## Estimates -/

/-- `RecipEstimate(a, FALSE)` (`256 ≤ a < 512`): `r = (2^19 DIV (2a+1) + 1) DIV 2`. -/
def recipEstimate (a : Nat) : Nat := (2 ^ 19 / (a * 2 + 1) + 1) / 2

/-- The `while a * (b+1) * (b+1) < 2^28 do b = b + 1` loop of `RecipSqrtEstimate`, from `b`,
with `fuel` iterations at most (the loop ends below `b = 1024` for `a ≥ 256`). -/
def rsqrtLoop (a : Nat) : Nat → Nat → Nat
  | 0, b => b
  | fuel + 1, b => if a * (b + 1) * (b + 1) < 2 ^ 28 then rsqrtLoop a fuel (b + 1) else b

/-- `RecipSqrtEstimate(a, FALSE)` (`128 ≤ a < 512`). -/
def rsqrtEstimate (a : Nat) : Nat :=
  let a := if a < 256 then a * 2 + 1 else (a / 2 * 2 + 1) * 2
  let b := rsqrtLoop a 1024 512
  (b + 1) / 2

/-- `UnsignedRecipEstimate(operand)` of a 32-bit element. -/
def unsignedRecipEstimate (x : Nat) : Nat :=
  if x / 2 ^ 31 % 2 = 0 then 2 ^ 32 - 1 else recipEstimate (x / 2 ^ 23 % 2 ^ 9) % 2 ^ 9 * 2 ^ 23

/-- `UnsignedRSqrtEstimate(operand)` of a 32-bit element. -/
def unsignedRSqrtEstimate (x : Nat) : Nat :=
  if x / 2 ^ 30 % 4 = 0 then 2 ^ 32 - 1 else rsqrtEstimate (x / 2 ^ 23 % 2 ^ 9) % 2 ^ 9 * 2 ^ 23

/-- `|v| < 2^k` for a finite value (`Val.num`). -/
def absLtPow2 (v : Val) (k : Int) : Bool :=
  let (m, e) := v.mag
  m = 0 || decide ((Nat.log2 m : Int) + e < k)

/-- The 52-bit `fraction` and the exponent `exp` of the estimate functions: the operand's
fraction left-aligned to 52 bits and its biased exponent field. -/
def fracExp (f : Fmt) (x : Nat) : Nat × Int :=
  (fracOf f x * 2 ^ (52 - f.fbits), (expOf f x : Int))

/-- `FPRecipEstimate(operand, fpcr)` without FEAT_RPRES's increased precision (which only
applies to `AH = 1` single precision, excluded by the executor). -/
def fpRecipEstimate (f : Fmt) (fpcr0 : Nat) (op : Nat) : Nat × Exc :=
  let altfp := ah fpcr0
  let fpcr := if altfp then altFpcr true fpcr0 else fpcr0
  let ((t, s, v), x) := unpack f fpcr true op
  let rounding := roundingMode fpcr
  let (r, e) : Nat × Exc :=
    if t.isNaN then let (r, e) := processNaN f fpcr t op; (r, x ++ e)
    else if t = .infinity then (zero f s, x)
    else if t = .zero then (inf f s, x ++ raise DZC)
    else if absLtPow2 v (-(2 ^ (f.ebits - 1) : Int)) then
      -- `Abs(value) < 2^-128` (single) / `2^-1024` (double)
      let toInf := match rounding with
        | .rne => true | .rpi => !s | .rmi => s | _ => false
      ((if toInf then inf f s else maxNormal f s), x ++ raise OFC ++ raise IXC)
    else if fz fpcr && !absLtPow2 v (2 ^ (f.ebits - 1) - 2 : Int) then
      -- `FPCR.FZ == '1' && Abs(value) >= 2^126` (single) / `2^1022` (double)
      (zero f s, x ++ ⟨0, UFC⟩)
    else
      let (fr, ex) := fracExp f op
      let (fr, ex) : Nat × Int :=
        if ex = 0 then
          if fr / 2 ^ 51 % 2 = 0 then (fr * 4 % 2 ^ 52, -1) else (fr * 2 % 2 ^ 52, 0)
        else (fr, ex)
      let scaled := 256 + fr / 2 ^ 44
      let resultExp : Int := (2 ^ f.ebits - 3 : Nat) - ex
      let est := recipEstimate scaled
      let fr := est % 256 * 2 ^ 44
      let (fr, resultExp) : Nat × Int :=
        if resultExp = 0 then (2 ^ 51 + fr / 2, 0)
        else if resultExp = -1 then (2 ^ 50 + fr / 4, 0)
        else (fr, resultExp)
      (pack f s (resultExp.toNat % 2 ^ f.ebits) (fr / 2 ^ (52 - f.fbits)), x)
  (r, if altfp then {} else e)

/-- `FPRSqrtEstimate(operand, fpcr)` without FEAT_RPRES (see `fpRecipEstimate`). -/
def fpRSqrtEstimate (f : Fmt) (fpcr0 : Nat) (op : Nat) : Nat × Exc :=
  let altfp := ah fpcr0
  let fpcr := if altfp then altFpcr false fpcr0 else fpcr0
  let ((t, s, _), x) := unpack f fpcr true op
  let (r, e) : Nat × Exc :=
    if t.isNaN then let (r, e) := processNaN f fpcr t op; (r, x ++ e)
    else if t = .zero then (inf f s, x ++ raise DZC)
    else if s then (defaultNaN f fpcr, x ++ raise IOC)
    else if t = .infinity then (zero f false, x)
    else
      let (fr, ex) := fracExp f op
      -- normalise a subnormal: `while fraction<51> == '0' do fraction = fraction<50:0>:'0';
      -- exp = exp - 1`, then drop the leading one
      let lz : Nat := if ex = 0 then 51 - Nat.log2 fr else 0
      let (fr, ex) : Nat × Int :=
        if ex = 0 then (fr * 2 ^ (lz + 1) % 2 ^ 52, -(lz : Int)) else (fr, ex)
      let scaled := if ex % 2 = 0 then 256 + fr / 2 ^ 44 else 128 + fr / 2 ^ 45
      let resultExp : Int := (3 * (2 ^ (f.ebits - 1) : Nat) - 4 - ex) / 2
      let est := rsqrtEstimate scaled
      (pack f false (resultExp.toNat % 2 ^ f.ebits) (est % 256 * 2 ^ (f.fbits - 8)), x)
  (r, if altfp then {} else e)

/-- `FPRecpX(op, fpcr)`: the sign, the inverted exponent (`Ones - 1` for a zero exponent) and a
zero fraction; NaNs are processed. -/
def fpRecpX (f : Fmt) (fpcr0 : Nat) (op : Nat) : Nat × Exc :=
  let altfp := ah fpcr0
  let fpcr := if altfp then altFpcr false fpcr0 else fpcr0
  let ((t, s, _), x) := unpack f fpcr true op
  let ex := expOf f op
  let (r, e) : Nat × Exc :=
    if t.isNaN then let (r, e) := processNaN f fpcr t op; (r, x ++ e)
    else if ex = 0 then (pack f s (2 ^ f.ebits - 2) 0, x)
    else (pack f s (ex ^^^ (2 ^ f.ebits - 1)) 0, x)
  (r, if altfp then {} else e)

/-! ## Conversions -/

/-- `FPToFixed(op, fbits, unsigned, fpcr, rounding, M)`: `FP.fpToFixed` with the value scaled by
`2^fbits` before rounding. -/
def fpToFixedF (f : Fmt) (fpcr : Nat) (unsigned : Bool) (rounding : RM) (M fbits : Nat)
    (op : Nat) : Nat × Exc :=
  let ((t, s, v), x) := unpack f fpcr (!ah fpcr) op
  let nanExc : Exc := if t.isNaN then raise IOC else {}
  match v with
  | .inf neg =>
    let (r, _) := satQ M unsigned (if neg then -(2 ^ (M + 1) : Int) else 2 ^ (M + 1))
    (r, x ++ nanExc ++ raise IOC)
  | .num n ex =>
    let (i, inexact) := if n = 0 then ((0 : Int), false)
      else roundToInt rounding s n.natAbs (ex + fbits)
    let (r, ovf) := satQ M unsigned i
    (r, x ++ nanExc ++ (if ovf then raise IOC else if inexact then raise IXC else {}))

/-- `FixedToFP(op, fbits, unsigned, fpcr, rounding, N)` of an `M`-bit value `op < 2^M`:
`Int(op) / 2^fbits` rounded. -/
def fixedToFPF (f : Fmt) (fpcr : Nat) (unsigned : Bool) (rounding : RM) (M fbits : Nat)
    (op : Nat) : Nat × Exc :=
  let i : Int := if unsigned || op < 2 ^ (M - 1) then op else (op : Int) - 2 ^ M
  if i = 0 then (zero f false, {}) else fpRound f fpcr rounding (decide (i < 0)) i.natAbs (-(fbits : Int))

/-- `FPRoundBase` with `FPRounding_ODD`: round toward zero and set the least significant bit of
an inexact (not flushed, not overflowed) result. -/
def fpRoundOdd (f : Fmt) (fpcr : Nat) (neg : Bool) (m : Nat) (e : Int) : Nat × Exc :=
  let altfp := ah fpcr
  let r := round f .rz neg m e
  let trappedUF := ufe fpcr
  if !altfp && fz fpcr && r.tinyBefore then (zero f neg, ⟨0, UFC⟩) else
  let uf1 : Exc := if !altfp && r.tinyBefore && (r.roundErr || trappedUF) then raise UFC else {}
  if altfp && r.tinyAfter && fz fpcr then (zero f neg, ⟨IXC, UFC⟩) else
  let uf2 : Exc := if altfp && r.tinyAfter && (r.roundErr || trappedUF) then raise UFC else {}
  let ovf : Exc := if r.overflow then raise OFC else {}
  let ix : Exc := if r.inexact then raise IXC else {}
  ((if r.roundErr && !r.overflow then r.bits ||| 1 else r.bits), uf1 ++ uf2 ++ ovf ++ ix)

/-- `FPConvert(op, fpcr, FPRounding_ODD, 32)` of a double (`FCVTXN`). -/
def fpConvertOdd (fpcr : Nat) (op : Nat) : Nat × Exc :=
  let f := binary64
  let g := binary32
  let ((t, s, v), x) := unpack f fpcr true op
  let (r, e) :=
    if t.isNaN then
      (if dn fpcr then defaultNaN g fpcr else convertNaN f g op,
       if t = .snan then raise IOC else {})
    else if t = .infinity then (inf g s, {})
    else if t = .zero then (zero g s, {})
    else
      let (m, ex) := v.mag
      let (r, e) := fpRoundOdd g fpcr s m ex
      (r, e ++ processDenorm fpcr t)
  (r, x ++ e)

/-! ## Three same -/

/-- Advanced SIMD (scalar) three same, floating point (`opcode = w<15:11> = 11xxx`, `a = size<1>`,
`sz = size<0>`), on `datasize` bits, `x = V[n]`, `y = V[m]`, `d = V[d]` (FMLA/FMLS):

| opcode | `U=0, a=0` | `U=0, a=1` | `U=1, a=0` | `U=1, a=1` |
|---|---|---|---|---|
| 11000 | FMAXNM | FMINNM | FMAXNMP | FMINNMP |
| 11001 | FMLA | FMLS | | |
| 11010 | FADD | FSUB | FADDP | FABD |
| 11011 | FMULX | | FMUL | |
| 11100 | FCMEQ | | FCMGE | FCMGT |
| 11101 | | | FACGE | FACGT |
| 11110 | FMAX | FMIN | FMAXP | FMINP |
| 11111 | FRECPS | FRSQRTS | FDIV | | -/
def threeSameFP (U a : Bool) (sz opcode datasize fpcr x y d : Nat) : Nat × Exc :=
  let f := fmtOf sz
  let e := fesize sz
  let n := datasize / e
  let pairwise := U && (opcode = 0b11000 || (opcode = 0b11010 && !a) || opcode = 0b11110)
  let op1 (i : Nat) : Nat := if pairwise then pairElem x y e n (2 * i) else elem x e i
  let op2 (i : Nat) : Nat := if pairwise then pairElem x y e n (2 * i + 1) else elem y e i
  fpLanes e n fun i =>
    let p := op1 i
    let q := op2 i
    if opcode = 0b11000 then fpMaxMinNum (!a) f fpcr p q
    else if opcode = 0b11001 then
      fpMulAdd f fpcr (elem d e i) (if a then fpNeg f fpcr p else p) q
    else if opcode = 0b11010 then
      if !a then fpAdd f fpcr p q
      else if !U then fpSub f fpcr p q
      else let (r, ex) := fpSub f fpcr p q; (fpAbs f fpcr r, ex)
    else if opcode = 0b11011 then (if U then fpMul f fpcr p q else fpMulX f fpcr p q)
    else if opcode = 0b11100 || opcode = 0b11101 then
      let (p, q) := if opcode = 0b11101 then (fpAbs f fpcr p, fpAbs f fpcr q) else (p, q)
      let (b, ex) := if !U then fpCmpEQ f fpcr p q else fpCmpG a f fpcr p q
      (mask e b, ex)
    else if opcode = 0b11110 then fpMaxMin (!a) f fpcr (ah fpcr) p q
    else if U then fpDiv f fpcr p q
    else fpStepFused a f fpcr p q

/-! ## Two-register miscellaneous -/

/-- Advanced SIMD (scalar) two-register miscellaneous, floating point (`opcode = w<16:12>`,
`a = size<1>`, `sz = size<0>`), same-width forms on `datasize` bits, `x = V[n]`:

* `11000`/`11001` FRINTN/FRINTP/FRINTM/FRINTZ (`U = 0`, rounding `FPDecodeRounding(o1:a)` with
  `o1 = opcode<0>`), FRINTA (`U = 1, a = 0, o1 = 0`), FRINTX (`U = 1, a = 0, o1 = 1`), FRINTI
  (`U = 1, a = 1, o1 = 1`);
* `11010`/`11011` FCVTNS/NU/PS/PU/MS/MU/ZS/ZU (rounding `FPDecodeRounding(o1:a)`), `11100`
  FCVTAS/FCVTAU (`a = 0`, ties away), URECPE/URSQRTE (`a = 1`, 32-bit elements);
* `11101` SCVTF/UCVTF (`a = 0`), FRECPE/FRSQRTE (`a = 1`);
* `01100` FCMGT/FCMGE #0.0, `01101` FCMEQ/FCMLE #0.0, `01110` FCMLT #0.0 (`a = 1`);
* `01111` FABS/FNEG (`a = 1`), `11111` FRECPX (`U = 0`, scalar) / FSQRT (`U = 1`) (`a = 1`). -/
def twoMiscFP (U a : Bool) (sz opcode datasize fpcr x : Nat) : Nat × Exc :=
  let f := fmtOf sz
  let e := fesize sz
  let n := datasize / e
  let o1 := opcode % 2
  let rmode := o1 * 2 + (if a then 1 else 0)
  fpLanes e n fun i =>
    let p := elem x e i
    if opcode = 0b11000 || opcode = 0b11001 then
      let (rounding, exact) : RM × Bool :=
        if !U then (decodeRounding rmode, false)
        else if o1 = 0 then (.rna, false)
        else if !a then (roundingMode fpcr, true)
        else (roundingMode fpcr, false)
      fpRoundInt f fpcr rounding exact p
    else if opcode = 0b11010 || opcode = 0b11011 then fpToFixed f fpcr U (decodeRounding rmode) e p
    else if opcode = 0b11100 then
      if !a then fpToFixed f fpcr U .rna e p
      else ((if U then unsignedRSqrtEstimate p else unsignedRecipEstimate p), {})
    else if opcode = 0b11101 then
      if !a then fixedToFP f fpcr U (roundingMode fpcr) e p
      else if U then fpRSqrtEstimate f fpcr p else fpRecipEstimate f fpcr p
    else if opcode = 0b01100 then
      let (b, ex) := fpCmpG (!U) f fpcr p (zero f false)
      (mask e b, ex)
    else if opcode = 0b01101 then
      let (b, ex) := if !U then fpCmpEQ f fpcr p (zero f false) else fpCmpG false f fpcr (zero f false) p
      (mask e b, ex)
    else if opcode = 0b01110 then
      let (b, ex) := fpCmpG true f fpcr (zero f false) p
      (mask e b, ex)
    else if opcode = 0b01111 then ((if U then fpNeg f fpcr p else fpAbs f fpcr p), {})
    else if U then fpSqrt f fpcr p
    else fpRecpX f fpcr p

/-- FCVTN/FCVTN2 (`U = 0`) and FCVTXN/FCVTXN2 (`U = 1`) from double: the `n` single-precision
results of the double elements of `x = V[n, 128]`. -/
def fcvtnOp (U : Bool) (n fpcr x : Nat) : Nat × Exc :=
  fpLanes 32 n fun i =>
    let p := elem x 64 i
    if U then fpConvertOdd fpcr p else fpConvert binary64 binary32 fpcr (roundingMode fpcr) p

/-- FCVTL/FCVTL2 from single: the two double results of the single elements of the 64-bit `x`
(`Vpart[n, part]`). -/
def fcvtlOp (fpcr x : Nat) : Nat × Exc :=
  fpLanes 64 2 fun i => fpConvert binary32 binary64 fpcr (roundingMode fpcr) (elem x 32 i)

/-! ## Reductions -/

/-- The operation of a floating-point reduction step (`ReduceOp`), on `lo` and `hi`:
`0` FMAXNUM, `1` FMINNUM, `2` FMAX, `3` FMIN, `4` FADD. -/
def reduceStep (op : Nat) (f : Fmt) (fpcr lo hi : Nat) : Nat × Exc :=
  if op = 0 then fpMaxMinNum true f fpcr lo hi
  else if op = 1 then fpMaxMinNum false f fpcr lo hi
  else if op = 2 then fpMaxMin true f fpcr (ah fpcr) lo hi
  else if op = 3 then fpMaxMin false f fpcr (ah fpcr) lo hi
  else fpAdd f fpcr lo hi

/-- `Reduce(op, V[n, 128], 32)` over four single-precision elements: the ASL's halving tree
`op(op(e0, e1), op(e2, e3))`. -/
def reduce4 (op : Nat) (fpcr x : Nat) : Nat × Exc :=
  let f := binary32
  let lo := reduceStep op f fpcr (elem x 32 0) (elem x 32 1)
  let hi := reduceStep op f fpcr (elem x 32 2) (elem x 32 3)
  let r := reduceStep op f fpcr lo.1 hi.1
  (r.1, hi.2 ++ lo.2 ++ r.2)

/-- `Reduce(op, V[n, 2 * esize], esize)` over two elements (the scalar pairwise forms). -/
def reduce2 (op sz fpcr x : Nat) : Nat × Exc :=
  let e := fesize sz
  reduceStep op (fmtOf sz) fpcr (elem x e 0) (elem x e 1)

/-! ## Vector x indexed element -/

/-- Floating-point (scalar) x indexed element (`opcode = w<15:12>`): `0001` FMLA, `0101` FMLS,
`1001` FMUL (`U = 0`) / FMULX (`U = 1`), with the element `el`, `x = V[n]`, `d = V[d]`. -/
def byElemFP (U : Bool) (sz opcode datasize fpcr x d el : Nat) : Nat × Exc :=
  let f := fmtOf sz
  let e := fesize sz
  fpLanes e (datasize / e) fun i =>
    let p := elem x e i
    if opcode = 0b1001 then (if U then fpMulX f fpcr p el else fpMul f fpcr p el)
    else fpMulAdd f fpcr (elem d e i) (if opcode = 0b0101 then fpNeg f fpcr p else p) el

end Janus.Arm64.NeonFP
