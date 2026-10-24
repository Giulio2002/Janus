import Janus

/-!
# `janus-testfloat`: check the floating-point model against Berkeley TestFloat vectors

`testfloat_gen` (Berkeley TestFloat 3e, results computed by Berkeley SoftFloat 3e) writes one
test vector per line: the operands, the expected result and the expected exception flags, in
hex (`flags`: `0x10` invalid, `0x08` divide by zero, `0x04` overflow, `0x02` underflow, `0x01`
inexact). This executable runs each vector through the Janus models and counts the vectors on
which the result bits or the flags differ:

```
testfloat_gen -tininessbefore -rminMag f64_add | janus-testfloat arm f64_add minMag
testfloat_gen -tininessafter -exact -rnear_even f64_to_i64 | janus-testfloat x86 f64_to_i64 near_even
```

`isa` is `arm` (`Janus.Arm64.FP` with `FPCR.RMode` from the rounding argument, `AH = DN = 0`;
compare with SoftFloat's `ARM-VFPv2` specialization and `-tininessbefore`), `arm-dn` (`DN = 1`,
SoftFloat `ARM-VFPv2-defaultNaN`), `arm-ah` (`AH = 1`: tininess after rounding; NaN results
are compared as "is a NaN", since `AH = 1` changes the NaN rules) or `x86` (`Janus.Amd64.FP`
with `MXCSR.RC` from the rounding argument, all exceptions masked; SoftFloat `8086-SSE`,
`-tininessafter`). The input-denormal flags (`IDC`, `DE`) have no TestFloat counterpart and
are ignored. For the conversions to integers and `roundToInt`, the rounding argument is the
instruction's own rounding (`FCVTN/P/M/Z/A`, `FRINTN/P/M/Z/A`, `CVTTSD2SI`, `ROUNDSD imm8`); an
optional fourth argument `exact` selects `FRINTX`-like behaviour (the vectors must then be
generated with `-exact`).

This is a test tool, not part of the trusted base.
-/

open Janus.Float

namespace TestFloat

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex (s : String) : Option Nat :=
  s.foldl (fun acc c => match acc, hexDigit? c with
    | some a, some d => some (a * 16 + d)
    | _, _ => none) (some 0)

def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- TestFloat flags of the Arm `FPSR` bits (IDC ignored). -/
def armFlags (e : Janus.Arm64.FP.Exc) : Nat :=
  let b := e.proc ||| e.direct
  (if b &&& 1 ≠ 0 then 0x10 else 0) + (if b &&& 2 ≠ 0 then 0x08 else 0) +
  (if b &&& 4 ≠ 0 then 0x04 else 0) + (if b &&& 8 ≠ 0 then 0x02 else 0) +
  (if b &&& 16 ≠ 0 then 0x01 else 0)

/-- TestFloat flags of the x86 `MXCSR` flags (DE ignored). -/
def x86Flags (b : Nat) : Nat :=
  (if b &&& 1 ≠ 0 then 0x10 else 0) + (if b &&& 4 ≠ 0 then 0x08 else 0) +
  (if b &&& 8 ≠ 0 then 0x04 else 0) + (if b &&& 0x10 ≠ 0 then 0x02 else 0) +
  (if b &&& 0x20 ≠ 0 then 0x01 else 0)

def rmOf : String → Option RM
  | "near_even" => some .rne
  | "minMag" => some .rz
  | "min" => some .rmi
  | "max" => some .rpi
  | "near_maxMag" => some .rna
  | _ => none

/-- `FPCR.RMode` of a rounding direction (`none` for ties-away, which has no RMode). -/
def armRMode : RM → Option Nat
  | .rne => some 0 | .rpi => some 1 | .rmi => some 2 | .rz => some 3 | .rna => none

/-- `MXCSR.RC` / `ROUNDSD imm8<1:0>` of a rounding direction. -/
def x86RC : RM → Option Nat
  | .rne => some 0 | .rmi => some 1 | .rpi => some 2 | .rz => some 3 | .rna => none

def fmtOfName (s : String) : Option Fmt :=
  if s = "f32" then some binary32 else if s = "f64" then some binary64 else none

def intOfName (s : String) : Option (Bool × Nat) :=
  if s = "i32" then some (false, 32) else if s = "i64" then some (false, 64)
  else if s = "ui32" then some (true, 32) else if s = "ui64" then some (true, 64) else none

/-- The model's `(result, flags)` for one vector, or `none` if the combination is not
applicable to the ISA. -/
def evalArm (fpcr : Nat) (fn : String) (rm : RM) (exact : Bool) (ops : List Nat) :
    Option (Nat × Nat) := open Janus.Arm64.FP in do
  let parts := fn.splitOn "_"
  let res (p : Nat × Exc) : Option (Nat × Nat) := some (p.1, armFlags p.2)
  match parts, ops with
  | [f, "add"], [a, b] => res (fpAdd (← fmtOfName f) fpcr a b)
  | [f, "sub"], [a, b] => res (fpSub (← fmtOfName f) fpcr a b)
  | [f, "mul"], [a, b] => res (fpMul (← fmtOfName f) fpcr a b)
  | [f, "div"], [a, b] => res (fpDiv (← fmtOfName f) fpcr a b)
  | [f, "mulAdd"], [a, b, c] => res (fpMulAdd (← fmtOfName f) fpcr c a b)
  | [f, "sqrt"], [a] => res (fpSqrt (← fmtOfName f) fpcr a)
  | [f, "roundToInt"], [a] => res (fpRoundInt (← fmtOfName f) fpcr rm exact a)
  | [f, cmp], [a, b] | [f, cmp, _], [a, b] =>
    let fmt ← fmtOfName f
    let signal := if parts.length = 3 then parts[2]! = "signaling" else cmp != "eq"
    let (nzcv, e) := fpCompare fmt fpcr signal a b
    let r := if cmp = "eq" then nzcv = 0b0110 else if cmp = "lt" then nzcv = 0b1000
      else if cmp = "le" then nzcv = 0b1000 || nzcv = 0b0110 else false
    if cmp = "eq" || cmp = "lt" || cmp = "le" then some (if r then 1 else 0, armFlags e) else none
  | [x, "to", y], [a] =>
    match fmtOfName x, fmtOfName y, intOfName x, intOfName y with
    | some f, some g, _, _ => res (fpConvert f g fpcr (roundingMode fpcr) a)
    | _, some g, some (u, w), _ => res (fixedToFP g fpcr u (roundingMode fpcr) w a)
    | some f, _, _, some (u, w) => res (fpToFixed f fpcr u rm w a)
    | _, _, _, _ => none
  | _, _ => none

def evalX86 (mx : Nat) (fn : String) (rm : RM) (exact : Bool) (ops : List Nat) :
    Option (Nat × Nat) := open Janus.Amd64 in do
  let parts := fn.splitOn "_"
  let res (o : FP.XR) : Option (Nat × Nat) :=
    if o.trap mx then some (0, 0xFF)  -- a trap with everything masked: never expected
    else some (o.res, x86Flags o.flags)
  match parts, ops with
  | [f, "add"], [a, b] => res (FP.binop .add (← fmtOfName f) mx a b)
  | [f, "sub"], [a, b] => res (FP.binop .sub (← fmtOfName f) mx a b)
  | [f, "mul"], [a, b] => res (FP.binop .mul (← fmtOfName f) mx a b)
  | [f, "div"], [a, b] => res (FP.binop .div (← fmtOfName f) mx a b)
  | [f, "sqrt"], [a] => res (FP.sqrt (← fmtOfName f) mx a)
  | [f, "roundToInt"], [a] =>
    let rc ← x86RC rm
    res (FP.roundInt (← fmtOfName f) mx (rc + (if exact then 0 else 8)) a)
  | [f, cmp], [a, b] | [f, cmp, _], [a, b] =>
    let fmt ← fmtOfName f
    let signal := if parts.length = 3 then parts[2]! = "signaling" else cmp != "eq"
    let o := FP.comis signal fmt mx a b
    if o.trap mx then some (0, 0xFF) else
    let zf := o.res / 4 % 2 = 1
    let pf := o.res / 2 % 2 = 1
    let cf := o.res % 2 = 1
    let r := if cmp = "eq" then zf && !pf else if cmp = "lt" then cf && !pf
      else if cmp = "le" then (cf || zf) && !pf else false
    if cmp = "eq" || cmp = "lt" || cmp = "le" then some (if r then 1 else 0, x86Flags o.flags) else none
  | [x, "to", y], [a] =>
    match fmtOfName x, fmtOfName y, intOfName x, intOfName y with
    | some f, some g, _, _ => res (FP.convert f g mx a)
    | _, some g, some (false, w), _ => res (FP.ofInt g mx w a)
    | some f, _, _, some (false, w) => res (FP.toInt f mx rm w a)
    | _, _, _, _ => none
  | _, _ => none

end TestFloat

open TestFloat in
def main (args : List String) : IO UInt32 := do
  match args with
  | isa :: fn :: rmS :: rest =>
    let some rm := rmOf rmS | IO.eprintln s!"bad rounding {rmS}"; return 2
    let exact := rest.contains "exact"
    let nanLoose := isa = "arm-ah"
    -- the format of the result, for "is a NaN" comparisons
    let resFmt : Option Fmt :=
      match (fn.splitOn "_").getLast? with
      | some "f32" => some binary32
      | some "f64" => some binary64
      | _ => fmtOfName ((fn.splitOn "_").headD "")
    let eval : List Nat → Option (Nat × Nat) :=
      if isa = "x86" then
        match x86RC rm with
        | some rc => evalX86 (0x1F80 + rc * 2 ^ 13) fn rm exact
        | none => evalX86 0x1F80 fn rm exact
      else
        let base := if isa = "arm-dn" then 2 ^ 25 else if isa = "arm-ah" then 2 else 0
        let fpcr := base + (armRMode rm).getD 0 * 2 ^ 22
        evalArm fpcr fn rm exact
    let stdin ← IO.getStdin
    let mut total := 0
    let mut bad := 0
    let mut skipped := 0
    let mut known := 0
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let toks := (line.trimAscii.toString.splitOn " ").filter (· ≠ "")
      if toks.length < 3 then continue
      let nums := toks.filterMap parseHex
      if nums.length ≠ toks.length then continue
      let ops := nums.take (nums.length - 2)
      let want := nums[nums.length - 2]!
      let wantFl := nums[nums.length - 1]!
      total := total + 1
      match eval ops with
      | none => skipped := skipped + 1
      | some (got, gotFl) =>
        let sameRes :=
          got == want ||
          (nanLoose && match resFmt with
            | some f => isNaN f got && isNaN f want
            | none => false)
        let opFmt := fmtOfName ((fn.splitOn "_").headD "")
        let nanIn := match opFmt with
          | some f => ops.any (isNaN f)
          | none => false
        let bothNaN := match resFmt with
          | some f => isNaN f got && isNaN f want
          | none => false
        -- Known SoftFloat/Arm differences, counted apart: SoftFloat's ARM-VFPv2 `mulAdd` gives
        -- priority to the NaN of a product operand, Arm's `FPProcessNaNs3` to the addend; and
        -- `FPCR.AH = 1` has its own NaN rules (no `IOC` for `0 * inf + qNaN`), which SoftFloat
        -- does not model.
        let isKnown := nanIn && bothNaN &&
          ((isa = "arm" && (fn.endsWith "mulAdd") && gotFl == wantFl) || isa = "arm-ah")
        if (!sameRes || gotFl != wantFl) && isKnown then
          known := known + 1
        else if !sameRes || gotFl != wantFl then
          bad := bad + 1
          if bad ≤ 20 then
            IO.println s!"MISMATCH {fn} {rmS} {(ops.map hex)}: model {hex got} flags {hex gotFl}, \
              testfloat {hex want} flags {hex wantFl}"
    IO.println s!"{isa} {fn} {rmS}{if exact then " exact" else ""}: {total} vectors, {bad} mismatches, {skipped} not applicable, {known} known NaN-rule differences"
    return (if bad = 0 then 0 else 1)
  | _ =>
    IO.eprintln "usage: janus-testfloat arm|arm-dn|arm-ah|x86 <function> <rounding> [exact] < vectors"
    return 2
