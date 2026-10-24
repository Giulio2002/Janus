import Janus

/-!
# The specifications themselves against Berkeley SoftFloat (docs/AUDIT-FP.md, row SPEC-TF)

`Janus.Float.add`/`mul`/`fma`/`truncInt` (`Janus/Float/Spec.lean`) are what the example theorems
state. `scripts/testfloat.sh` checks the *machine models* against SoftFloat; this checks the
*specifications* directly, so that "the IEEE sum" in a printed theorem is checked against an
independent IEEE implementation and not only through the bridge lemmas:

```
testfloat_gen -rnear_even f64_add | lake env lean --run audit/rt-fp/SpecTestFloat.lean f64_add near_even
```

A vector agrees when the specification is `some r` with `r` the expected bits and the expected
result is not a NaN, or the specification is `none` and the expected result is a NaN (the
specifications leave the NaN open). For `f64_to_i64` / `f64_to_ui64` with `minMag`,
`truncInt` must be the expected integer whenever SoftFloat raises no invalid flag. Prints
`vectors N mismatches M` and the first mismatches; exit status 1 on a mismatch.
-/

open Janus.Float

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex (s : String) : Option Nat :=
  s.foldl (fun acc c => match acc, hexDigit? c with
    | some a, some d => some (a * 16 + d)
    | _, _ => none) (some 0)

def rmOf : String → Option RM
  | "near_even" => some .rne | "minMag" => some .rz | "min" => some .rmi
  | "max" => some .rpi | "near_maxMag" => some .rna | _ => none

def fmtOf (s : String) : Option Fmt :=
  if s = "f32" then some binary32 else if s = "f64" then some binary64 else none

/-- `true` when the vector agrees with the specification. -/
def check (fn : String) (rm : RM) (ws : List Nat) : Option Bool := do
  match fn.splitOn "_", ws with
  | [f, "add"], [a, b, r, _] => let g ← fmtOf f; some (agree g (add g rm a b) r)
  | [f, "mul"], [a, b, r, _] => let g ← fmtOf f; some (agree g (mul g rm a b) r)
  | [f, "mulAdd"], [a, b, c, r, _] => let g ← fmtOf f; some (agree g (fma g rm a b c) r)
  | [f, "to", i], [a, r, fl] =>
    let g ← fmtOf f
    let w := if i = "i64" || i = "ui64" then 64 else 32
    if fl &&& 0x10 ≠ 0 then some true   -- invalid: out of range or NaN, nothing to compare
    else match truncInt g a with
      | none => some false
      | some v =>
        let signed := i = "i64" || i = "i32"
        let want : Int := if signed && r ≥ 2 ^ (w - 1) then (r : Int) - 2 ^ w else r
        some (v == want)
  | _, _ => none
where
  agree (g : Fmt) (spec : Option Nat) (r : Nat) : Bool :=
    match spec with
    | some x => x == r && !isNaN g r
    | none => isNaN g r

partial def loop (h : IO.FS.Stream) (fn : String) (rm : RM) (n bad : Nat) (shown : Nat) :
    IO (Nat × Nat) := do
  let line ← h.getLine
  if line.isEmpty then return (n, bad)
  let ws := (line.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.filterMap parseHex
  match check fn rm ws with
  | some true => loop h fn rm (n + 1) bad shown
  | some false =>
    if shown < 10 then IO.println s!"MISMATCH {line.trimAscii}"
    loop h fn rm (n + 1) (bad + 1) (shown + 1)
  | none => throw (IO.userError s!"cannot check {fn}: {line}")

def main (args : List String) : IO UInt32 := do
  let fn := args[0]!
  let some rm := rmOf args[1]! | throw (IO.userError "rounding")
  let (n, bad) ← loop (← IO.getStdin) fn rm 0 0 0
  IO.println s!"{fn} {args[1]!}: vectors {n} mismatches {bad}"
  return (if bad = 0 then 0 else 1)
