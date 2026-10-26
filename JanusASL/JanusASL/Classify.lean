import Janus

/-! # Which words are in the proved subset (`janus verify --asl`)

`classify w` names the proved encoding class of the 32-bit word `w`: each branch tests exactly the
hypotheses of one `JanusASL.Proofs.stepOK_<class>` theorem (Run.lean), in that theorem's form, so
`JanusASL.Verify.classify_sound` turns `classify w = some c` into `StepOK w`. `covered p` checks
every word of a program, and that its code and stubs are untagged (below `2^56`), which is what
`Ensures.toASL` needs about the program. It is a `Bool`, decided by kernel evaluation
(`decide +kernel`) on the very `Extracted.program` constant that `janus verify` identity-checks.

This module imports only `Janus` (not the ASL model), so the coverage check and the report of
uncovered words run without loading ArmASL. -/

namespace JanusASL.Classify
open Janus

/-- The proved encoding class of `w` (the name of its `stepOK_<class>` theorem), if any. The
conditions are the theorems' hypotheses verbatim; the order only matters for the reported name. -/
def classify (w : Nat) : Option String :=
  if w < 2 ^ 32 then
    if (w / 2 ^ 23) % 64 = 0b100010 then some "addSubImm"
    else if (w / 2 ^ 24) % 32 = 0b01011 ∧ (w / 2 ^ 21) % 2 = 0 ∧ (w / 2 ^ 22) % 4 ≠ 3 ∧
        ((w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) then some "addSubShifted"
    else if (w / 2 ^ 24) % 32 = 0b01011 ∧ (w / 2 ^ 21) % 8 = 1 ∧ (w / 2 ^ 10) % 8 ≤ 4 then some "addSubExt"
    else if (w / 2 ^ 21) % 256 = 0b11010000 ∧ (w / 2 ^ 10) % 64 = 0 then some "addSubCarry"
    else if (w / 2 ^ 24) % 32 = 0b01010 ∧ ((w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) then
      some "logicalShifted"
    else if (w / 2 ^ 23) % 64 = 0b100100 ∧ ((w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0) ∧
        (Janus.Arm64.decodeBitMasks (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 21 16)
          true (if Janus.Arm64.bit w 31 then 64 else 32)).isSome = true then some "logicalImm"
    else if (w / 2 ^ 23) % 64 = 0b100101 ∧ (w / 2 ^ 29) % 4 ≠ 1 ∧
        ((w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0) then some "moveWide"
    else if (w / 2 ^ 23) % 64 = 0b100110 ∧ (w / 2 ^ 29) % 4 ≠ 3 ∧ (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2 ∧
        ((w / 2 ^ 31) % 2 = 1 ∨ ((w / 2 ^ 16) % 64 < 32 ∧ (w / 2 ^ 10) % 64 < 32)) ∧
        (Janus.Arm64.decodeBitMasks (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 21 16)
          false (if Janus.Arm64.bit w 31 then 64 else 32)).isSome = true then some "bitfield"
    else if (w / 2 ^ 23) % 64 = 0b100111 ∧ (w / 2 ^ 29) % 4 = 0 ∧ (w / 2 ^ 21) % 2 = 0 ∧
        (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2 ∧ ((w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) then some "extr"
    else if (w / 2 ^ 24) % 32 = 0b10000 then some "pcrel"
    else if (w / 2 ^ 21) % 512 = 0b011010100 ∧ (w / 2 ^ 11) % 2 = 0 then some "condSel"
    else if (w / 2 ^ 21) % 512 = 0b111010010 ∧ (w / 2 ^ 10) % 2 = 0 ∧ (w / 2 ^ 4) % 2 = 0 ∧
        (w / 2 ^ 11) % 2 = 0 then some "condCmpReg"
    else if (w / 2 ^ 21) % 512 = 0b111010010 ∧ (w / 2 ^ 10) % 2 = 0 ∧ (w / 2 ^ 4) % 2 = 0 ∧
        (w / 2 ^ 11) % 2 = 1 then some "condCmpImm"
    else if (w / 2 ^ 21) % 1024 = 0b0011011000 then some "madd"
    else if (w / 2 ^ 24) % 256 = 0b10011011 ∧ (w / 2 ^ 21) % 4 = 1 then some "maddl"
    else if (w / 2 ^ 24) % 256 = 0b10011011 ∧ (w / 2 ^ 21) % 4 = 2 ∧ (w / 2 ^ 15) % 2 = 0 ∧
        (w / 2 ^ 10) % 32 = 31 then some "mulh"
    else if (w / 2 ^ 21) % 1024 = 0b0011010110 ∧ (w / 2 ^ 11) % 32 = 1 then some "div"
    else if (w / 2 ^ 21) % 1024 = 0b0011010110 ∧ (w / 2 ^ 12) % 16 = 0b0010 then some "shiftV"
    else if (w / 2 ^ 21) % 1024 = 0b1011010110 ∧ (w / 2 ^ 16) % 32 = 0 ∧ (w / 2 ^ 10) % 64 = 0 then some "rbit"
    else if (w / 2 ^ 21) % 1024 = 0b1011010110 ∧ (w / 2 ^ 16) % 32 = 0 ∧ (w / 2 ^ 10) % 64 = 4 then some "clz"
    else if (w / 2 ^ 21) % 1024 = 0b1011010110 ∧ (w / 2 ^ 16) % 32 = 0 ∧ (w / 2 ^ 10) % 64 = 5 then some "cls"
    else if (w / 2 ^ 21) % 1024 = 0b1011010110 ∧ (w / 2 ^ 16) % 32 = 0 ∧ (w / 2 ^ 10) % 64 = 1 then some "rev16"
    else if (w / 2 ^ 21) % 1024 = 0b1011010110 ∧ (w / 2 ^ 16) % 32 = 0 ∧ (w / 2 ^ 10) % 64 = 2 then some "rev32"
    else if (w / 2 ^ 21) % 1024 = 0b1011010110 ∧ (w / 2 ^ 16) % 32 = 0 ∧ (w / 2 ^ 10) % 64 = 3 ∧
        (w / 2 ^ 31) % 2 = 1 then some "rev64"
    else if (w / 2 ^ 26) % 32 = 0b00101 then some "b"
    else if (w / 2 ^ 24) % 256 = 0b01010100 ∧ (w / 2 ^ 4) % 2 = 0 then some "bcond"
    else if (w / 2 ^ 25) % 64 = 0b011010 then some "cb"
    else if (w / 2 ^ 25) % 64 = 0b011011 then some "tb"
    else if (w / 2 ^ 10) % 4194304 = 3508160 ∧ w % 32 = 0 then some "br"
    else if (w / 2 ^ 10) % 4194304 = 3510208 ∧ w % 32 = 0 then some "blr"
    else if (w / 2 ^ 10) % 4194304 = 3512256 ∧ w % 32 = 0 then some "ret"
    else none
  else none

/-- The proved scalar floating-point encoding class of `w` (the name of its `fpStepOK_<class>` theorem,
`JanusASL/Proofs/FP/Run.lean`), if any. Like `classify`, the conditions are the theorems' hypotheses
verbatim. -/
def fpClassify (w : Nat) : Option String :=
  if w < 2 ^ 32 then
    if w / 2 ^ 24 = 0x1E ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 10) % 16 = 8 ∧
        (w / 2 ^ 14) % 4 = 0 ∧ w % 8 = 0 ∧ ((w / 2 ^ 3) % 2 = 1 → (w / 2 ^ 16) % 32 = 0) then some "fcmp"
    else if w / 2 ^ 24 = 0x1E ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 10) % 4 = 2 ∧
        (w / 2 ^ 12) % 16 = 0 then some "fmul"
    else if w / 2 ^ 24 = 0x1E ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 10) % 4 = 2 ∧
        (w / 2 ^ 12) % 16 = 1 then some "fdiv"
    else if w / 2 ^ 24 = 0x1E ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 10) % 4 = 2 ∧
        (w / 2 ^ 12) % 16 = 2 then some "fadd"
    else if w / 2 ^ 24 = 0x1E ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 10) % 4 = 2 ∧
        (w / 2 ^ 12) % 16 = 3 then some "fsub"
    else if w / 2 ^ 24 = 0x1F ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 0 ∧ (w / 2 ^ 15) % 2 = 0 then some "fmadd"
    else if w / 2 ^ 24 = 0x1F ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 0 ∧ (w / 2 ^ 15) % 2 = 1 then some "fmsub"
    else if w / 2 ^ 24 = 0x1F ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 15) % 2 = 0 then some "fnmadd"
    else if w / 2 ^ 24 = 0x1F ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 15) % 2 = 1 then some "fnmsub"
    else if w / 2 ^ 24 = 0x1E ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 10) % 32 = 16 ∧
        (w / 2 ^ 15) % 64 = 3 then some "fsqrt"
    else if w / 2 ^ 24 = 0x1E ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 10) % 4 = 1 then some "fccmp"
    else if w / 2 ^ 24 = 0x1E ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧ (w / 2 ^ 10) % 32 = 16 ∧
        (((w / 2 ^ 15) % 64 = 4 ∧ (w / 2 ^ 22) % 4 = 1) ∨ ((w / 2 ^ 15) % 64 = 5 ∧ (w / 2 ^ 22) % 4 = 0)) then
      some "fcvt"
    else if (w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E) ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧
        (w / 2 ^ 10) % 64 = 0 ∧ (w / 2 ^ 16) % 8 = 2 ∧ (w / 2 ^ 19) % 4 = 0 then some "scvtf"
    else if (w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E) ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧
        (w / 2 ^ 10) % 64 = 0 ∧ (w / 2 ^ 16) % 8 = 3 ∧ (w / 2 ^ 19) % 4 = 0 then some "ucvtf"
    else if (w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E) ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧
        (w / 2 ^ 10) % 64 = 0 ∧ (w / 2 ^ 16) % 8 = 0 ∧ (w / 2 ^ 19) % 4 = 3 then some "fcvtzs"
    else if (w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E) ∧ (w / 2 ^ 22) % 4 < 2 ∧ (w / 2 ^ 21) % 2 = 1 ∧
        (w / 2 ^ 10) % 64 = 0 ∧ (w / 2 ^ 16) % 8 = 1 ∧ (w / 2 ^ 19) % 4 = 3 then some "fcvtzu"
    else none
  else none

/-- Every word of `p` is in the proved subset, and its code and stubs are untagged. -/
def covered (p : Program) : Bool :=
  p.segments.all (fun seg => decide (seg.base + 4 * seg.words.length < 2 ^ 56) &&
      seg.words.all (fun w => (classify w).isSome)) &&
    p.stubs.all (fun st => decide (st.addr < 2 ^ 56))

/-- The Arm A64 top-level encoding group of `w` (bits 28:25), for the report. -/
def armGroup (w : Nat) : String :=
  let op0 := (w / 2 ^ 25) % 16
  if op0 / 2 == 4 then "data processing (immediate)"
  else if op0 / 2 == 5 then "branches, exception generation and system"
  else if op0 % 2 == 0 && (op0 / 4) % 2 == 1 then "loads and stores"
  else if op0 % 8 == 5 then "data processing (register)"
  else if op0 % 8 == 7 then "data processing (SIMD and FP)"
  else "reserved, SME, SVE or unallocated"

/-- What Janus decodes `w` to (constructor only), for the report. -/
def janusName (w : Nat) : String :=
  match Janus.Arm64.decode w with
  | some i => ((toString (repr i)).splitOn " ").headD "?"
  | none => "undecodable"

/-- One line per problem with `p`: words outside the proved subset (address, word, Arm group,
Janus instruction), tagged code and tagged stubs. Empty iff `covered p`. -/
def problems (p : Program) : List String := Id.run do
  let mut out := []
  for seg in p.segments do
    if ¬ (seg.base + 4 * seg.words.length < 2 ^ 56) then
      out := out ++ [s!"code {seg.name} at {seg.base} reaches the tagged range (>= 2^56)"]
    let mut i := 0
    for w in seg.words do
      if (classify w).isNone then
        out := out ++ [s!"word 0x{String.ofList (Nat.toDigits 16 w)} at 0x{String.ofList (Nat.toDigits 16 (seg.base + 4 * i))} ({seg.name}): {janusName w}, {armGroup w}"]
      i := i + 1
  for st in p.stubs do
    if ¬ (st.addr < 2 ^ 56) then
      out := out ++ [s!"stub {st.name} at {st.addr} is in the tagged range (>= 2^56)"]
  return out

/-- How many words of `p` fall in each proved class, in order of first appearance. -/
def classCounts (p : Program) : List (String × Nat) := Id.run do
  let mut out : List (String × Nat) := []
  for seg in p.segments do
    for w in seg.words do
      if let some c := classify w then
        if out.any (·.1 == c) then out := out.map fun (d, n) => if d == c then (d, n + 1) else (d, n)
        else out := out ++ [(c, 1)]
  return out

/-- Print the report with a marker, for `janus verify --asl`. -/
def report (marker : String) (p : Program) : IO Unit := do
  let ps := problems p
  for l in ps do IO.println s!"{marker}uncovered {l}"
  for (c, n) in classCounts p do IO.println s!"{marker}class {c} {n}"
  let n := p.segments.foldl (fun n s => n + s.words.length) 0
  IO.println s!"{marker}summary {n} {ps.length}"

end JanusASL.Classify
