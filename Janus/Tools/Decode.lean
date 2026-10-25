import Janus.Arm64.Decode
import Janus.Amd64.Decode

/-!
# `janus-decode`: run the trusted Lean decoder over instruction words

Reads one 32-bit instruction word per line on stdin (hexadecimal with a `0x` prefix, or
decimal; blank lines are skipped) and prints one line per word:

```text
0x8b010000 ok Janus.Arm64.Instr.addSubShifted true false false (Janus.Arm64.ShiftType.lsl) 1 0 0 0
0x4e083c00 none
```

`ok` means `Janus.Arm64.decodeAll` (the decoder of `step`) accepts the word (the rest of the line is the decoded `Instr`);
`none` means the model rejects it, so executing it faults with `undecodable`. A line that is not
a word prints `error <reason>` and the tool exits with status 1 at the end. `janus blockers`
drives this tool.

A line `x86 <hex bytes>` (an even number of hexadecimal digits, at most 15 bytes: the bytes
from an instruction's address to the end of its function, as `Janus.Amd64.Program.fetch`
returns them) runs `Janus.Amd64.decode` instead and prints `x86 <hex bytes> ok <length> <Instr>`
or `x86 <hex bytes> none`.
-/

namespace JanusDecode

open Janus.Arm64

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseWord (s : String) : Option Nat :=
  if s.startsWith "0x" || s.startsWith "0X" then
    let t := (s.drop 2).toString
    if t.isEmpty then none else
    t.foldl (fun acc c => acc.bind fun a => (hexDigit? c).map (a * 16 + ·)) (some 0)
  else s.toNat?

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- Hexadecimal digit pairs as bytes. -/
def parseBytes (s : String) : Option (List Nat) :=
  let cs := s.toList
  if cs.length % 2 ≠ 0 then none else
  let rec go : List Char → Option (List Nat)
    | [] => some []
    | a :: b :: rest => do
      let x ← hexDigit? a
      let y ← hexDigit? b
      let r ← go rest
      pure ((x * 16 + y) :: r)
    | [_] => none
  go cs

/-- An amd64 query line `x86 <hex bytes>`. -/
def handleX86 (hexs : String) : String × Bool :=
  match parseBytes hexs with
  | none => (s!"error cannot parse x86 bytes {hexs.quote}", true)
  | some bs =>
    if bs.isEmpty || bs.length > 15 then (s!"error x86 query of {bs.length} bytes", true) else
    match Janus.Amd64.decode bs with
    | some (i, len) => (s!"x86 {hexs} ok {len} {(repr i).pretty 100000}", false)
    | none => (s!"x86 {hexs} none", false)

/-- One output line for one input line, and whether the input was malformed. -/
def handle (line : String) : String × Bool :=
  if line.startsWith "x86 " then handleX86 (line.drop 4).toString.trimAscii.toString else
  match parseWord line with
  | none => (s!"error cannot parse {line.quote}", true)
  | some w =>
    if w ≥ 2 ^ 32 then (s!"error {hex w} is not a 32-bit word", true) else
    match decodeAll w with
    | some i => (s!"{hex w} ok {(repr i).pretty 100000}", false)
    | none => (s!"{hex w} none", false)

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (bad : Bool) : IO Bool := do
  let line ← stdin.getLine
  if line.isEmpty then return bad
  let t := line.trimAscii.toString
  if t.isEmpty then loop stdin stdout bad else
  let (out, err) := handle t
  stdout.putStrLn out
  loop stdin stdout (bad || err)

end JanusDecode

def main : IO UInt32 := do
  let bad ← JanusDecode.loop (← IO.getStdin) (← IO.getStdout) false
  (← IO.getStdout).flush
  return if bad then 1 else 0
