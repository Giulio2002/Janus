/-
Lean side of the rt-print differential test (audit/rt-print/run.sh).

Reads the case list written by audit/rt-print/gen (one case per line, see gen/main.go) and
writes to stdout the bytes the Go runtime's builtin print must have written to stderr, computed
with the spec functions of Janus.Spec.Print only.

  lean --run audit/rt-print/Diff.lean CASES     (or compiled, as run.sh does)
-/
import Janus.Spec.Print

open Janus.Spec.Print

namespace RtPrint

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def parseHex (s : String) : Nat := s.foldl (fun n c => 16 * n + hexVal c) 0

def bv64 (s : String) : BitVec 64 := BitVec.ofNat 64 (parseHex s)
def bv32 (s : String) : BitVec 32 := BitVec.ofNat 32 (parseHex s)

/-- A hex-encoded UTF-8 string ("-" is the empty string). -/
def parseStr (s : String) : String :=
  if s = "-" then ""
  else
    let cs := s.toList
    let rec go : List Char → Array UInt8 → Array UInt8
      | a :: b :: rest, acc => go rest (acc.push (16 * hexVal a + hexVal b).toUInt8)
      | _, acc => acc
    String.fromUTF8! ⟨go cs #[]⟩

/-- `println(id, xs…)`: operands separated by `printsp`, then `printnl`. -/
def println (id : Nat) (xs : List (List (BitVec 8))) : List (BitVec 8) :=
  fmtInt (BitVec.ofNat 64 id) ++ (xs.map (fmtSp ++ ·)).flatten ++ fmtNl

/-- The expected output line of case `id`. -/
def expect (id : Nat) (line : String) : Except String (List (BitVec 8)) :=
  match line.splitOn " " with
  | ["u", v] => pure (println id [fmtUint (bv64 v)])
  | ["i", v] => pure (println id [fmtInt (bv64 v)])
  | ["b", v] => pure (println id [fmtBool (parseHex v ≠ 0)])
  | ["h", v] => pure (println id [fmtUint (bv64 v)])  -- uintptr: printuint
  | ["p", v] => pure (println id [fmtPointer (bv64 v)])
  | ["d", v] => pure (println id [fmtF64 (bv64 v)])
  | ["f", v] => pure (println id [fmtF32 (bv32 v)])
  | ["c", re, im] => pure (println id [fmtC128 (bv64 re) (bv64 im)])
  | ["k", re, im] => pure (println id [fmtC64 (bv32 re) (bv32 im)])
  | ["s", s] => pure (println id [ofString (parseStr s)])
  | ["l", p, l, c] => pure (println id [fmtSlice (bv64 p) (bv64 l) (bv64 c)])
  | ["e", t, d] => pure (println id [fmtEface (bv64 t) (bv64 d)])
  | ["I", t, d] => pure (println id [fmtEface (bv64 t) (bv64 d)])
  | ["M", i, f, b, s] =>
    pure (println id [fmtInt (bv64 i), fmtF64 (bv64 f), fmtBool (parseHex b ≠ 0),
      ofString (parseStr s)])
  | ["P", f, g] =>
    -- print(id, "\t", f64, f32, "\n"): no separators
    pure (fmtInt (BitVec.ofNat 64 id) ++ ofString "\t" ++ fmtF64 (bv64 f) ++ fmtF32 (bv32 g) ++
      fmtNl)
  | _ => throw s!"case {id}: cannot parse {line.quote}"

def toBytes (acc : ByteArray) (l : List (BitVec 8)) : ByteArray :=
  l.foldl (fun a b => a.push b.toNat.toUInt8) acc

end RtPrint

open RtPrint in
def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: Diff CASES"; return 2
  let stdout ← IO.getStdout
  let h ← IO.FS.Handle.mk path .read
  let mut id := 0
  let mut buf := ByteArray.empty
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    match expect id line.trimAsciiEnd.toString with
    | .ok bs => buf := toBytes buf bs
    | .error e => IO.eprintln e; return 1
    id := id + 1
    if buf.size ≥ 1 <<< 20 then
      stdout.write buf
      buf := ByteArray.empty
  stdout.write buf
  stdout.flush
  return 0
