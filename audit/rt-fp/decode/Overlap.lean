import Janus.Arm64.Decode

/-!
Row DEC-A64 (docs/AUDIT-FP.md): no word is claimed by two decoders. Reads the words of a
`janus-decode` output file (argument 1) that `decodeAll` accepts and checks that `decode` and
`decodeNeon` do not both accept any of them (`decodeAll` tries `decode` first, so an overlap
would be a second, shadowed decoder for the same encoding). Prints the overlapping words and
`decoded by both: N`; exits 1 when `N > 0`.
-/
open Janus.Arm64

def hexWord (t : String) : Nat :=
  ((t.drop 2).toString).foldl (fun a c =>
    a * 16 + (if c ≤ '9' then c.toNat - 48 else if c ≤ 'F' then c.toNat - 55 else c.toNat - 87)) 0

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: Overlap.lean JANUS_DECODE_OUT"; return 2
  let s ← IO.FS.readFile path
  let mut n := 0
  let mut both := 0
  for l in s.splitOn "\n" do
    match l.splitOn " " with
    | w :: "ok" :: _ =>
      n := n + 1
      let x := hexWord w
      if (decode x).isSome && (decodeNeon x).isSome then
        both := both + 1
        if both ≤ 20 then IO.println s!"BOTH {w} {(repr (decode x)).pretty 1000} / {(repr (decodeNeon x)).pretty 1000}"
    | _ => pure ()
  IO.println s!"accepted words checked: {n}; decoded by both: {both}"
  return if both = 0 then 0 else 1
