import Janus
import Lean.Data.Json

/-!
# `janus-oracle`: run `Janus.Arm64.step` on differential-test cases

Reads one JSON test case per line on stdin (the format written by `oracle gen`, see
`oracle/layout/layout.go` and `docs/ORACLE.md`) and prints one JSON result per line:

* the initial `State` has `X0..X30`, `SP`, `NZCV`, `pc` and `dczid` (the reference machine's
  DCZID_EL0, field `dczid`) from the case;
* `mem.regions` is exactly the native runner's data buffer `[DataBase, DataBase + DataSize)`
  (writable), and its bytes follow `pattern seed`; every other byte reads as 0 but lies
  outside every region, so any access to it must fault;
* the result is either the fault, or the successor state: registers, SP, NZCV, pc and the
  list of buffer bytes that differ from the initial pattern.

The constants below must match `oracle/layout/layout.go`.
-/

open Lean Janus Janus.Arm64

namespace Oracle

def dataBase : Nat := 0x10_0000_0000 + 0x4_0000
def dataSize : Nat := 4096
def testPC : Nat := 0x10_0000_0800

/-- Initial byte `i` of the data buffer (mirrors `layout.Pattern`). -/
def pattern (seed i : Nat) : Nat := (i * 157 + seed * 89 + (i / 256) * 41 + 7) % 256

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex (s : String) : Except String Nat := do
  let t := if s.startsWith "0x" || s.startsWith "0X" then s.drop 2 else s
  if t.isEmpty then throw s!"bad hex '{s}'"
  t.foldl (fun acc c => do
    let a ← acc
    match hexDigit? c with
    | some d => pure (a * 16 + d)
    | none => throw s!"bad hex '{s}'") (pure 0)

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def faultJson : Fault → String × Json
  | .undecodable pc w => ("undecodable", Json.mkObj [("pc", hex pc), ("word", hex w)])
  | .noCode pc => ("noCode", Json.mkObj [("pc", hex pc)])
  | .outsideAllocation a n => ("outsideAllocation", Json.mkObj [("addr", hex a), ("size", n)])
  | .readOnly a n => ("readOnly", Json.mkObj [("addr", hex a), ("size", n)])
  | .spMisaligned sp => ("spMisaligned", Json.mkObj [("sp", hex sp)])
  | .pcMisaligned pc => ("pcMisaligned", Json.mkObj [("pc", hex pc)])
  | .unaligned a n => ("unaligned", Json.mkObj [("addr", hex a), ("size", n)])
  | .trapped pc => ("trapped", Json.mkObj [("pc", hex pc)])
  | .outOfFuel => ("outOfFuel", Json.null)

structure Case where
  id : Nat
  word : Nat
  pc : Nat
  x : Array Nat
  sp : Nat
  nzcv : Nat
  seed : Nat
  /-- DCZID_EL0 of the reference machine (`State.dczid`). Absent in old corpora: `0x10`. -/
  dczid : Nat

def hexField (j : Json) (k : String) : Except String Nat := do
  parseHex (← j.getObjValAs? String k)

def parseCase (line : String) : Except String Case := do
  let j ← Json.parse line
  let id ← j.getObjValAs? Nat "id"
  let word ← hexField j "word"
  let pc ← (hexField j "pc" <|> pure testPC)
  let xs ← j.getObjValAs? (Array String) "x"
  if xs.size ≠ 31 then throw "x must have 31 entries"
  let x ← xs.mapM parseHex
  let sp ← hexField j "sp"
  let nzcv ← j.getObjValAs? Nat "nzcv"
  let seed ← j.getObjValAs? Nat "seed"
  let dczid ← (j.getObjValAs? Nat "dczid" <|> pure 0x10)
  pure { id, word, pc, x, sp, nzcv, seed, dczid }

def initState (c : Case) : State :=
  { regs := fun i => if i < 31 then BitVec.ofNat 64 c.x[i]! else 0
    sp := BitVec.ofNat 64 c.sp
    pc := BitVec.ofNat 64 c.pc
    flags := ⟨c.nzcv &&& 8 ≠ 0, c.nzcv &&& 4 ≠ 0, c.nzcv &&& 2 ≠ 0, c.nzcv &&& 1 ≠ 0⟩
    mem :=
      { bytes := fun a =>
          if dataBase ≤ a ∧ a < dataBase + dataSize then BitVec.ofNat 8 (pattern c.seed (a - dataBase))
          else 0
        regions := [{ base := dataBase, size := dataSize, writable := true }] }
    dczid := BitVec.ofNat 5 c.dczid }

def nzcvOf (f : Flags) : Nat :=
  (if f.n then 8 else 0) + (if f.z then 4 else 0) + (if f.c then 2 else 0) + (if f.v then 1 else 0)

def runCase (c : Case) : Json :=
  match Arm64.step c.word (initState c) with
  | .error f =>
    let (k, d) := faultJson f
    Json.mkObj [("id", c.id), ("status", "fault"), ("fault", k), ("detail", d)]
  | .ok s =>
    let mem := (List.range dataSize).filterMap fun i =>
      let b := (s.mem.bytes (dataBase + i)).toNat
      if b ≠ pattern c.seed i then some (Json.arr #[i, b]) else none
    Json.mkObj [("id", c.id), ("status", "ok"), ("pc", hex s.pc.toNat),
      ("x", Json.arr ((List.range 31).map fun i => Json.str (hex (s.regs i).toNat)).toArray),
      ("sp", hex s.sp.toNat), ("nzcv", nzcvOf s.flags),
      ("mem", Json.arr mem.toArray)]

end Oracle

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let l := line.trimAscii.toString
  if !l.isEmpty then
    match Oracle.parseCase l with
    | .ok c => stdout.putStrLn (Oracle.runCase c).compress
    | .error e => stdout.putStrLn (Json.mkObj [("status", "error"), ("error", e)]).compress
  loop stdin stdout

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println "usage: janus-oracle < cases.jsonl > model.jsonl"
    return 0
  loop (← IO.getStdin) (← IO.getStdout)
  return 0
