import Janus.Amd64
import Lean.Data.Json

/-!
# `janus-oracle-amd64`: run `Janus.Amd64.step` on differential-test cases

Reads one JSON test case per line on stdin (`oracle-amd64/layout/layout.go`, `Case`) and
prints one JSON result per line (`Model`):

* the initial `State` has the 16 GPRs, the six status flags (all defined), `XMM0`–`XMM15`,
  the upper halves of `YMM0`–`YMM15` (`ymmh`, default 0), the `FS` base (`fsbase`, default 0),
  `MXCSR` (`mxcsr`, default `0x1F80`) from the case and `rip = TestPC`;
* `mem.regions` is exactly the native runner's data buffer `[DataBase, DataBase + DataSize)`
  (writable), with bytes `pattern seed` overridden by the case's `init` entries; every other byte lies outside every region;
* the instruction bytes are those of the native code page: the case bytes at `TestPC`
  followed by `0xCC` up to the end of the page;
* the result is the fault, or the successor state: registers, `rip`, the status flags with the
  mask of the defined ones, the XMM registers, the upper YMM halves, `MXCSR` and the buffer bytes that
  differ from the initial pattern.

The constants below must match `oracle-amd64/layout/layout.go`.
-/

open Lean Janus.Amd64

namespace OracleAmd64

def codePage : Nat := 0x10_0000_0000
def testPC : Nat := codePage + 0x800
def dataBase : Nat := codePage + 0x4_0000
def dataSize : Nat := 4096
def pageSize : Nat := 4096

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

def parseBytes (s : String) : Except String (List Nat) := do
  let cs := s.toList
  if cs.length % 2 ≠ 0 then throw "odd byte string"
  let rec go : List Char → Except String (List Nat)
    | a :: b :: rest => do
      let some x := hexDigit? a | throw "bad byte"
      let some y := hexDigit? b | throw "bad byte"
      return (x * 16 + y) :: (← go rest)
    | _ => pure []
  go cs

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def faultJson : Fault → String × Json
  | .undecodable pc bs => ("undecodable", Json.mkObj [("pc", hex pc), ("bytes", toJson bs)])
  | .noCode pc => ("noCode", Json.mkObj [("pc", hex pc)])
  | .outsideAllocation a n => ("outsideAllocation", Json.mkObj [("addr", hex a), ("size", n)])
  | .readOnly a n => ("readOnly", Json.mkObj [("addr", hex a), ("size", n)])
  | .undefinedFlag pc => ("undefinedFlag", Json.mkObj [("pc", hex pc)])
  | .undefinedResult pc => ("undefinedResult", Json.mkObj [("pc", hex pc)])
  | .divideError pc => ("divideError", Json.mkObj [("pc", hex pc)])
  | .misaligned a => ("misaligned", Json.mkObj [("addr", hex a)])
  | .badTarget t => ("badTarget", Json.mkObj [("target", hex t)])
  | .simdFPException pc => ("simdFPException", Json.mkObj [("pc", hex pc)])
  | .trap pc sig => ("trap", Json.mkObj [("pc", hex pc), ("signal", sig)])
  | .kernel pc => ("kernel", Json.mkObj [("pc", hex pc)])
  | .systemFlag pc => ("systemFlag", Json.mkObj [("pc", hex pc)])
  | .outOfFuel => ("outOfFuel", Json.null)

structure Case where
  id : Nat
  bytes : List Nat
  regs : Array Nat
  rflags : Nat
  xmm : Array Nat
  ymmh : Array Nat
  fsBase : Nat
  seed : Nat
  /-- buffer overrides `(offset, byte)` applied after the pattern, in order -/
  init : List (Nat × Nat)
  /-- `MXCSR` (absent: `0x1F80`, the Linux/Go default) -/
  mxcsr : Nat
  /-- audit/rt-model sequence mode: the instructions laid out one after another at `TestPC`
  (`bytes` is ignored when non-empty) -/
  seq : List (List Nat) := []

def parseCase (line : String) : Except String Case := do
  let j ← Json.parse line
  let id ← j.getObjValAs? Nat "id"
  let bytes ← parseBytes (← j.getObjValAs? String "bytes")
  let rs ← j.getObjValAs? (Array String) "regs"
  if rs.size ≠ 16 then throw "regs must have 16 entries"
  let regs ← rs.mapM parseHex
  let rflags ← j.getObjValAs? Nat "rflags"
  let xs ← j.getObjValAs? (Array String) "xmm"
  if xs.size ≠ 16 then throw "xmm must have 16 entries"
  let xmm ← xs.mapM parseHex
  let ys : Array String := (j.getObjValAs? (Array String) "ymmh").toOption.getD #[]
  if ys.size ≠ 0 ∧ ys.size ≠ 16 then throw "ymmh must have 16 entries"
  let ymmh ← ys.mapM parseHex
  let fsBase ← match (j.getObjValAs? String "fsbase").toOption with
    | some f => parseHex f
    | none => pure 0
  let seed ← j.getObjValAs? Nat "seed"
  let init : Array (Array Nat) := (j.getObjValAs? (Array (Array Nat)) "init").toOption.getD #[]
  let init ← init.toList.mapM fun a =>
    if a.size = 2 ∧ a[0]! < dataSize ∧ a[1]! < 256 then pure (a[0]!, a[1]!) else throw "bad init entry"
  let mxcsr ← match (j.getObjValAs? String "mxcsr").toOption with
    | some m => parseHex m
    | none => pure 0x1F80
  if mxcsr ≥ 2 ^ 16 then throw "mxcsr: reserved bits set"
  let seqS : Array String := (j.getObjValAs? (Array String) "seq").toOption.getD #[]
  let seq ← seqS.toList.mapM parseBytes
  pure { id, bytes, regs, rflags, xmm, ymmh, fsBase, seed, init, mxcsr, seq }

/-- Initial byte at buffer offset `i`: the last override for `i`, else the pattern. -/
def initByte (c : Case) (i : Nat) : Nat :=
  c.init.foldl (fun acc (o, b) => if o = i then b else acc) (pattern c.seed i)

def bitSet (x i : Nat) : Bool := (x / 2 ^ i) % 2 = 1

def initState (c : Case) (initArr : Array Nat) : State :=
  { regs := fun i => if i < 16 then BitVec.ofNat 64 c.regs[i]! else 0
    rip := BitVec.ofNat 64 testPC
    flags := { cf := some (bitSet c.rflags 0), pf := some (bitSet c.rflags 2),
               af := some (bitSet c.rflags 4), zf := some (bitSet c.rflags 6),
               sf := some (bitSet c.rflags 7), ovf := some (bitSet c.rflags 11) }
    xmm := fun i => if i < 16 then BitVec.ofNat 128 c.xmm[i]! else 0
    ymmHi := fun i => if i < c.ymmh.size then BitVec.ofNat 128 c.ymmh[i]! else 0
    fsBase := BitVec.ofNat 64 c.fsBase
    df := bitSet c.rflags 10
    mxcsr := BitVec.ofNat 32 c.mxcsr
    mem :=
      { bytes := fun a =>
          if dataBase ≤ a ∧ a < dataBase + dataSize then BitVec.ofNat 8 (initArr[a - dataBase]!)
          else 0
        regions := [{ base := dataBase, size := dataSize, writable := true }] } }

/-- The code page bytes from `TestPC` on. -/
def codeBytes (c : Case) : List Nat :=
  let tail := pageSize - 0x800 - c.bytes.length
  (c.bytes ++ List.replicate tail 0xCC).take 15

def flagBits (f : Flags) : Nat × Nat :=
  let one (o : Option Bool) (bit : Nat) : Nat × Nat :=
    match o with
    | some true => (bit, bit)
    | some false => (0, bit)
    | none => (0, 0)
  let parts := [one f.cf 1, one f.pf 4, one f.af 16, one f.zf 64, one f.sf 128, one f.ovf 2048]
  (parts.foldl (· + ·.1) 0, parts.foldl (· + ·.2) 0)

/-- Sequence mode: the code page is the concatenated instructions followed by `0xCC`; `step`
is applied from `TestPC` until `rip` reaches the end of the sequence (or leaves it, or faults),
each time on the page bytes from `rip` (at most 15). -/
def runSeq (page : Array Nat) (stop : Nat) : Nat → State → Except Fault State
  | 0, s => .ok s
  | k + 1, s =>
    let r := s.rip.toNat
    if r = stop ∨ r < testPC ∨ r ≥ stop then .ok s else
    let off := r - codePage
    let bs := ((List.range 15).map fun i => page.getD (off + i) 0xCC)
    match Janus.Amd64.step bs s with
    | .error f => .error f
    | .ok s' => runSeq page stop k s'

def runCase (c : Case) : Json :=
  let bs := codeBytes c
  let len := match decode bs with | some (_, n) => n | none => 0
  let initArr := (List.range dataSize).toArray.map (initByte c)
  let flat := c.seq.foldr (· ++ ·) []
  let page : Array Nat := ((List.replicate 0x800 0xCC) ++ flat ++
    List.replicate (pageSize - 0x800 - flat.length) 0xCC).toArray
  let res := if c.seq.isEmpty then Janus.Amd64.step bs (initState c initArr)
    else runSeq page (testPC + flat.length) (4 * c.seq.length) (initState c initArr)
  match res with
  | .error f =>
    let (k, d) := faultJson f
    Json.mkObj [("id", c.id), ("status", "fault"), ("fault", k), ("detail", d), ("len", len),
      ("rflags", 0), ("defined", 0)]
  | .ok s =>
    let mem := (List.range dataSize).filterMap fun i =>
      let b := (s.mem.bytes (dataBase + i)).toNat
      if b ≠ initArr[i]! then some (Json.arr #[i, b]) else none
    let (fl, def_) := flagBits s.flags
    Json.mkObj [("id", c.id), ("status", "ok"), ("len", len), ("pc", hex s.rip.toNat),
      ("regs", Json.arr ((List.range 16).map fun i => Json.str (hex (s.regs i).toNat)).toArray),
      ("rflags", fl), ("defined", def_), ("df", s.df),
      ("xmm", Json.arr ((List.range 16).map fun i => Json.str (hex (s.xmm i).toNat)).toArray),
      ("ymmh", Json.arr ((List.range 16).map fun i => Json.str (hex (s.ymmHi i).toNat)).toArray),
      ("mxcsr", hex s.mxcsr.toNat),
      ("mem", Json.arr mem.toArray)]

end OracleAmd64

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let l := line.trimAscii.toString
  if !l.isEmpty then
    match OracleAmd64.parseCase l with
    | .ok c => stdout.putStrLn (OracleAmd64.runCase c).compress
    | .error e => stdout.putStrLn (Json.mkObj [("status", "error"), ("error", e)]).compress
  stdout.flush
  loop stdin stdout

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println "usage: janus-oracle-amd64 < cases.jsonl > model.jsonl"
    return 0
  loop (← IO.getStdin) (← IO.getStdout)
  return 0
