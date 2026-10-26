import Janus.Amd64
import Lean.Data.Json

/-!
# `janus-oracle-amd64`: run `Janus.Amd64.step` on differential-test cases

Reads one JSON test case per line on stdin (`oracle-amd64/layout/layout.go`, `Case`) and
prints one JSON result per line (`Model`):

* the initial `State` has the 16 GPRs, the six status flags (all defined), `XMM0`–`XMM15`,
  the upper halves of `YMM0`–`YMM15` (`ymmh`, default 0), the AVX-512 state (`zmmh` bits
  511:256 of `ZMM0`–`ZMM15`, `zmmx` = `ZMM16`–`ZMM31`, `k` = `K0`–`K7`, default 0), the `FS` base (`fsbase`, default 0),
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
  | .fpuException pc => ("fpuException", Json.mkObj [("pc", hex pc)])
  | .fpuStack pc => ("fpuStack", Json.mkObj [("pc", hex pc)])
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
  /-- the x87 state (`x87`: FCW, FSW, abridged FTW, `ST(0)`..`ST(7)`), absent: after `FNINIT` -/
  x87 : Janus.Amd64.X87.St := {}
  /-- the x87 control word (`State.fpucw`, what `FNSTCW` reads back of the case's `fcw`) -/
  fcw : Nat := 0x37F
  /-- bits 511:256 of `ZMM0`–`ZMM15` (`zmmh`), `ZMM16`–`ZMM31` (`zmmx`), `K0`–`K7` (`k`); empty =
  all zero (AVX-512, WP-G) -/
  zmmh : Array Nat := #[]
  zmmx : Array Nat := #[]
  k : Array Nat := #[]

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
  let fcw ← match j.getObjVal? "x87" with
    | .ok x => do pure (Janus.Amd64.X87.normCW (← parseHex (← x.getObjValAs? String "fcw")))
    | .error _ => pure 0x37F
  let x87 ← match j.getObjVal? "x87" with
    | .ok x => do
      let fcw ← parseHex (← x.getObjValAs? String "fcw")
      let fsw ← parseHex (← x.getObjValAs? String "fsw")
      let ftw ← x.getObjValAs? Nat "ftw"
      let st ← (← x.getObjValAs? (Array String) "st").mapM parseHex
      if st.size ≠ 8 ∨ fcw ≥ 2 ^ 16 ∨ fsw ≥ 2 ^ 16 ∨ ftw ≥ 256 ∨ st.any (· ≥ 2 ^ 80) then
        throw "bad x87 state"
      let top := fsw / 0x800 % 8
      let bit (i : Nat) : Option Bool := some (fsw / 2 ^ i % 2 = 1)
      -- FXRSTOR loads the control word as given; the model keeps what FNSTCW reads back
      pure ({ regs := fun r => st[(r + 8 - top) % 8]!, top, tags := fun r => ftw / 2 ^ r % 2 = 1,
              sw := fsw % 256 + (fsw / 0x8000) * 0x8000,
              c0 := bit 8, c1 := bit 9, c2 := bit 10, c3 := bit 14 } : Janus.Amd64.X87.St)
    | .error _ => pure {}
  let opt (name : String) (n : Nat) : Except String (Array Nat) := do
    let a : Array String := (j.getObjValAs? (Array String) name).toOption.getD #[]
    if a.size ≠ 0 ∧ a.size ≠ n then throw s!"{name} must have {n} entries"
    a.mapM parseHex
  let zmmh ← opt "zmmh" 16
  let zmmx ← opt "zmmx" 16
  let k ← opt "k" 8
  pure { id, bytes, regs, rflags, xmm, ymmh, fsBase, seed, init, mxcsr, seq, x87, fcw, zmmh, zmmx, k }

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
    xmm := fun i => if i < 16 then BitVec.ofNat 128 c.xmm[i]!
      else if i < 32 ∧ i - 16 < c.zmmx.size then BitVec.ofNat 128 c.zmmx[i - 16]! else 0
    ymmHi := fun i => if i < c.ymmh.size then BitVec.ofNat 128 c.ymmh[i]!
      else if 16 ≤ i ∧ i < 32 ∧ i - 16 < c.zmmx.size then BitVec.ofNat 128 (c.zmmx[i - 16]! / 2 ^ 128) else 0
    zmmHi := fun i => if i < c.zmmh.size then BitVec.ofNat 256 c.zmmh[i]!
      else if 16 ≤ i ∧ i < 32 ∧ i - 16 < c.zmmx.size then BitVec.ofNat 256 (c.zmmx[i - 16]! / 2 ^ 256) else 0
    kreg := fun i => if i < c.k.size then BitVec.ofNat 64 c.k[i]! else 0
    fsBase := BitVec.ofNat 64 c.fsBase
    df := bitSet c.rflags 10
    mxcsr := BitVec.ofNat 32 c.mxcsr
    x87 := c.x87
    fpucw := BitVec.ofNat 16 c.fcw
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

/-- The x87 state in `FXSAVE` terms (`layout.X87State`); undefined condition codes read as 0
(`fswDefined` masks them out). -/
def x87Json (t : Janus.Amd64.X87.St) (cw : Nat) : Json :=
  let b (o : Option Bool) (v : Nat) : Nat := if o = some true then v else 0
  let fsw := t.sw % 256 + (if t.sw / 0x8000 % 2 = 1 then 0x8000 else 0) + b t.c0 0x100 +
    b t.c1 0x200 + b t.c2 0x400 + t.top % 8 * 0x800 + b t.c3 0x4000
  Json.mkObj [("fcw", hex cw), ("fsw", hex fsw), ("ftw", toJson ((List.range 8).foldl (fun acc r => acc + if t.tags r then 2 ^ r else 0) 0)),
    ("st", Json.arr ((List.range 8).map fun i => Json.str (hex (t.regs ((t.top + i) % 8) % 2 ^ 80))).toArray)]

/-- The `FSW` bits the model defines: all but the undefined condition codes. -/
def fswDefined (t : Janus.Amd64.X87.St) : Nat :=
  let u (o : Option Bool) (v : Nat) : Nat := if o.isSome then 0 else v
  0xFFFF - u t.c0 0x100 - u t.c1 0x200 - u t.c2 0x400 - u t.c3 0x4000

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
      ("x87", x87Json s.x87 s.fpucw.toNat), ("fswdef", toJson (fswDefined s.x87)),
      ("zmmh", Json.arr ((List.range 16).map fun i => Json.str (hex (s.zmmHi i).toNat)).toArray),
      ("zmmx", Json.arr ((List.range 16).map fun i => Json.str (hex (s.zmm (i + 16)))).toArray),
      ("k", Json.arr ((List.range 8).map fun i => Json.str (hex (s.kreg i).toNat)).toArray),
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
