import X86Sail
import Janus
import JanusX86.Proofs.Config
import Lean.Data.Json

/-!
# `janus-x86-check`: Janus `Amd64.step` against the Sail x86 model, both in compiled Lean

For every case of the amd64 oracle corpus (`artifacts/oracle-amd64/cases.jsonl`, format of
`oracle-amd64/layout/layout.go`), run

* the **Sail side**: `X86Sail.Functions.janus_x86_step` (rems-project/sail-x86-from-acl2, the
  Sail translation of ACL2 X86isa, sliced to the opcodes Janus decodes and translated to Lean
  by Sail's Lean backend, `JanusX86/sail/`), from `janus_x86_init` (64-bit mode, CPL 3,
  application-level memory view), with the code page and the data buffer in the Sail memory,
  **twice**: with the model's undefined-value source returning 0 and 1 (a flag or register that
  differs between the two runs is undefined in the model, as in `oracle-amd64-formal/compare.py`);
* the **Janus side**: `Janus.Amd64.step` from the state `Oracle/Amd64Main.lean` builds,

and compare. This is a *test* (compiled evaluation), not a proof. See `docs/X86FORMAL.md`.

Verdicts:

* `agree`: both complete with equal GPRs, RIP, DF, YMM0-15 (bits 255:0), data-buffer bytes and
  every status flag Janus defines (which must also be defined, i.e. equal in both runs, in the
  model), and no other byte of the Sail memory changed; or both reject the instruction (Janus
  `undecodable`, the model a fault such as `#UD`); or both fault on the same condition (`#DE`,
  an access outside the mapped bytes, a misaligned SSE operand).
* `gap`: one side refuses where the other has a result: Janus faults conservatively, the model
  does not implement the instruction ("Opcode Unimplemented in x86isa", untranslated opcodes,
  every VEX instruction), or the instruction is outside the Janus subset.
* `sail-defect`: the results differ, and the **hardware** (`hw.jsonl`, the native oracle's
  single-stepped run of the same case) agrees with Janus on every compared field. Each such case
  is assigned a defect class (`defectClass`); docs/X86FORMAL.md lists them with evidence. These
  classes are excluded from agreement claims.
* `MISMATCH`: anything else: the results differ and the hardware does not side with Janus (or
  there is no hardware record), or an instruction Janus decodes reaches an arm the slice
  excluded. The exit code is 1 if there is any.

`--config` checks `X86Config` (`JanusX86.Proofs.cfgOk`, the assumption of the class theorems) on
the base state and on every case's pre- and post-states, and the checker reports violations.
-/

open Lean
open X86Sail X86Sail.Functions

namespace JanusX86.Check

/-! ## Layout (`oracle-amd64/layout/layout.go`) -/

def codePage : Nat := 0x10_0000_0000
def testPC : Nat := codePage + 0x800
def dataBase : Nat := codePage + 0x4_0000
def dataSize : Nat := 4096
def pageSize : Nat := 4096

def pattern (seed i : Nat) : Nat := (i * 157 + seed * 89 + (i / 256) * 41 + 7) % 256

/-! ## Case parsing (as `Oracle/Amd64Main.lean`) -/

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

structure Case where
  id : Nat
  cls : String
  bytesHex : String
  bytes : List Nat
  regs : Array Nat
  rflags : Nat
  xmm : Array Nat
  ymmh : Array Nat
  fsBase : Nat
  seed : Nat
  init : List (Nat × Nat)

def parseCase (line : String) : Except String Case := do
  let j ← Json.parse line
  let id ← j.getObjValAs? Nat "id"
  let cls := (j.getObjValAs? String "class").toOption.getD ""
  let bytesHex ← j.getObjValAs? String "bytes"
  let bytes ← parseBytes bytesHex
  let rs ← j.getObjValAs? (Array String) "regs"
  if rs.size ≠ 16 then throw "regs must have 16 entries"
  let regs ← rs.mapM parseHex
  let rflags ← j.getObjValAs? Nat "rflags"
  let xs ← j.getObjValAs? (Array String) "xmm"
  if xs.size ≠ 16 then throw "xmm must have 16 entries"
  let xmm ← xs.mapM parseHex
  let ys : Array String := (j.getObjValAs? (Array String) "ymmh").toOption.getD #[]
  if ys.size ≠ 0 ∧ ys.size ≠ 16 then throw "ymmh must have 16 entries"
  let ymmh ← if ys.size = 0 then pure (Array.replicate 16 0) else ys.mapM parseHex
  let fsBase ← match (j.getObjValAs? String "fsbase").toOption with
    | some f => parseHex f
    | none => pure 0
  let seed ← j.getObjValAs? Nat "seed"
  let init : Array (Array Nat) := (j.getObjValAs? (Array (Array Nat)) "init").toOption.getD #[]
  let init ← init.toList.mapM fun a =>
    if a.size = 2 ∧ a[0]! < dataSize ∧ a[1]! < 256 then pure (a[0]!, a[1]!) else throw "bad init entry"
  pure { id, cls, bytesHex, bytes, regs, rflags, xmm, ymmh, fsBase, seed, init }

def initByte (c : Case) (i : Nat) : Nat :=
  c.init.foldl (fun acc (o, b) => if o = i then b else acc) (pattern c.seed i)

def bitSet (x i : Nat) : Bool := (x / 2 ^ i) % 2 = 1

/-- The code page from `testPC` on: the case bytes, then `INT3` (`0xCC`) to the page end. -/
def codeTail (c : Case) : List Nat :=
  c.bytes ++ List.replicate (pageSize - 0x800 - c.bytes.length) 0xCC

/-! ## The Sail side -/

abbrev SState := Sail.ConcurrencyInterfaceV1.SequentialState RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource

def emptyState : SState :=
  { regs := ∅, choiceState := (), mem := ∅, tags := (), cycleCount := 0, sailOutput := #[] }

/-- `none` with an error text, or the value and the state. Errors are lean-sail errors that are
not Sail exceptions: a read of an address outside the Sail memory (`OutOfMemoryRange`), a
failed assertion, ... -/
def runM (m : SailM α) (s : SState) : Except String (α × SState) :=
  match m.run s with
  | .ok a s => .ok (a, s)
  | .error e _ => .error (match e with
      | .User _ => "uncaught Sail exception"
      | e => e.print)

/-- The registers after `sail_model_init` (declared initial values, `initialize_registers`) and
`janus_x86_init`; empty memory. -/
def baseState : Except String SState := do
  let ((), s) ← runM (sail_model_init ()) emptyState
  let ((), s) ← runM (janus_x86_init ()) s
  pure s

structure SailOk where
  regs : Array Nat
  rip : Nat
  rflags : Nat
  ymm : Array Nat
  mem : List (Nat × Nat)
  /-- addresses outside the data buffer whose Sail memory byte changed (or appeared) -/
  stray : List Nat
deriving BEq

inductive SailResult where
  | ok (r : SailOk)
  | fault (msg : String)
  | error (msg : String)
  /-- a lean-sail error: memory outside the mapped bytes (`OutOfMemoryRange`), assertion, ... -/
  | leanErr (msg : String)

def SailResult.tag : SailResult → String
  | .ok _ => "ok"
  | .fault m => s!"fault {m}"
  | .error m => s!"error {m}"
  | .leanErr m => s!"lean-error {m}"

def statusMask : Nat := 0x8D5   -- CF PF AF ZF SF OF

/-- The pre-state of a case: registers, flags (status flags, DF, and the reserved bit 1), RIP,
YMM0-15, FS base, code page and data buffer. -/
def preState (base : SState) (c : Case) : Except String SState := do
  let mem0 := (List.range dataSize).foldl
    (fun m i => m.insert (dataBase + i) (BitVec.ofNat 8 (initByte c i))) base.mem
  let mem0 := (List.range 0x800).foldl (fun m i => m.insert (codePage + i) (0xCC#8)) mem0
  let mem0 := (codeTail c).zipIdx.foldl (fun m (b, i) => m.insert (testPC + i) (BitVec.ofNat 8 b)) mem0
  let s0 : SState := { base with mem := mem0 }
  let setup : SailM Unit := do
    for i in [0:16] do
      janus_set_gpr (BitVec.ofNat 4 i) (BitVec.ofNat 64 c.regs[i]!)
    janus_set_rflags (BitVec.ofNat 32 ((c.rflags &&& (statusMask ||| 0x400)) ||| 2))
    janus_set_rip (BitVec.ofNat 64 testPC)
    for i in [0:16] do
      janus_set_ymm (BitVec.ofNat 4 i) (BitVec.ofNat 256 (c.ymmh[i]! * 2 ^ 128 + c.xmm[i]!))
    janus_set_fsbase (BitVec.ofNat 64 c.fsBase)
  let ((), s1) ← runM setup s0
  pure s1

def runSail (pre : SState) (undef : Nat) : SailResult × Option SState := Id.run do
  let s1 := match runM (janus_set_undef undef) pre with
    | .ok ((), s) => s
    | .error _ => pre
  match runM (janus_x86_step ()) s1 with
  | .error e => return (.leanErr e, none)
  | .ok (r, s2) =>
  match r with
  | .Janus_Fault =>
    match runM (readReg Register.__janus_msg) s2 with
    | .ok (m, _) => return (.fault m, some s2)
    | .error e => return (.leanErr e, some s2)
  | .Janus_Error =>
    match runM (readReg Register.__janus_msg) s2 with
    | .ok (m, _) => return (.error m, some s2)
    | .error e => return (.leanErr e, some s2)
  | .Janus_OK =>
    let readBack : SailM (Array Nat × Nat × Nat × Array Nat) := do
      let mut rs := #[]
      for i in [0:16] do
        rs := rs.push (← janus_get_gpr (BitVec.ofNat 4 i)).toNat
      let mut ys := #[]
      for i in [0:16] do
        ys := ys.push (← janus_get_ymm (BitVec.ofNat 4 i)).toNat
      pure (rs, (← janus_get_rip ()).toNat, (← janus_get_rflags ()).toNat, ys)
    match runM readBack s2 with
    | .error e => return (.leanErr s!"readback: {e}", some s2)
    | .ok ((rs, rip, fl, ys), _) =>
      let mem := (List.range dataSize).filterMap fun i =>
        let b := (s2.mem.getD (dataBase + i) 0).toNat
        if b ≠ (pre.mem.getD (dataBase + i) 0).toNat then some (i, b) else none
      let stray := (List.range pageSize).filterMap fun i =>
        if s2.mem.get? (codePage + i) = pre.mem.get? (codePage + i) then none else some (codePage + i)
      let stray := if s2.mem.size = pre.mem.size then stray else stray ++ [0]
      return (.ok { regs := rs, rip, rflags := fl, ymm := ys, mem, stray }, some s2)

/-! ## The Janus side (as `Oracle/Amd64Main.lean`) -/

open Janus.Amd64 in
def janusInit (c : Case) (initArr : Array Nat) : State :=
  { regs := fun i => if i < 16 then BitVec.ofNat 64 c.regs[i]! else 0
    rip := BitVec.ofNat 64 testPC
    flags := { cf := some (bitSet c.rflags 0), pf := some (bitSet c.rflags 2),
               af := some (bitSet c.rflags 4), zf := some (bitSet c.rflags 6),
               sf := some (bitSet c.rflags 7), ovf := some (bitSet c.rflags 11) }
    xmm := fun i => if i < 16 then BitVec.ofNat 128 c.xmm[i]! else 0
    ymmHi := fun i => if i < 16 then BitVec.ofNat 128 c.ymmh[i]! else 0
    fsBase := BitVec.ofNat 64 c.fsBase
    df := bitSet c.rflags 10
    mem :=
      { bytes := fun a =>
          if dataBase ≤ a ∧ a < dataBase + dataSize then BitVec.ofNat 8 (initArr[a - dataBase]!)
          else 0
        regions := [{ base := dataBase, size := dataSize, writable := true }] } }

/-- `(value, defined mask)` of the six status flags. -/
def flagBits (f : Janus.Amd64.Flags) : Nat × Nat :=
  let one (o : Option Bool) (bit : Nat) : Nat × Nat :=
    match o with
    | some true => (bit, bit)
    | some false => (0, bit)
    | none => (0, 0)
  let parts := [one f.cf 1, one f.pf 4, one f.af 16, one f.zf 64, one f.sf 128, one f.ovf 2048]
  (parts.foldl (· + ·.1) 0, parts.foldl (· + ·.2) 0)

structure JanusOk where
  regs : Array Nat
  rip : Nat
  flags : Nat
  defined : Nat
  df : Bool
  ymm : Array Nat
  mem : List (Nat × Nat)

def janusOk (s : Janus.Amd64.State) (initArr : Array Nat) : JanusOk :=
  let (fl, d) := flagBits s.flags
  { regs := (List.range 16).toArray.map fun i => (s.regs i).toNat
    rip := s.rip.toNat, flags := fl, defined := d, df := s.df
    ymm := (List.range 16).toArray.map fun i => (s.ymmHi i).toNat * 2 ^ 128 + (s.xmm i).toNat
    mem := (List.range dataSize).filterMap fun i =>
      let b := (s.mem.bytes (dataBase + i)).toNat
      if b ≠ initArr[i]! then some (i, b) else none }

/-! ## Hardware records (`hw.jsonl`) -/

structure Hw where
  status : String
  pc : Nat
  regs : Array Nat
  rflags : Nat
  df : Bool
  xmm : Array Nat
  ymmh : Array Nat
  mem : List (Nat × Nat)

def parseHw (line : String) : Except String Hw := do
  let j ← Json.parse line
  let status ← j.getObjValAs? String "status"
  let pc ← match (j.getObjValAs? String "pc").toOption with
    | some p => parseHex p
    | none => pure 0
  let regs ← ((j.getObjValAs? (Array String) "regs").toOption.getD #[]).mapM parseHex
  let rflags := (j.getObjValAs? Nat "rflags").toOption.getD 0
  let df := (j.getObjValAs? Bool "df").toOption.getD false
  let xmm ← ((j.getObjValAs? (Array String) "xmm").toOption.getD #[]).mapM parseHex
  let ymmh ← ((j.getObjValAs? (Array String) "ymmh").toOption.getD #[]).mapM parseHex
  let mem : Array (Array Nat) := (j.getObjValAs? (Array (Array Nat)) "mem").toOption.getD #[]
  pure { status, pc, regs, rflags, df, xmm, ymmh, mem := mem.toList.map fun a => (a[0]!, a[1]!) }

/-- Janus' result equals the hardware's on every field the native oracle compares (GPRs, RIP,
the flags Janus defines, DF, XMM, the upper YMM halves when recorded, the data buffer). -/
def janusEqHw (j : JanusOk) (h : Hw) : Bool :=
  h.status == "ok" && h.regs.size == 16 && h.regs == j.regs && h.pc == j.rip &&
  (h.rflags &&& j.defined) == j.flags && h.df == j.df &&
  (h.xmm.size != 16 || h.xmm == j.ymm.map (· % 2 ^ 128)) &&
  (h.ymmh.size != 16 || h.ymmh == j.ymm.map (· / 2 ^ 128)) &&
  h.mem == j.mem

/-! ## Known Sail-x86 defects -/

/-- The defect class of a case whose Sail result differs from Janus' (and the hardware sides with
Janus); docs/X86FORMAL.md, "Known defects of the Sail x86 model". -/
def defectClass (c : Case) (i : Janus.Amd64.Instr) (why : String) : String :=
  -- the REX prefix of the instruction (if any): the byte right before the opcode
  let opIdx := c.bytes.findIdx fun b => !(b == 0x66 || b == 0xF2 || b == 0xF3 || b == 0xF0 ||
    b == 0x26 || b == 0x2E || b == 0x36 || b == 0x3E || b == 0x64 || (0x40 ≤ b && b < 0x50))
  let rexW := opIdx > 0 && (match c.bytes[opIdx - 1]? with
    | some b => 0x48 ≤ b && b < 0x50
    | none => false)
  match i with
  | .locked i _ _ => defectClass c i why
  | .cmpxchg .. => "D1 cmpxchg-flags-operand-order"
  | .alu _ 8 (.reg 0) (.imm _) => if rexW then "D2 rax-imm8-rexw" else "unclassified alu-al-imm8"
  | .test 8 (.reg 0) (.imm _) => if rexW then "D2 rax-imm8-rexw" else "unclassified test-al-imm8"
  | .shift op w _ cnt =>
    -- the masked count (5 bits; 6 for 64-bit operands)
    let raw := match cnt with
      | .imm v => v
      | _ => c.regs[1]! % 256
    let k := raw % (if w == 64 then 64 else 32)
    if (op == .rol || op == .ror) && (w == 8 || w == 16) && k ≥ w then "D3 rotate-8-16-count-ge-width"
    else if op == .ror && why.startsWith "flags" then "D6 ror-cf-from-bit-0"
    else s!"unclassified shift"
  | .movdq _ true _ _ => "D4 movd-movq-to-xmm-no-zero-extension"
  | .movq .. => "D4 movd-movq-to-xmm-no-zero-extension"
  | .movs true _ | .stos true _ => "D5 rep-string"
  | _ => s!"unclassified {why.takeWhile (· != ':')}"

/-! ## Comparison -/

inductive Verdict where
  | agree (kind : String)
  | gap (kind : String) (detail : String := "")
  | defect (cls : String) (why : String)
  | mismatch (why : String)

/-- Differences between Janus' completed step and the two Sail runs (`none` = agree). Flags:
every flag Janus defines must be equal in both runs (defined in the model) and equal to Janus'. -/
def diffOk (j : JanusOk) (s0 s1 : SailOk) : Option String :=
  let undefFlags := (s0.rflags ^^^ s1.rflags) &&& statusMask
  if j.regs != s0.regs then
    let i := (List.range 16).find? (fun i => j.regs[i]! != s0.regs[i]!) |>.getD 0
    some s!"reg {i}: janus {hex j.regs[i]!} sail {hex s0.regs[i]!}"
  else if s0.regs != s1.regs then some "sail result register undefined, janus defines it"
  else if j.rip != s0.rip then some s!"rip: janus {hex j.rip} sail {hex s0.rip}"
  else if undefFlags &&& j.defined != 0 then
    some s!"flags: undefined in sail, defined in janus (mask {hex (undefFlags &&& j.defined)})"
  else if (s0.rflags &&& j.defined) != j.flags then
    some s!"flags: janus {hex j.flags} sail {hex (s0.rflags &&& j.defined)} (mask {hex j.defined})"
  else if bitSet s0.rflags 10 != j.df then some "df"
  else if j.ymm != s0.ymm then
    let i := (List.range 16).find? (fun i => j.ymm[i]! != s0.ymm[i]!) |>.getD 0
    some s!"ymm{i}: janus {hex j.ymm[i]!} sail {hex s0.ymm[i]!}"
  else if s0.ymm != s1.ymm then some "sail ymm undefined"
  else if j.mem != s0.mem then some s!"memory: janus {j.mem.take 8} sail {s0.mem.take 8}"
  else if !s0.stray.isEmpty then some s!"sail wrote outside the data buffer: {s0.stray.take 4 |>.map hex}"
  else none

def isUnimplemented (m : String) : Bool :=
  (m.splitOn "Unimplemented").length > 1 || (m.splitOn "not translated").length > 1 ||
  (m.splitOn "janus-excluded: VEX").length > 1

def isExcluded (m : String) : Bool := (m.splitOn "janus-excluded").length > 1

def faultName (f : Janus.Amd64.Fault) : String :=
  ((repr f).pretty.takeWhile (· != ' ')).replace "Janus.Amd64.Fault." ""

open Janus.Amd64 in
def compare (c : Case) (hw : Option Hw) (s0 s1 : SailResult) : Verdict :=
  let initArr := (List.range dataSize).toArray.map (initByte c)
  let bs := (codeTail c).take 15
  let instr := (decode bs).map (·.1)
  match Janus.Amd64.step bs (janusInit c initArr), s0 with
  | .error (.undecodable _ _), .fault _ => .agree "both-reject"
  | .error (.undecodable _ _), .error m =>
    if isExcluded m then .gap "janus-undecodable/sail-excluded"
    else if isUnimplemented m then .gap "janus-undecodable/sail-unimplemented"
    else .gap s!"janus-undecodable/sail-error"
  | .error (.undecodable _ _), .ok _ => .gap "janus-undecodable/sail-ok"
  | .error (.undecodable _ _), .leanErr _ => .gap "janus-undecodable/sail-memory"
  | .ok js, _ =>
    let j := janusOk js initArr
    let candidate (why : String) : Verdict :=
      match hw with
      | some h => if janusEqHw j h then .defect (defectClass c (instr.getD .nop) why) why
        else .mismatch s!"{why} (hardware does not side with janus)"
      | none => .mismatch s!"{why} (no hardware record)"
    match s0, s1 with
    | .ok r0, .ok r1 =>
      match diffOk j r0 r1 with
      | none => .agree "ok"
      | some why => candidate why
    | .error m, _ =>
      if isUnimplemented m then .gap "sail-unimplemented"
      else if isExcluded m then .mismatch s!"janus decodes, the slice excludes it: {m}"
      else candidate s!"sail model error: {m}"
    | .fault m, _ => candidate s!"janus completes, sail faults: {m}"
    | .leanErr m, _ => candidate s!"janus completes, sail: {m}"
    | _, r => candidate s!"the two sail runs differ in outcome: {r.tag}"
  | .error (.outsideAllocation _ _), .leanErr m =>
    if (m.splitOn "Out of Memory").length > 1 || (m.splitOn "memory").length > 1 then .agree "both-unmapped"
    else .gap s!"outsideAllocation/sail-lean-error"
  | .error (.divideError _), .fault m =>
    if (m.splitOn "DE").length > 1 then .agree "divide-error" else .gap s!"divideError/sail-fault"
  -- the model signals #DE as a model error (`x86_model_error(":UNSIGNED-DIVIDE-ERROR-OVERFLOW")`, ...)
  | .error (.divideError _), .error m =>
    if (m.splitOn "DIVIDE-ERROR").length > 1 then .agree "divide-error" else .gap s!"divideError/sail-error"
  -- a non-canonical access: the model stops with a model error, Janus outside every region
  | .error (.outsideAllocation _ _), .error m =>
    if (m.splitOn "NON-CANONICAL").length > 1 then .agree "both-fault-non-canonical"
    else if isUnimplemented m then .gap "janus-outsideAllocation/sail-unimplemented"
    else .gap "janus-outsideAllocation/sail-error"
  -- a branch to a non-canonical target: #GP in the model, `badTarget` in Janus
  | .error (.badTarget _), .fault m =>
    if (m.splitOn ":GP").length > 1 then .agree "both-fault-bad-target" else .gap "janus-badTarget/sail-fault"
  | .error (.misaligned _), .fault _ => .agree "misaligned"
  | .error f, .error m =>
    if isUnimplemented m then .gap s!"janus-{faultName f}/sail-unimplemented"
    else .gap s!"janus-{faultName f}/sail-error"
  | .error f, r => .gap s!"janus-{faultName f}/sail-{(r.tag.takeWhile (· != ' '))}"

/-- `compare`, with the Sail outcome attached to every `gap` verdict. -/
def compareD (c : Case) (hw : Option Hw) (s0 s1 : SailResult) : Verdict :=
  match compare c hw s0 s1 with
  | .gap k _ => .gap k s0.tag
  | v => v

def verdictJson (c : Case) : Verdict → Json
  | .agree k => Json.mkObj [("id", c.id), ("class", c.cls), ("verdict", "agree"), ("kind", k)]
  | .gap k d => Json.mkObj [("id", c.id), ("class", c.cls), ("bytes", c.bytesHex), ("verdict", "gap"),
      ("kind", k), ("sail", d)]
  | .defect k w => Json.mkObj [("id", c.id), ("class", c.cls), ("bytes", c.bytesHex),
      ("verdict", "sail-defect"), ("defect", k), ("why", w)]
  | .mismatch w => Json.mkObj [("id", c.id), ("class", c.cls), ("bytes", c.bytesHex),
      ("verdict", "MISMATCH"), ("why", w)]

/-- One case: the verdict, and whether `X86Config` holds on the pre-state and on the
post-states of the completed Sail runs. -/
def runCase (base : SState) (hw : Option Hw) (c : Case) : Verdict × Bool :=
  match preState base c with
  | .error e => (.mismatch s!"sail setup: {e}", false)
  | .ok pre =>
    let (r0, t0) := runSail pre 0
    let (r1, t1) := runSail pre 1
    let post (t : Option SState) (r : SailResult) : Bool :=
      match r, t with
      | .ok _, some s => JanusX86.Proofs.cfgOk s
      | _, _ => true
    let cfg := JanusX86.Proofs.cfgOk pre && post t0 r0 && post t1 r1
    (compareD c hw r0 r1, cfg)

end JanusX86.Check

open JanusX86.Check in
def main (args : List String) : IO UInt32 := do
  let path := args.headD "artifacts/oracle-amd64/cases.jsonl"
  let hwPath := (args.drop 1).headD "artifacts/oracle-amd64/hw.jsonl"
  let out := (args.drop 2).headD "artifacts/x86formal/verdicts.jsonl"
  let jobs := ((args.drop 3).headD "48").toNat!
  let base ← match baseState with
    | .ok s => pure s
    | .error e => IO.eprintln s!"janus-x86-check: Sail initialisation failed: {e}"; return 2
  let lines := (← IO.FS.lines path).filter (·.trimAscii.toString != "")
  let cases ← lines.mapM fun l => match parseCase l with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"bad case: {e}")
  -- hardware records by case id, parsed on demand (only for differing cases)
  let hwLines ← if (← System.FilePath.pathExists hwPath) then IO.FS.lines hwPath else pure #[]
  let mut hwById : Std.HashMap Nat String := {}
  for l in hwLines do
    -- every record starts with `{"id":N,` (oracle-amd64/layout/layout.go field order)
    let fast := if l.startsWith "{\"id\":" then ((l.drop 6).takeWhile Char.isDigit).toString.toNat? else none
    match fast <|> (Json.parse l).toOption.bind (fun j => (j.getObjValAs? Nat "id").toOption) with
    | some id => hwById := hwById.insert id l
    | none => pure ()
  IO.eprintln s!"janus-x86-check: {cases.size} cases, {hwById.size} hardware records, {jobs} tasks"
  let chunk := (cases.size + jobs - 1) / jobs
  let tasks := (List.range jobs).map fun k =>
    Task.spawn (prio := .dedicated) fun _ =>
      (cases.extract (k * chunk) ((k + 1) * chunk)).map fun c =>
        let hw := (hwById.get? c.id).bind fun l => (parseHw l).toOption
        let (v, cfg) := runCase base hw c
        (c, v, cfg)
  let results := tasks.foldl (fun acc t => acc ++ t.get) #[]
  let baseCfg := JanusX86.Proofs.cfgOk base
  let cfgBad := (results.filter fun (_, _, cfg) => !cfg).size
  let mut agree := 0
  let mut gap := 0
  let mut defect := 0
  let mut mism := 0
  let mut kinds : Std.HashMap String Nat := {}
  let h ← IO.FS.Handle.mk out .write
  for (c, v, _) in results do
    h.putStrLn (verdictJson c v).compress
    let bump (k : String) (m : Std.HashMap String Nat) := m.insert k (m.getD k 0 + 1)
    match v with
    | .agree k => agree := agree + 1; kinds := bump ("agree " ++ k) kinds
    | .gap k _ => gap := gap + 1; kinds := bump ("gap " ++ k) kinds
    | .defect k _ => defect := defect + 1; kinds := bump ("sail-defect " ++ k) kinds
    | .mismatch _ => mism := mism + 1
  for (k, n) in kinds.toList.mergeSort (fun a b => a.2 ≥ b.2) do
    IO.println s!"{n}\t{k}"
  IO.println s!"cases {results.size}  agree {agree}  gap {gap}  sail-defect {defect}  MISMATCH {mism}"
  IO.println s!"X86Config: base {baseCfg}, cases violating it (pre- or post-state) {cfgBad}"
  return if mism = 0 && baseCfg && cfgBad = 0 then 0 else 1
