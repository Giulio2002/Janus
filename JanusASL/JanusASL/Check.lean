import ArmASL
import Janus
import JanusASL.Proofs.Mem
import JanusASL.Proofs.FP.Config
import Lean.Data.Json

/-!
# `janus-asl-check`: Janus `step` against Arm's ASL, both evaluated in compiled Lean

For every case of the oracle corpus (`artifacts/oracle/cases.jsonl`, format of
`oracle/layout/layout.go`), run

* the **ASL side**: `ArmASL.Functions.janus_step` (the sail-arm arm-v9.4-a model, sliced to the
  Janus subset and translated to Lean by Sail's Lean backend, `JanusASL/sail/`), from the Linux
  EL0 state of `janus_init` with the MMU on and a 4-level identity map of the code page and the
  data buffer (the same tables as `oracle-sail/src/main.rs`), and
* the **Janus side**: `Janus.Arm64.step` from the state `Oracle/Main.lean` builds,

and compare. This is a *test* (compiled evaluation), not a proof. See `docs/ASL.md`.

Verdicts (one per case):

* `agree`: both completed with equal X0-X30, SP, PC, NZCV and memory (data buffer bytes; no
  other byte of the ASL memory changed), or Janus faulted where the ASL takes the matching
  exception (outsideAllocation ↔ data abort, spMisaligned ↔ SP alignment fault), or Janus
  faulted `pcMisaligned` where the ASL branched to that misaligned PC (the fault is the next
  fetch), or both reject the word (Janus `undecodable`, ASL UNDEFINED).
* `gap`: Janus faulted conservatively where the ASL has a result (the word is outside the
  Janus subset, or an access the Linux identity map allows but Janus' allocation does not,
  or a branch to a tagged address).
* `MISMATCH`: anything else, in particular Janus completing with a state the ASL does not
  produce, Janus decoding a word the ASL treats as UNDEFINED/UNPREDICTABLE, or a Janus-decoded
  word reaching an excluded clause of the slice. The exit code is 1 if there is any.
-/

open Lean
open ArmASL ArmASL.Functions

namespace JanusASL.Check

/-! ## Layout (`oracle/layout/layout.go`, `oracle-sail/src/main.rs`) -/

def codePage : Nat := 0x10_0000_0000
def testPC : Nat := codePage + 0x800
def dataBase : Nat := codePage + 0x4_0000
def dataSize : Nat := 4096
def pageSize : Nat := 4096
def ttL0 : Nat := 0x7000_0000

def pattern (seed i : Nat) : Nat := (i * 157 + seed * 89 + (i / 256) * 41 + 7) % 256

/-! ## Case parsing (as `Oracle/Main.lean`) -/

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

structure Case where
  id : Nat
  cls : String
  word : Nat
  pc : Nat
  x : Array Nat
  sp : Nat
  nzcv : Nat
  seed : Nat
  /-- V0..V31 (128-bit; absent in the case: all zero) and TPIDR_EL0 (absent: 0). -/
  v : Array Nat
  tpidr : Nat
  /-- FPCR and FPSR (32-bit; absent in the case: 0). -/
  fpcr : Nat
  fpsr : Nat

def parseCase (line : String) : Except String Case := do
  let j ← Json.parse line
  let id ← j.getObjValAs? Nat "id"
  let cls := (j.getObjValAs? String "class").toOption.getD ""
  let word ← parseHex (← j.getObjValAs? String "word")
  let pc ← ((do parseHex (← j.getObjValAs? String "pc")) <|> pure testPC)
  let xs ← j.getObjValAs? (Array String) "x"
  if xs.size ≠ 31 then throw "x must have 31 entries"
  let x ← xs.mapM parseHex
  let sp ← parseHex (← j.getObjValAs? String "sp")
  let nzcv ← j.getObjValAs? Nat "nzcv"
  let seed ← j.getObjValAs? Nat "seed"
  let vs ← (j.getObjValAs? (Array String) "v" <|> pure #[])
  if vs.size ≠ 0 && vs.size ≠ 32 then throw "v must have 32 entries"
  let v ← if vs.size = 0 then pure (Array.replicate 32 0) else vs.mapM parseHex
  let tpidr ← ((do parseHex (← j.getObjValAs? String "tpidr")) <|> pure 0)
  let fpcr ← ((do parseHex (← j.getObjValAs? String "fpcr")) <|> pure 0)
  let fpsr ← ((do parseHex (← j.getObjValAs? String "fpsr")) <|> pure 0)
  if fpcr ≥ 2 ^ 32 ∨ fpsr ≥ 2 ^ 32 then throw "fpcr/fpsr must be below 2^32"
  pure { id, cls, word, pc, x, sp, nzcv, seed, v, tpidr, fpcr, fpsr }

/-! ## The ASL side -/

abbrev SState := Sail.ConcurrencyInterfaceV1.SequentialState RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource

def emptyState : SState :=
  { regs := ∅, choiceState := (), mem := ∅, tags := (), cycleCount := 0, sailOutput := #[] }

def runM (m : SailM α) (s : SState) : Except String (α × SState) :=
  match m.run s with
  | .ok a s => .ok (a, s)
  | .error e _ => .error (match e with
      | .User _ => "uncaught Sail exception"
      | e => e.print)

def writeU64 (mem : Std.ExtHashMap Nat (BitVec 8)) (addr v : Nat) : Std.ExtHashMap Nat (BitVec 8) :=
  (List.range 8).foldl (fun m i => m.insert (addr + i) (BitVec.ofNat 8 (v / 256 ^ i))) mem

def zeroPage (mem : Std.ExtHashMap Nat (BitVec 8)) (base : Nat) : Std.ExtHashMap Nat (BitVec 8) :=
  (List.range pageSize).foldl (fun m i => m.insert (base + i) 0) mem

/-- Translation tables of `oracle-sail/src/main.rs` (`install_tables`): L0..L3 at `ttL0`,
the code page user RW + PXN, the data page user RW + PXN + UXN, Normal WB (AttrIndx 0),
inner shareable, AF, nG. Plus the (zero) code page and data page themselves. -/
def baseMemory : Std.ExtHashMap Nat (BitVec 8) := Id.run do
  let mut m : Std.ExtHashMap Nat (BitVec 8) := ∅
  for t in [ttL0, ttL0 + pageSize, ttL0 + 2 * pageSize, ttL0 + 3 * pageSize] do
    m := zeroPage m t
  let table := 3
  let pageRWUser := 3 + (1 <<< 6) + (3 <<< 8) + (1 <<< 10) + (1 <<< 11)
  let pxn := 1 <<< 53
  let uxn := 1 <<< 54
  let l0 := (codePage >>> 39) % 512
  let l1 := (codePage >>> 30) % 512
  let l2 := (codePage >>> 21) % 512
  m := writeU64 m (ttL0 + 8 * l0) ((ttL0 + pageSize) + table)
  m := writeU64 m (ttL0 + pageSize + 8 * l1) ((ttL0 + 2 * pageSize) + table)
  m := writeU64 m (ttL0 + 2 * pageSize + 8 * l2) ((ttL0 + 3 * pageSize) + table)
  m := writeU64 m (ttL0 + 3 * pageSize + 8 * ((codePage >>> 12) % 512)) (codePage + pageRWUser + pxn)
  m := writeU64 m (ttL0 + 3 * pageSize + 8 * ((dataBase >>> 12) % 512))
    (dataBase + pageRWUser + pxn + uxn)
  m := zeroPage m codePage
  m := zeroPage m dataBase
  return m

/-- Every address `baseMemory` defines outside the data buffer (tables, code page). -/
def baseKeys : List Nat :=
  [ttL0, ttL0 + pageSize, ttL0 + 2 * pageSize, ttL0 + 3 * pageSize, codePage].flatMap fun b =>
    (List.range pageSize).map (b + ·)

/-- Registers after `sail_model_init` (declared initial values, then `initialize_registers`: undefined = 0) and
`janus_init` (Arm's reset `__InitSystem`, then the Linux EL0 configuration). -/
def baseState : Except String SState := do
  let ((), s) ← runM (sail_model_init ()) emptyState
  let ((), s) ← runM (janus_init ()) s
  pure { s with mem := baseMemory }


/-! ## `UserMapped` (JanusASL/Proofs/Mem.lean), evaluated

The load/store theorems assume that the ASL's own `AArch64_TranslateAddress` maps every byte of
Janus' regions identically as Normal write-back memory, without fault and without changing the
state. The check evaluates that on its tables: every byte of the data buffer, as a load and a
store, aligned or not, for every access size, on the base state (with the state compared on every
register the translation code can write), and a few bytes on every case's pre-state. -/

/-- Every register the call graph of `AArch64_TranslateAddress` writes (static, from the generated
code) holds the same value in `s` and `s2`. -/
def transRegsSame (s s2 : SState) : Bool :=
  toString (repr (s2.regs.get? Register.BRBFCR_EL1)) == toString (repr (s.regs.get? Register.BRBFCR_EL1)) &&
  toString (repr (s2.regs.get? Register.Branchtypetaken)) == toString (repr (s.regs.get? Register.Branchtypetaken)) &&
  toString (repr (s2.regs.get? Register.DLR_EL0)) == toString (repr (s.regs.get? Register.DLR_EL0)) &&
  toString (repr (s2.regs.get? Register.DSPSR_EL0)) == toString (repr (s.regs.get? Register.DSPSR_EL0)) &&
  toString (repr (s2.regs.get? Register.EDWAR)) == toString (repr (s.regs.get? Register.EDWAR)) &&
  toString (repr (s2.regs.get? Register.FPCR)) == toString (repr (s.regs.get? Register.FPCR)) &&
  toString (repr (s2.regs.get? Register.FPSR)) == toString (repr (s.regs.get? Register.FPSR)) &&
  toString (repr (s2.regs.get? Register.GCSPR_EL0)) == toString (repr (s.regs.get? Register.GCSPR_EL0)) &&
  toString (repr (s2.regs.get? Register.GCSPR_EL1)) == toString (repr (s.regs.get? Register.GCSPR_EL1)) &&
  toString (repr (s2.regs.get? Register.GCSPR_EL2)) == toString (repr (s.regs.get? Register.GCSPR_EL2)) &&
  toString (repr (s2.regs.get? Register.GCSPR_EL3)) == toString (repr (s.regs.get? Register.GCSPR_EL3)) &&
  toString (repr (s2.regs.get? Register.GICC_CTLR)) == toString (repr (s.regs.get? Register.GICC_CTLR)) &&
  toString (repr (s2.regs.get? Register.ICC_PMR_EL1)) == toString (repr (s.regs.get? Register.ICC_PMR_EL1)) &&
  toString (repr (s2.regs.get? Register.InGuardedPage)) == toString (repr (s.regs.get? Register.InGuardedPage)) &&
  toString (repr (s2.regs.get? Register.MDCCSR_EL0)) == toString (repr (s.regs.get? Register.MDCCSR_EL0)) &&
  toString (repr (s2.regs.get? Register.PMICNTR_EL0)) == toString (repr (s.regs.get? Register.PMICNTR_EL0)) &&
  toString (repr (s2.regs.get? Register.PMOVSCLR_EL0)) == toString (repr (s.regs.get? Register.PMOVSCLR_EL0)) &&
  toString (repr (s2.regs.get? Register.PMOVSSET_EL0)) == toString (repr (s.regs.get? Register.PMOVSSET_EL0)) &&
  toString (repr (s2.regs.get? Register.PMUEventAccumulator)) == toString (repr (s.regs.get? Register.PMUEventAccumulator)) &&
  toString (repr (s2.regs.get? Register.PSTATE)) == toString (repr (s.regs.get? Register.PSTATE)) &&
  toString (repr (s2.regs.get? Register.R0)) == toString (repr (s.regs.get? Register.R0)) &&
  toString (repr (s2.regs.get? Register.R1)) == toString (repr (s.regs.get? Register.R1)) &&
  toString (repr (s2.regs.get? Register.R10)) == toString (repr (s.regs.get? Register.R10)) &&
  toString (repr (s2.regs.get? Register.R11)) == toString (repr (s.regs.get? Register.R11)) &&
  toString (repr (s2.regs.get? Register.R12)) == toString (repr (s.regs.get? Register.R12)) &&
  toString (repr (s2.regs.get? Register.R13)) == toString (repr (s.regs.get? Register.R13)) &&
  toString (repr (s2.regs.get? Register.R14)) == toString (repr (s.regs.get? Register.R14)) &&
  toString (repr (s2.regs.get? Register.R15)) == toString (repr (s.regs.get? Register.R15)) &&
  toString (repr (s2.regs.get? Register.R16)) == toString (repr (s.regs.get? Register.R16)) &&
  toString (repr (s2.regs.get? Register.R17)) == toString (repr (s.regs.get? Register.R17)) &&
  toString (repr (s2.regs.get? Register.R18)) == toString (repr (s.regs.get? Register.R18)) &&
  toString (repr (s2.regs.get? Register.R19)) == toString (repr (s.regs.get? Register.R19)) &&
  toString (repr (s2.regs.get? Register.R2)) == toString (repr (s.regs.get? Register.R2)) &&
  toString (repr (s2.regs.get? Register.R20)) == toString (repr (s.regs.get? Register.R20)) &&
  toString (repr (s2.regs.get? Register.R21)) == toString (repr (s.regs.get? Register.R21)) &&
  toString (repr (s2.regs.get? Register.R22)) == toString (repr (s.regs.get? Register.R22)) &&
  toString (repr (s2.regs.get? Register.R23)) == toString (repr (s.regs.get? Register.R23)) &&
  toString (repr (s2.regs.get? Register.R24)) == toString (repr (s.regs.get? Register.R24)) &&
  toString (repr (s2.regs.get? Register.R25)) == toString (repr (s.regs.get? Register.R25)) &&
  toString (repr (s2.regs.get? Register.R26)) == toString (repr (s.regs.get? Register.R26)) &&
  toString (repr (s2.regs.get? Register.R27)) == toString (repr (s.regs.get? Register.R27)) &&
  toString (repr (s2.regs.get? Register.R28)) == toString (repr (s.regs.get? Register.R28)) &&
  toString (repr (s2.regs.get? Register.R29)) == toString (repr (s.regs.get? Register.R29)) &&
  toString (repr (s2.regs.get? Register.R3)) == toString (repr (s.regs.get? Register.R3)) &&
  toString (repr (s2.regs.get? Register.R30)) == toString (repr (s.regs.get? Register.R30)) &&
  toString (repr (s2.regs.get? Register.R4)) == toString (repr (s.regs.get? Register.R4)) &&
  toString (repr (s2.regs.get? Register.R5)) == toString (repr (s.regs.get? Register.R5)) &&
  toString (repr (s2.regs.get? Register.R6)) == toString (repr (s.regs.get? Register.R6)) &&
  toString (repr (s2.regs.get? Register.R7)) == toString (repr (s.regs.get? Register.R7)) &&
  toString (repr (s2.regs.get? Register.R8)) == toString (repr (s.regs.get? Register.R8)) &&
  toString (repr (s2.regs.get? Register.R9)) == toString (repr (s.regs.get? Register.R9)) &&
  toString (repr (s2.regs.get? Register.RC)) == toString (repr (s.regs.get? Register.RC)) &&
  toString (repr (s2.regs.get? Register.Records_INF)) == toString (repr (s.regs.get? Register.Records_INF)) &&
  toString (repr (s2.regs.get? Register.Records_SRC)) == toString (repr (s.regs.get? Register.Records_SRC)) &&
  toString (repr (s2.regs.get? Register.Records_TGT)) == toString (repr (s.regs.get? Register.Records_TGT)) &&
  toString (repr (s2.regs.get? Register.SPESampleAddress)) == toString (repr (s.regs.get? Register.SPESampleAddress)) &&
  toString (repr (s2.regs.get? Register.SPESampleAddressValid)) == toString (repr (s.regs.get? Register.SPESampleAddressValid)) &&
  toString (repr (s2.regs.get? Register.SPESampleClass)) == toString (repr (s.regs.get? Register.SPESampleClass)) &&
  toString (repr (s2.regs.get? Register.SPESampleCounterPending)) == toString (repr (s.regs.get? Register.SPESampleCounterPending)) &&
  toString (repr (s2.regs.get? Register.SPESampleCounterValid)) == toString (repr (s.regs.get? Register.SPESampleCounterValid)) &&
  toString (repr (s2.regs.get? Register.SPESampleEvents)) == toString (repr (s.regs.get? Register.SPESampleEvents)) &&
  toString (repr (s2.regs.get? Register.SPESampleOpType)) == toString (repr (s.regs.get? Register.SPESampleOpType)) &&
  toString (repr (s2.regs.get? Register.SPESamplePreviousBranchAddress)) == toString (repr (s.regs.get? Register.SPESamplePreviousBranchAddress)) &&
  toString (repr (s2.regs.get? Register.SPESamplePreviousBranchAddressValid)) == toString (repr (s.regs.get? Register.SPESamplePreviousBranchAddressValid)) &&
  toString (repr (s2.regs.get? Register.SPESampleSubclass)) == toString (repr (s.regs.get? Register.SPESampleSubclass)) &&
  toString (repr (s2.regs.get? Register.SP_EL0)) == toString (repr (s.regs.get? Register.SP_EL0)) &&
  toString (repr (s2.regs.get? Register.SP_EL1)) == toString (repr (s.regs.get? Register.SP_EL1)) &&
  toString (repr (s2.regs.get? Register.SP_EL2)) == toString (repr (s.regs.get? Register.SP_EL2)) &&
  toString (repr (s2.regs.get? Register.SP_EL3)) == toString (repr (s.regs.get? Register.SP_EL3)) &&
  toString (repr (s2.regs.get? Register.TSTATE)) == toString (repr (s.regs.get? Register.TSTATE)) &&
  toString (repr (s2.regs.get? Register._DLR)) == toString (repr (s.regs.get? Register._DLR)) &&
  toString (repr (s2.regs.get? Register._DSPSR)) == toString (repr (s.regs.get? Register._DSPSR)) &&
  toString (repr (s2.regs.get? Register._DSPSR2)) == toString (repr (s.regs.get? Register._DSPSR2)) &&
  toString (repr (s2.regs.get? Register._EDSCR)) == toString (repr (s.regs.get? Register._EDSCR)) &&
  toString (repr (s2.regs.get? Register._FFR)) == toString (repr (s.regs.get? Register._FFR)) &&
  toString (repr (s2.regs.get? Register._P)) == toString (repr (s.regs.get? Register._P)) &&
  toString (repr (s2.regs.get? Register._PC)) == toString (repr (s.regs.get? Register._PC)) &&
  toString (repr (s2.regs.get? Register._Z)) == toString (repr (s.regs.get? Register._Z)) &&
  toString (repr (s2.regs.get? Register.__BranchTaken)) == toString (repr (s.regs.get? Register.__BranchTaken)) &&
  toString (repr (s2.regs.get? Register.__GIC_Active)) == toString (repr (s.regs.get? Register.__GIC_Active)) &&
  toString (repr (s2.regs.get? Register.__GIC_Pending)) == toString (repr (s.regs.get? Register.__GIC_Pending)) &&
  toString (repr (s2.regs.get? Register.__janus_exc_syndrome)) == toString (repr (s.regs.get? Register.__janus_exc_syndrome)) &&
  toString (repr (s2.regs.get? Register.__janus_exc_taken)) == toString (repr (s.regs.get? Register.__janus_exc_taken)) &&
  toString (repr (s2.regs.get? Register.__janus_exc_target_el)) == toString (repr (s.regs.get? Register.__janus_exc_target_el)) &&
  toString (repr (s2.regs.get? Register.__janus_exc_type)) == toString (repr (s.regs.get? Register.__janus_exc_type)) &&
  toString (repr (s2.regs.get? Register.__janus_exc_vaddress)) == toString (repr (s.regs.get? Register.__janus_exc_vaddress)) &&
  toString (repr (s2.regs.get? Register.__last_branch_valid)) == toString (repr (s.regs.get? Register.__last_branch_valid)) &&
  toString (repr (s2.regs.get? Register.__last_cycle_count)) == toString (repr (s.regs.get? Register.__last_cycle_count))

/-- The access descriptors `UserMapped` covers for a load (`w = false`) or store: `gprAcc` and
`OrdAcc`. -/
def accsFor (w : Bool) : List AccessDescriptor :=
  [JanusASL.Proofs.gprAcc w, JanusASL.Proofs.acqRelAcc w, JanusASL.Proofs.exclAcc w false,
    JanusASL.Proofs.exclAcc w true] ++ (if w then [] else [JanusASL.Proofs.acqPCAcc])

def transOk1 (s : SState) (va : Nat) (acc : AccessDescriptor) (al : Bool) (size : Int) (full : Bool := false) : Bool :=
  match runM (AArch64_TranslateAddress (BitVec.ofNat 64 va) acc al size) s with
  | .ok (d, s2) =>
    d.fault.statuscode == .Fault_None && d.paddress.address == (BitVec.ofNat 64 va).setWidth 56 &&
      d.memattrs.memtype == .MemType_Normal && d.memattrs.inner.attrs == MemAttr_WB &&
      d.memattrs.outer.attrs == MemAttr_WB && s2.mem.size == s.mem.size && s2.cycleCount == s.cycleCount &&
      s2.sailOutput.size == s.sailOutput.size && (!full || transRegsSame s s2)
  | .error _ => false

/-- The atomic descriptors (`atomAcc`), every operation and ordering. -/
def atomAccs : List AccessDescriptor :=
  [MemAtomicOp.MemAtomicOp_GCSSS1, .MemAtomicOp_ADD, .MemAtomicOp_BIC, .MemAtomicOp_EOR, .MemAtomicOp_ORR,
    .MemAtomicOp_SMAX, .MemAtomicOp_SMIN, .MemAtomicOp_UMAX, .MemAtomicOp_UMIN, .MemAtomicOp_SWP,
    .MemAtomicOp_CAS].flatMap fun op =>
    [false, true].flatMap fun a => [false, true].map fun r => JanusASL.Proofs.atomAcc op a r

def transOk (s : SState) (va : Nat) (w al : Bool) (size : Int) (full : Bool := false) : Bool :=
  (accsFor w).all fun acc => transOk1 s va acc al size full

def transOkAtom (s : SState) (va : Nat) (al : Bool) (size : Int) : Bool :=
  atomAccs.all fun acc => transOk1 s va acc al size

/-- The data buffer is outside the model's GIC and UART windows (`UserMapped.nodev`). -/
def dataNoDev : Bool := (dataBase / 2 ^ 16 != 0x2C00 && (dataBase + dataSize - 1) / 2 ^ 16 != 0x2C00 &&
  dataBase / 2 ^ 16 != 0x3C00 && (dataBase + dataSize - 1) / 2 ^ 16 != 0x3C00)

/-- The sweep on the base state: every byte, load and store, aligned or not, sizes 1..16. -/
def userMappedBase (s : SState) : Bool :=
  dataNoDev && (List.range dataSize).all fun i => [false, true].all fun w => [false, true].all fun al =>
    ([1, 2, 4, 8, 16] : List Int).all fun sz => transOk s (dataBase + i) w al sz (full := i % 64 == 0) &&
      (!w || i % 16 != 0 || transOkAtom s (dataBase + i) al sz)

/-- The per-case points: first, last and a seed-dependent byte, as a load and a store. -/
def userMappedCase (s : SState) (seed : Nat) : Bool :=
  [dataBase, dataBase + dataSize - 1, dataBase + (seed * 97 + 13) % dataSize].all fun va =>
    [false, true].all fun w => transOk s va w false 8 && (!w || transOkAtom s va true 8)

/-- What the ASL step produced. -/
inductive AslResult where
  | ok (x : Array Nat) (sp pc nzcv : Nat) (mem : List (Nat × Nat)) (stray : List Nat) (v : Array Nat) (fpsr : Nat)
  | exception (ty : ArmASL.Exception) (syndrome : Nat) (vaddr : Nat)
  | undefined
  | unpredictable
  | impdef (s : String)
  | other (s : String)
  | error (s : String)

def excName (e : ArmASL.Exception) : String := (repr e).pretty

/-- The ASL step of a case, and whether `LinuxEL0Config` (`JanusASL.Proofs.cfgOk`) holds on its
pre-state and (if it completes) its post-state: the configuration the branch theorems assume. -/
def runAsl (base : SState) (c : Case) : AslResult × Bool × Bool := Id.run do
  let mem0 := (List.range dataSize).foldl
    (fun m i => m.insert (dataBase + i) (BitVec.ofNat 8 (pattern c.seed i))) base.mem
  let mem0 := (List.range 4).foldl
    (fun m i => m.insert (testPC + i) (BitVec.ofNat 8 (c.word / 256 ^ i))) mem0
  let s0 : SState := { base with mem := mem0 }
  let setup : SailM Unit := do
    for i in [0:31] do
      janus_set_x (BitVec.ofNat 5 i) (BitVec.ofNat 64 c.x[i]!)
    janus_set_sp (BitVec.ofNat 64 c.sp)
    janus_set_nzcv (BitVec.ofNat 4 c.nzcv)
    janus_set_pc (BitVec.ofNat 64 c.pc)
    for i in [0:32] do
      janus_set_v (BitVec.ofNat 5 i) (BitVec.ofNat 128 c.v[i]!)
    janus_set_tpidr (BitVec.ofNat 64 c.tpidr)
    writeReg Register.FPCR (BitVec.ofNat 64 c.fpcr)
    writeReg Register.FPSR (BitVec.ofNat 64 c.fpsr)
  match runM setup s0 with
  | .error e => return (.error s!"setup: {e}", false, false)
  | .ok ((), s1) =>
  let pre := JanusASL.Proofs.cfgOk s1 && JanusASL.Proofs.fpCfgOk s1
  let um := userMappedCase s1 c.seed
  match runM (janus_step (BitVec.ofNat 32 c.word)) s1 with
  | .error e => return (.error e, pre, um)
  | .ok (r, s2) =>
  let cfg := pre && JanusASL.Proofs.cfgOk s2 && JanusASL.Proofs.fpCfgOk s2
  match r with
  | .Janus_OK =>
    let readBack : SailM (Array Nat × Nat × Nat × Nat × Array Nat × Nat) := do
      let mut xs := #[]
      for i in [0:31] do
        xs := xs.push (← janus_get_x (BitVec.ofNat 5 i)).toNat
      let mut vs := #[]
      for i in [0:32] do
        vs := vs.push (← janus_get_v (BitVec.ofNat 5 i)).toNat
      pure (xs, (← janus_get_sp ()).toNat, (← janus_get_pc ()).toNat, (← janus_get_nzcv ()).toNat, vs,
        (← readReg Register.FPSR).toNat)
    match runM readBack s2 with
    | .error e => return (.error s!"readback: {e}", cfg, um)
    | .ok ((xs, sp, pc, nzcv, vs, fpsr), _) =>
      let mem := (List.range dataSize).filterMap fun i =>
        let b := (s2.mem.getD (dataBase + i) 0).toNat
        if b ≠ pattern c.seed i then some (i, b) else none
      -- every other byte the ASL memory holds must be unchanged, and no new byte appears
      let stray := baseKeys.filterMap fun a =>
        if s2.mem.get? a = mem0.get? a then none else some a
      let stray := if s2.mem.size = mem0.size then stray else stray ++ [0]
      return (.ok xs sp pc nzcv mem stray vs fpsr, cfg, um)
  | .Janus_Exception =>
    let rd : SailM (ArmASL.Exception × BitVec 25 × BitVec 64) := do
      pure (← readReg Register.__janus_exc_type, ← readReg Register.__janus_exc_syndrome, ← readReg Register.__janus_exc_vaddress)
    match runM rd s2 with
    | .ok ((e, syn, va), _) => return (.exception e syn.toNat va.toNat, cfg, um)
    | .error e => return (.error e, cfg, um)
  | .Janus_Undefined => return (.undefined, cfg, um)
  | .Janus_Unpredictable => return (.unpredictable, cfg, um)
  | .Janus_ImpDef =>
    match runM (readReg Register.__janus_impdef) s2 with
    | .ok (s, _) => return (.impdef s, cfg, um)
    | .error e => return (.error e, cfg, um)
  | .Janus_See => return (.other "SEE", cfg, um)
  | .Janus_Other => return (.other "ReservedEncoding/SError", cfg, um)

/-! ## The Janus side (as `Oracle/Main.lean`) -/

open Janus.Arm64 in
def janusInit (dczid : Nat) (c : Case) : State :=
  { regs := fun i => if i < 31 then BitVec.ofNat 64 c.x[i]! else 0
    sp := BitVec.ofNat 64 c.sp
    pc := BitVec.ofNat 64 c.pc
    flags := ⟨c.nzcv &&& 8 ≠ 0, c.nzcv &&& 4 ≠ 0, c.nzcv &&& 2 ≠ 0, c.nzcv &&& 1 ≠ 0⟩
    mem :=
      { bytes := fun a =>
          if dataBase ≤ a ∧ a < dataBase + dataSize then BitVec.ofNat 8 (pattern c.seed (a - dataBase))
          else 0
        regions := [{ base := dataBase, size := dataSize, writable := true }] }
    dczid := BitVec.ofNat 5 dczid
    vregs := fun i => if i < 32 then BitVec.ofNat 128 c.v[i]! else 0
    tpidr := BitVec.ofNat 64 c.tpidr
    fpcr := BitVec.ofNat 32 c.fpcr
    fpsr := BitVec.ofNat 32 c.fpsr }

open Janus.Arm64 in
def nzcvOf (f : Flags) : Nat :=
  (if f.n then 8 else 0) + (if f.z then 4 else 0) + (if f.c then 2 else 0) + (if f.v then 1 else 0)

/-! ## Comparison -/

inductive Verdict where
  | agree (kind : String)
  | gap (kind : String)
  | mismatch (why : String)

/-- DFSC (ISS bits 5:0) of a data abort. -/
def dfsc (syn : Nat) : Nat := syn % 64

def isAlignmentDfsc (d : Nat) : Bool := d == 0x21
def isTranslationOrPermission (d : Nat) : Bool := d / 4 == 1 || d / 4 == 2 || d / 4 == 3 || d == 0

/-- The implemented FPSR bits: N Z C V (31:28), QC (27), IDC (7), IXC UFC OFC DZC IOC (4:0).
The others are RES0. Sail stores whatever `MSR FPSR` writes in the 64-bit register (it does not
model RES0 fields), while an implementation may make them RAZ/WI, as Janus does; so FPSR is
compared on the implemented bits. -/
def fpsrImpl : Nat := 0xF800009F

/-- `UDF #imm` (permanently UNDEFINED; agent/syscall decodes it as a trap with SIGILL, 4):
the ASL's UNDEFINED is the same outcome. Matched on the fault's `repr` so that the check also
builds against a Janus without that constructor. -/
def isUdfTrap {α : Type} [Repr α] (f : α) : Bool :=
  let r := (repr f).pretty
  r.takeWhile (· != ' ') == "Janus.Arm64.Fault.trap" && (r.splitOn " ").getLast? == some "4"

open Janus.Arm64 in
def compare (dczid : Nat) (c : Case) (asl : AslResult) : Verdict :=
  match Janus.Arm64.step c.word (janusInit dczid c), asl with
  | .error (.undecodable _ _), .undefined => .agree "both-undefined"
  | .error (.undecodable _ _), .impdef _ => .gap "janus-undecodable/asl-excluded"
  | .error (.undecodable _ _), .error e => .gap s!"janus-undecodable/asl-error:{e}"
  | .error (.undecodable _ _), _ => .gap "janus-undecodable"
  | _, .impdef s => .mismatch s!"janus decodes, ASL: {s}"
  | .error f, .undefined =>
    if isUdfTrap f then .agree "udf-undefined" else .mismatch "janus decodes an UNDEFINED encoding"
  | _, .undefined => .mismatch "janus decodes an UNDEFINED encoding"
  | _, .unpredictable => .mismatch "janus decodes a (CONSTRAINED) UNPREDICTABLE case"
  | _, .other s => .mismatch s!"ASL: {s}"
  | _, .error e => .mismatch s!"ASL model error: {e}"
  | .ok s, .ok xs sp pc nzcv mem stray vs fpsr =>
    let jx := (List.range 31).map fun i => (s.regs i).toNat
    let jmem := (List.range dataSize).filterMap fun i =>
      let b := (s.mem.bytes (dataBase + i)).toNat
      if b ≠ pattern c.seed i then some (i, b) else none
    if jx != xs.toList then .mismatch s!"X: janus {jx.map hex} asl {xs.toList.map hex}"
    else if s.sp.toNat ≠ sp then .mismatch s!"SP: janus {hex s.sp.toNat} asl {hex sp}"
    else if s.pc.toNat ≠ pc then .mismatch s!"PC: janus {hex s.pc.toNat} asl {hex pc}"
    else if nzcvOf s.flags ≠ nzcv then .mismatch s!"NZCV: janus {nzcvOf s.flags} asl {nzcv}"
    else if jmem != mem then .mismatch s!"memory: janus {jmem} asl {mem}"
    else if (List.range 32).map (fun i => (s.vregs i).toNat) != vs.toList then
      .mismatch s!"V: janus {(List.range 32).map fun i => hex (s.vregs i).toNat} asl {vs.toList.map hex}"
    else if s.fpsr.toNat ≠ fpsr &&& fpsrImpl then
      .mismatch s!"FPSR: janus {hex s.fpsr.toNat} asl {hex fpsr} (implemented bits {hex (fpsr &&& fpsrImpl)})"
    else if !stray.isEmpty then .mismatch s!"ASL wrote outside the data buffer: {stray.take 4 |>.map hex}"
    else .agree "ok"
  | .ok _, .exception ty syn va => .mismatch s!"janus completes, ASL takes {excName ty} (ISS {hex syn}, va {hex va})"
  | .error (.outsideAllocation _ _), .exception .Exception_DataAbort syn _ =>
    if isTranslationOrPermission (dfsc syn) then .agree "data-abort" else
      .gap s!"outsideAllocation/data-abort-dfsc-{hex (dfsc syn)}"
  | .error (.outsideAllocation _ _), .ok .. => .gap "outsideAllocation/asl-ok (mapped page)"
  | .error (.spMisaligned _), .exception .Exception_SPAlignment _ _ => .agree "sp-alignment"
  | .error (.unaligned _ _), .exception .Exception_DataAbort syn _ =>
    if isAlignmentDfsc (dfsc syn) then .agree "alignment-fault" else
      .gap s!"unaligned/data-abort-dfsc-{hex (dfsc syn)}"
  | .error (.pcMisaligned t), .ok _ _ pc _ _ _ _ _ =>
    if pc == t then .agree "pc-misaligned-next-fetch" else .mismatch s!"pcMisaligned {hex t}, ASL pc {hex pc}"
  | .error (.noCode t), .ok _ _ pc _ _ _ _ _ => .gap s!"noCode {hex t}/asl-pc {hex pc}"
  | .error f, .exception ty syn _ => .gap s!"janus {(repr f).pretty.takeWhile (· != ' ')}/asl {excName ty} ISS {hex syn}"
  | .error f, .ok .. => .gap s!"janus {(repr f).pretty.takeWhile (· != ' ')}/asl-ok"

def verdictJson (c : Case) : Verdict → Json
  | .agree k => Json.mkObj [("id", c.id), ("class", c.cls), ("verdict", "agree"), ("kind", k)]
  | .gap k => Json.mkObj [("id", c.id), ("class", c.cls), ("verdict", "gap"), ("kind", k)]
  | .mismatch w => Json.mkObj [("id", c.id), ("class", c.cls), ("word", hex c.word),
      ("verdict", "MISMATCH"), ("why", w)]

end JanusASL.Check

open JanusASL.Check in
def main (args : List String) : IO UInt32 := do
  let path := args.headD "artifacts/oracle/cases.jsonl"
  let out := (args.drop 1).headD "artifacts/asl/verdicts.jsonl"
  let jobs := ((args.drop 2).headD "48").toNat!
  let base ← match baseState with
    | .ok s => pure s
    | .error e => IO.eprintln s!"janus-asl-check: ASL initialisation failed: {e}"; return 2
  -- DCZID_EL0 is IMPLEMENTATION DEFINED; `State.dczid` is a free parameter of every Janus
  -- theorem, so Janus runs with the ASL model's value (as scripts/oracle-sail.sh does).
  let dczid ← match runM (readReg Register.DCZID_EL0) base with
    | .ok (v, _) => pure (v.toNat % 32)
    | .error e => IO.eprintln s!"janus-asl-check: DCZID_EL0: {e}"; return 2
  IO.eprintln s!"janus-asl-check: ASL DCZID_EL0<4:0> = {hex dczid}"
  if path == "--cfg" then
    -- configuration registers of the base state (the values the proofs' `Cfg` assumes)
    match runM (readReg Register.FeatureImpl) base with
    | .ok (v, _) =>
      IO.println s!"FeatureImpl true at: {(List.range 259).filter (fun i => v.toArray.getD i false)}"
    | .error e => IO.println s!"FeatureImpl: {e}"
    match runM (readReg Register.BRBFCR_EL1) base with
    | .ok (v, _) => IO.println s!"BRBFCR_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"BRBFCR_EL1: {e}"
    match runM (readReg Register.BRBCR_EL1) base with
    | .ok (v, _) => IO.println s!"BRBCR_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"BRBCR_EL1: {e}"
    match runM (readReg Register.BRBCR_EL2) base with
    | .ok (v, _) => IO.println s!"BRBCR_EL2 = {hex v.toNat}"
    | .error e => IO.println s!"BRBCR_EL2: {e}"
    match runM (readReg Register.PMSIDR_EL1) base with
    | .ok (v, _) => IO.println s!"PMSIDR_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"PMSIDR_EL1: {e}"
    match runM (readReg Register.PMSCR_EL1) base with
    | .ok (v, _) => IO.println s!"PMSCR_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"PMSCR_EL1: {e}"
    match runM (readReg Register.PMSCR_EL2) base with
    | .ok (v, _) => IO.println s!"PMSCR_EL2 = {hex v.toNat}"
    | .error e => IO.println s!"PMSCR_EL2: {e}"
    match runM (readReg Register.PMBLIMITR_EL1) base with
    | .ok (v, _) => IO.println s!"PMBLIMITR_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"PMBLIMITR_EL1: {e}"
    match runM (readReg Register.PMBSR_EL1) base with
    | .ok (v, _) => IO.println s!"PMBSR_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"PMBSR_EL1: {e}"
    match runM (readReg Register.GCSCRE0_EL1) base with
    | .ok (v, _) => IO.println s!"GCSCRE0_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"GCSCRE0_EL1: {e}"
    match runM (readReg Register.GCSCR_EL1) base with
    | .ok (v, _) => IO.println s!"GCSCR_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"GCSCR_EL1: {e}"
    match runM (readReg Register.HCRX_EL2) base with
    | .ok (v, _) => IO.println s!"HCRX_EL2 = {hex v.toNat}"
    | .error e => IO.println s!"HCRX_EL2: {e}"
    match runM (readReg Register.TCR_EL2) base with
    | .ok (v, _) => IO.println s!"TCR_EL2 = {hex v.toNat}"
    | .error e => IO.println s!"TCR_EL2: {e}"
    match runM (readReg Register.SCTLR_EL2) base with
    | .ok (v, _) => IO.println s!"SCTLR_EL2 = {hex v.toNat}"
    | .error e => IO.println s!"SCTLR_EL2: {e}"
    match runM (readReg Register.SCTLR_EL3) base with
    | .ok (v, _) => IO.println s!"SCTLR_EL3 = {hex v.toNat}"
    | .error e => IO.println s!"SCTLR_EL3: {e}"
    match runM (readReg Register.CPTR_EL3) base with
    | .ok (v, _) => IO.println s!"CPTR_EL3 = {hex v.toNat}"
    | .error e => IO.println s!"CPTR_EL3: {e}"
    match runM (readReg Register.CPTR_EL2) base with
    | .ok (v, _) => IO.println s!"CPTR_EL2 = {hex v.toNat}"
    | .error e => IO.println s!"CPTR_EL2: {e}"
    match runM (readReg Register.CPACR_EL1) base with
    | .ok (v, _) => IO.println s!"CPACR_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"CPACR_EL1: {e}"
    match runM (readReg Register.MDSCR_EL1) base with
    | .ok (v, _) => IO.println s!"MDSCR_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"MDSCR_EL1: {e}"
    match runM (readReg Register.SPESampleInFlight) base with
    | .ok (v, _) => IO.println s!"SPESampleInFlight = {v}"
    | .error e => IO.println s!"SPESampleInFlight: {e}"
    match runM (readReg Register.InGuardedPage) base with
    | .ok (v, _) => IO.println s!"InGuardedPage = {v}"
    | .error e => IO.println s!"InGuardedPage: {e}"
    match runM (readReg Register.SCR) base with
    | .ok (v, _) => IO.println s!"SCR = {hex v.toNat}"
    | .error e => IO.println s!"SCR: {e}"
    match runM (readReg Register.SCR_EL3) base with
    | .ok (v, _) => IO.println s!"SCR_EL3 = {hex v.toNat}"
    | .error e => IO.println s!"SCR_EL3: {e}"
    match runM (readReg Register.HCR_EL2) base with
    | .ok (v, _) => IO.println s!"HCR_EL2 = {hex v.toNat}"
    | .error e => IO.println s!"HCR_EL2: {e}"
    match runM (readReg Register.TCR_EL1) base with
    | .ok (v, _) => IO.println s!"TCR_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"TCR_EL1: {e}"
    match runM (readReg Register.SCTLR_EL1) base with
    | .ok (v, _) => IO.println s!"SCTLR_EL1 = {hex v.toNat}"
    | .error e => IO.println s!"SCTLR_EL1: {e}"
    match runM (readReg Register.MDCR_EL3) base with
    | .ok (v, _) => IO.println s!"MDCR_EL3 = {hex v.toNat}"
    | .error e => IO.println s!"MDCR_EL3: {e}"
    match runM (readReg Register.MDCR_EL2) base with
    | .ok (v, _) => IO.println s!"MDCR_EL2 = {hex v.toNat}"
    | .error e => IO.println s!"MDCR_EL2: {e}"
    match runM (CreateAccDescGPR MemOp.MemOp_LOAD false false true) base with
    | .ok (acc, _) => IO.println s!"accdesc load: {repr acc}"
    | .error e => IO.println s!"accdesc: {e}"
    -- translation of a data-buffer address, as a load and as a store
    for (nm, op) in [("load", MemOp.MemOp_LOAD), ("store", MemOp.MemOp_STORE)] do
      let tr : SailM (AddressDescriptor × Bool) := do
        let acc ← CreateAccDescGPR op false false true
        let tc ← AArch64_AccessIsTagChecked (BitVec.ofNat 64 (dataBase + 8)) acc
        let d ← AArch64_TranslateAddress (BitVec.ofNat 64 (dataBase + 8)) acc true 8
        pure (d, tc)
      match runM tr base with
      | .ok ((d, tc), _) =>
        IO.println s!"{nm}: fault {repr d.fault.statuscode} pa {hex d.paddress.address.toNat} {repr d.paddress.paspace} memtype {repr d.memattrs.memtype} inner {d.memattrs.inner.attrs} outer {d.memattrs.outer.attrs} tags {repr d.memattrs.tags} tagchecked {tc}"
      | .error e => IO.println s!"{nm}: {e}"
    return 0
  if path == "--dump-asl" then
    -- The ASL side only, one JSON line per case (V0-V31, FPSR, outcome), for comparing the Lean
    -- model with Sail's C backend (audit/rt-asl/sqrt: FSQRT and the `sqrt_real` replacement).
    let cases ← IO.FS.lines out
    for l in cases do
      let l := l.trimAscii.toString
      if l == "" then continue
      match parseCase l with
      | .error e => throw (IO.userError s!"bad case: {e}")
      | .ok c =>
        let (r, _, _) := runAsl base c
        let j := match r with
          | .ok _ _ _ _ _ _ vs fpsr => Json.mkObj [("id", c.id), ("status", "ok"),
              ("v", Json.arr (vs.map fun x => Json.str (hex x))), ("fpsr", hex fpsr)]
          | .exception ty syn _ => Json.mkObj [("id", c.id), ("status", s!"exception {excName ty} {hex syn}")]
          | .undefined => Json.mkObj [("id", c.id), ("status", "undefined")]
          | .unpredictable => Json.mkObj [("id", c.id), ("status", "unpredictable")]
          | .impdef s => Json.mkObj [("id", c.id), ("status", s!"impdef {s}")]
          | .other s => Json.mkObj [("id", c.id), ("status", s!"other {s}")]
          | .error s => Json.mkObj [("id", c.id), ("status", s!"error {s}")]
        IO.println j.compress
    return 0
  -- The corpus (about 1 GB of JSON lines) is streamed: cases are read, run and written in
  -- batches of `jobs * 256`, one batch running while the next is read, so memory is bounded by
  -- two batches whatever the corpus size. Verdicts are written in corpus order, as before.
  let hin ← IO.FS.Handle.mk path .read
  let h ← IO.FS.Handle.mk out .write
  IO.eprintln s!"janus-asl-check: streaming {path}, {jobs} tasks"
  let batch := jobs * 256
  let baseCfg := JanusASL.Proofs.cfgOk base && JanusASL.Proofs.fpCfgOk base
  let umBase := userMappedBase base
  let spawn (cases : Array Case) : List (Task (Array (Case × Verdict × Bool × Bool))) :=
    let chunk := (cases.size + jobs - 1) / jobs
    (List.range jobs).map fun k =>
      Task.spawn (prio := .dedicated) fun _ =>
        (cases.extract (k * chunk) ((k + 1) * chunk)).map fun c =>
          let (r, cfg, um) := runAsl base c
          (c, compare dczid c r, cfg, um)
  let mut total := 0
  let mut cfgBad := 0
  let mut umBad := 0
  let mut agree := 0
  let mut gap := 0
  let mut mism := 0
  let mut kinds : Std.HashMap String Nat := {}
  let mut pending : List (Task (Array (Case × Verdict × Bool × Bool))) := []
  let mut eof := false
  while !eof || !pending.isEmpty do
    -- read the next batch (while the pending one runs)
    let mut cases : Array Case := #[]
    while !eof && cases.size < batch do
      let l ← hin.getLine
      if l.isEmpty then
        eof := true
      else
        let l := l.trimAscii.toString
        if l != "" then
          match parseCase l with
          | .ok c => cases := cases.push c
          | .error e => throw (IO.userError s!"bad case: {e}")
    let next := if cases.isEmpty then [] else spawn cases
    -- write the pending batch's verdicts, in order
    for t in pending do
      for (c, v, cfg, um) in t.get do
        total := total + 1
        -- LinuxEL0Config (the branch theorems' assumption) on every case's pre- and post-state
        if !cfg then cfgBad := cfgBad + 1
        if !um then umBad := umBad + 1
        h.putStrLn (verdictJson c v).compress
        match v with
        | .agree k => agree := agree + 1; kinds := kinds.insert ("agree " ++ k) (kinds.getD ("agree " ++ k) 0 + 1)
        | .gap k =>
          gap := gap + 1
          let k := k.takeWhile (· != ' ')
          kinds := kinds.insert ("gap " ++ k) (kinds.getD ("gap " ++ k) 0 + 1)
        | .mismatch _ => mism := mism + 1
    pending := next
  IO.eprintln s!"janus-asl-check: {total} cases"
  for (k, n) in kinds.toList.mergeSort (fun a b => a.2 ≥ b.2) do
    IO.println s!"{n}\t{k}"
  IO.println s!"cases {total}  agree {agree}  gap {gap}  MISMATCH {mism}"
  IO.println s!"LinuxEL0Config and FPConfig: base {baseCfg}, cases violating them (pre- or post-state) {cfgBad}"
  IO.println s!"UserMapped (data buffer): base sweep {umBase}, cases violating it (pre-state points) {umBad}"
  return if mism = 0 && baseCfg && cfgBad = 0 && umBase && umBad = 0 then 0 else 1
