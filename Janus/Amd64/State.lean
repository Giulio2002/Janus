import Janus.Arm64.State

/-!
# Machine state for the x86-64 (amd64) user-mode model

The shared contract between the ISA model (`Decode`, `Exec`), the program loader
(`Janus.Amd64.Program`), the Go calling convention (`Janus.Amd64.GoABI`) and the oracle.

* The 16 general-purpose registers are indexed by their hardware encoding number:
  `0 RAX, 1 RCX, 2 RDX, 3 RBX, 4 RSP, 5 RBP, 6 RSI, 7 RDI, 8..15 R8..R15`. Only `0..15` are
  meaningful. There is no separate stack pointer: `RSP` is register 4.
* `RIP` is the address of the next instruction to execute.
* `RFLAGS` is modelled by its six status flags. Each flag is `some b` (defined) or `none`
  (architecturally **undefined**, e.g. `SF` after `MUL`, everything after `DIV`). An
  instruction that reads an undefined flag (`Jcc`, `SETcc`, `CMOVcc`, `ADC`, `SBB`, `CMC`)
  faults with `undefinedFlag`; the model never invents a value for it. The direction flag is
  always clear in Go code (ABI) and no modelled instruction depends on it; the system flags are
  not modelled.
* The 128-bit SSE registers `XMM0`–`XMM15` are modelled because Go uses them to move and zero
  memory (`MOVUPS`, and `X15 = 0` in ABIInternal). Their upper YMM/ZMM halves are not modelled
  (no modelled instruction touches them).
* Memory is the checked byte memory of the arm64 model (`Janus.Arm64.Memory`, with
  `Janus.Arm64.load`/`store` semantics re-exported below with amd64 faults): every access must
  lie entirely inside one caller-provided region, and stores need a writable one. x86-64 user
  mode performs no alignment checks for ordinary accesses (`RFLAGS.AC` is clear), so there is
  no alignment fault except where an instruction requires one (`MOVAPS` and friends).
-/

namespace Janus.Amd64

abbrev W64 := BitVec 64
abbrev W128 := BitVec 128
abbrev Byte := BitVec 8
abbrev Memory := Janus.Arm64.Memory
abbrev Region := Janus.Arm64.Region

/-- The six status flags. `none` = undefined (reading it faults). -/
structure Flags where
  cf : Option Bool
  pf : Option Bool
  af : Option Bool
  zf : Option Bool
  sf : Option Bool
  ovf : Option Bool
deriving Repr, DecidableEq, Inhabited

structure State where
  regs : Nat → W64
  rip : W64
  flags : Flags
  xmm : Nat → W128
  mem : Memory

instance : Inhabited State :=
  ⟨⟨fun _ => 0, 0, ⟨none, none, none, none, none, none⟩, fun _ => 0, default⟩⟩

/-- Reasons execution stops without a defined architectural result. -/
inductive Fault where
  /-- The bytes at `pc` (at most 15 shown) are outside the supported, decoded subset. -/
  | undecodable (pc : Nat) (bytes : List Nat)
  /-- `pc` does not point into any loaded code segment or known stub. -/
  | noCode (pc : Nat)
  /-- A memory access of `size` bytes at `addr` is not inside one allocation. -/
  | outsideAllocation (addr : Nat) (size : Nat)
  /-- A store (or read-modify-write) targeted a read-only allocation. -/
  | readOnly (addr : Nat) (size : Nat)
  /-- The instruction at `pc` reads a status flag whose value is architecturally undefined. -/
  | undefinedFlag (pc : Nat)
  /-- The instruction at `pc` has an architecturally undefined result for these operands
  (e.g. 16-bit `SHLD` with a count above 16, or a 32-bit `BSF` of zero). -/
  | undefinedResult (pc : Nat)
  /-- `#DE`: division by zero or quotient overflow at `pc`. -/
  | divideError (pc : Nat)
  /-- `#GP` for a misaligned 16-byte SSE memory operand at `addr`. -/
  | misaligned (addr : Nat)
  /-- A branch to `target`, which is not a canonical lower-half (user) address `< 2^47`. -/
  | badTarget (target : Nat)
  /-- Fuel ran out before the call returned. -/
  | outOfFuel
deriving Repr, DecidableEq, Inhabited

/-- Checked load of `n` bytes (little-endian). Same condition as `Janus.Arm64.load`. -/
def load (m : Memory) (addr n : Nat) : Except Fault Nat :=
  if m.accessible addr n false then .ok (m.readLE addr n) else .error (.outsideAllocation addr n)

/-- Checked store of the low `n` bytes of `v`. Same conditions as `Janus.Arm64.store`. -/
def store (m : Memory) (addr n v : Nat) : Except Fault Memory :=
  if m.accessible addr n false then
    if m.accessible addr n true then .ok (m.writeLE addr n v) else .error (.readOnly addr n)
  else .error (.outsideAllocation addr n)

/-- The load half of a read-modify-write: the bytes must be readable **and writable** (the
model refuses a read-modify-write of read-only memory up front, whether or not the hardware
would get to the write). -/
def loadRW (m : Memory) (addr n : Nat) : Except Fault Nat :=
  if m.accessible addr n false then
    if m.accessible addr n true then .ok (m.readLE addr n) else .error (.readOnly addr n)
  else .error (.outsideAllocation addr n)

theorem load_eq_arm64 (m : Memory) (addr n : Nat) :
    load m addr n = match Janus.Arm64.load m addr n with
      | .ok v => .ok v
      | .error _ => .error (.outsideAllocation addr n) := by
  unfold load Janus.Arm64.load; split <;> rfl

theorem store_eq_arm64 (m : Memory) (addr n v : Nat) :
    store m addr n v = match Janus.Arm64.store m addr n v with
      | .ok m' => .ok m'
      | .error (.readOnly a k) => .error (.readOnly a k)
      | .error _ => .error (.outsideAllocation addr n) := by
  unfold store Janus.Arm64.store; split
  · split <;> rfl
  · rfl

end Janus.Amd64
