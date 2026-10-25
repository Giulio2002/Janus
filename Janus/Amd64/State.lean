import Janus.Arm64.State
import Janus.Amd64.X87

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
  faults with `undefinedFlag`; the model never invents a value for it. The direction flag
  `RFLAGS.DF` is the separate field `df`: `CLD`/`STD` write it, `MOVS`/`STOS` step backward
  when it is set, and the Go ABI guarantees it is clear at calls (`GoABI.CallSetup.df`). The
  system flags are not modelled.
* The 256-bit AVX registers `YMM0`–`YMM15` are modelled as two fields: `xmm n` is bits 127:0
  (`XMMn`) and `ymmHi n` is bits 255:128, so `YMMn = ymmHi n ++ xmm n` (`State.ymm`). Go uses
  `XMM` to move and zero memory (`MOVUPS`, and `X15 = 0` in ABIInternal), and `YMM` in the AVX2
  paths of `memmove`, `memclrNoHeapPointers` and `internal/bytealg`. Keeping the upper lanes in
  their own field means a legacy-SSE instruction, which preserves bits 255:128 (SDM Vol. 1
  §14.1.3), simply does not touch `ymmHi`; a VEX.128 instruction zeroes `ymmHi` of its
  destination and a VEX.256 one writes both. The AVX-512 state (`ZMM` bits 511:256,
  `ZMM16`–`ZMM31`, the mask registers) is not modelled: no modelled instruction reads it (VEX
  instructions only zero it, which is unobservable to the model).
* `fsBase` is the base address of the `FS` segment (`IA32_FS_BASE`, set by the kernel for the
  thread: Go keeps the TLS block, with the `g` slot at `FS:-8`, there). An `FS`-prefixed memory
  operand is at `fsBase + effective address (mod 2^64)` and goes through the same checked
  memory as every other access. Specifications quantify over it (it is just a state field);
  `GoABI.TlsG` describes the `g` slot.
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
  /-- Bits 127:0 of `YMM0`–`YMM15` (`XMM0`–`XMM15`). -/
  xmm : Nat → W128
  mem : Memory
  /-- Bits 255:128 of `YMM0`–`YMM15`. -/
  ymmHi : Nat → W128 := fun _ => 0
  /-- The `FS` segment base. -/
  fsBase : W64 := 0
  /-- The direction flag `RFLAGS.DF` (`true` = string instructions step backward). -/
  df : Bool := false
  /-- `MXCSR`, the SSE control and status register: the exception flags `IE DE ZE OE UE PE`
  (bits 0–5), `DAZ` (6), the exception masks `IM DM ZM OM UM PM` (7–12), the rounding control
  `RC` (14:13) and `FTZ` (15). Read by the SSE floating-point instructions, which OR the flags
  of the exceptions they raise into it; no accepted instruction writes the control bits
  (`LDMXCSR` is not decoded). `0x1F80` (all masked, round to nearest) is the value Linux gives
  a new process; the Go ABI fixes only its control bits (`GoABI.GoMXCSR`), and the flags are
  sticky (a Go program's `main` already sees `PE` set). -/
  mxcsr : BitVec 32 := 0x1F80
  /-- The x87 FPU (`Janus.Amd64.X87.St`: data registers, `TOP`, tags, control and status
  words). Only the `long double` code of C functions uses it; Go code never does. -/
  x87 : X87.St := {}

instance : Inhabited State :=
  ⟨{ regs := fun _ => 0, rip := 0, flags := ⟨none, none, none, none, none, none⟩,
     xmm := fun _ => 0, mem := default }⟩

/-- The 256-bit value with upper half `hi` and lower half `lo`. -/
def ymmJoin (hi lo : W128) : Nat := hi.toNat * 2 ^ 128 + lo.toNat

/-- The full 256-bit register `YMMn` (`ymmHi n ++ xmm n`), as a natural number. -/
def State.ymm (s : State) (n : Nat) : Nat := ymmJoin (s.ymmHi n) (s.xmm n)

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
  /-- `#GP` for a misaligned 16-byte SSE or 16/32-byte AVX memory operand at `addr`. -/
  | misaligned (addr : Nat)
  /-- A branch to `target`, which is not a canonical lower-half (user) address `< 2^47`. -/
  | badTarget (target : Nat)
  /-- `#XM`: the SSE floating-point instruction at `pc` raised an exception that is unmasked
  in `MXCSR` (Linux delivers `SIGFPE`). -/
  | simdFPException (pc : Nat)
  /-- The x87 instruction at `pc` raised an exception that is unmasked in the x87 control word,
  or found one pending (`#MF`, `SIGFPE` on Linux; see `Janus.Amd64.X87`). -/
  | fpuException (pc : Nat)
  /-- The x87 instruction at `pc` overflowed or underflowed the register stack (pushed onto an
  in-use `ST(7)` or read an empty register). -/
  | fpuStack (pc : Nat)
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
