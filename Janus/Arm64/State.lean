/-!
# Machine state for the AArch64 user-mode model

This file is the shared contract between the ISA model (`Decode`, `Exec`), the program
loader (`Janus.Program`), the Go calling convention (`Janus.GoABI`) and the oracle.

* General-purpose registers `X0`–`X30` are indexed by `Nat`; only `0..30` are meaningful.
  Register number 31 is never stored here: instructions read it as `XZR` or `SP`
  depending on the encoding, which `readZR` / `readSP` make explicit.
* Memory is byte-addressed by `Nat` and carries the list of allocations the caller owns.
  Every access is checked against these regions; an access that is not fully inside one
  well-formed region is a fault, never undefined behaviour. A region is well-formed when it
  lies below `2^48`, the Linux arm64 user virtual-address limit, so every successful access is
  below `2^48`: it never wraps around `2^64`, and a tagged address (top byte non-zero, which
  hardware with top-byte-ignore would alias to an untagged one) always faults. A store also
  faults if any byte it touches lies in a read-only region, even when a writable region covers
  it too (hardware permissions are per byte, not per allocation).
* `dczid` is the 5 meaningful bits of the read-only system register DCZID_EL0 (`BS` in bits 3:0,
  the log2 of the DC ZVA block size in 4-byte words; `DZP` in bit 4, DC ZVA prohibited). It is
  IMPLEMENTATION DEFINED (qemu `-cpu max` reports 7, the Sail Armv9.4 model 8, Neoverse cores
  4), so it is part of the state: execution never changes it, and a theorem about arbitrary
  initial states quantifies over every value. The default `0x10` (DC ZVA prohibited) only fills
  in concrete states built in tests and witnesses.
* There are no SIMD/FP (`V0`–`V31`) registers: no supported instruction reads or writes them
  (Go 1.26 `runtime.memmove`/`memclrNoHeapPointers` and the compiler's inline copies and
  zeroing use general-purpose `LDP`/`STP` only; see `docs/SOUNDNESS.md`).
-/

namespace Janus.Arm64

abbrev W64 := BitVec 64
abbrev W32 := BitVec 32
abbrev Byte := BitVec 8

structure Flags where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
deriving Repr, DecidableEq, Inhabited

structure Region where
  base : Nat
  size : Nat
  writable : Bool
deriving Repr, DecidableEq, Inhabited

structure Memory where
  bytes : Nat → Byte
  regions : List Region

instance : Inhabited Memory := ⟨⟨fun _ => 0, []⟩⟩

structure State where
  regs : Nat → W64
  sp : W64
  pc : W64
  flags : Flags
  mem : Memory
  /-- DCZID_EL0 bits 4:0 (`DZP:BS`); constant during execution. -/
  dczid : BitVec 5 := 0x10

instance : Inhabited State :=
  ⟨{ regs := fun _ => 0, sp := 0, pc := 0, flags := ⟨false, false, false, false⟩, mem := default }⟩

/-- Reasons execution stops without a defined architectural result. -/
inductive Fault where
  /-- The word at `pc` is outside the supported, decoded subset. -/
  | undecodable (pc : Nat) (word : Nat)
  /-- `pc` does not point into any loaded code segment or known stub. -/
  | noCode (pc : Nat)
  /-- A memory access of `size` bytes at `addr` is not inside one (well-formed) allocation. -/
  | outsideAllocation (addr : Nat) (size : Nat)
  /-- A store touched a read-only allocation. -/
  | readOnly (addr : Nat) (size : Nat)
  /-- An access used `SP` as base while `SP` was not 16-byte aligned (SCTLR_EL1.SA0). -/
  | spMisaligned (sp : Nat)
  /-- A branch to a misaligned (non multiple of 4) target. -/
  | pcMisaligned (pc : Nat)
  /-- An ordered, exclusive or atomic access of `size` bytes at `addr` that is not naturally
  aligned (the model requires natural alignment for these, see `Exec`). -/
  | unaligned (addr : Nat) (size : Nat)
  /-- The instruction at `pc` is disabled by the system configuration (DC ZVA while
  `DCZID_EL0.DZP = 1`); on Linux a `SIGILL`. -/
  | trapped (pc : Nat)
  /-- Fuel ran out before the call returned. -/
  | outOfFuel
deriving Repr, DecidableEq, Inhabited

namespace State

/-- Read register `r` where encoding 31 means the zero register. -/
def readZR (s : State) (r : Nat) : W64 := if r = 31 then 0 else s.regs r

/-- Read register `r` where encoding 31 means the stack pointer. -/
def readSP (s : State) (r : Nat) : W64 := if r = 31 then s.sp else s.regs r

/-- Write register `r` where encoding 31 discards the value (`XZR`). -/
def writeZR (s : State) (r : Nat) (v : W64) : State :=
  if r = 31 then s else { s with regs := fun i => if i = r then v else s.regs i }

/-- Write register `r` where encoding 31 sets the stack pointer. -/
def writeSP (s : State) (r : Nat) (v : W64) : State :=
  if r = 31 then { s with sp := v } else { s with regs := fun i => if i = r then v else s.regs i }

end State

namespace Memory

/-- `size` bytes at `addr` lie inside a single region that ends at or below `2^48` (the Linux
arm64 user address limit), writable if `write`; and, for a write, no read-only region overlaps
`[addr, addr + size)`. -/
def accessible (m : Memory) (addr size : Nat) (write : Bool) : Bool :=
  m.regions.any (fun r => r.base ≤ addr && addr + size ≤ r.base + r.size &&
      r.base + r.size ≤ 2 ^ 48 && (!write || r.writable)) &&
    (!write || m.regions.all fun r => r.writable || addr + size ≤ r.base || r.base + r.size ≤ addr)

/-- Little-endian read of `n` bytes as a natural number. -/
def readLE (m : Memory) (addr : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (m.bytes addr).toNat + 256 * m.readLE (addr + 1) n

/-- Little-endian write of the low `n` bytes of `v`. -/
def writeLE (m : Memory) (addr n v : Nat) : Memory :=
  { m with bytes := fun a =>
      if addr ≤ a ∧ a < addr + n then BitVec.ofNat 8 (v / 256 ^ (a - addr)) else m.bytes a }

end Memory

/-- Checked load of `n ∈ {1,2,4,8,16}` bytes. -/
def load (m : Memory) (addr n : Nat) : Except Fault Nat :=
  if m.accessible addr n false then .ok (m.readLE addr n) else .error (.outsideAllocation addr n)

/-- Checked store of the low `n` bytes of `v`: `outsideAllocation` unless the bytes are readable,
`readOnly` unless they lie in one writable region and no read-only region overlaps them. -/
def store (m : Memory) (addr n v : Nat) : Except Fault Memory :=
  if m.accessible addr n false then
    if m.accessible addr n true then .ok (m.writeLE addr n v) else .error (.readOnly addr n)
  else .error (.outsideAllocation addr n)

end Janus.Arm64
