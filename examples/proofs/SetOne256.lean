import Extracted

/-!
# `SetOne256(z *[4]uint64)` stores the 256-bit value 1 into `z` (a `.rodata` constant)

**Guarantee.** For every pointer `z` and every Go call state `s` of
`example.com/basic.SetOne256` (`z` in `X0`) in which the 32 bytes at `z` are writable and memory
holds the program's read-only data (`Program.DataLoaded`: the 32-byte `.rodata` constant
`{1, 0, 0, 0}` that the code loads with `adrp`/`add`/`ldp`, copied from the binary and checked by
`janus verify`), the call returns (never faulting or panicking), obeys the ABI, the value at `z` is `1`, and no other byte
changes.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof


theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => Ptr32 s.mem z true ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' => val256 s'.mem z.toNat = 1 ∧ OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, hd⟩
  janus_intro hs
  janus_data hd
  janus_run




namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def wbytes (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧ (Ptr32 s.mem z true ∧ Extracted.program.DataLoaded s.mem) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (val256 s'.mem z.toNat = 1 ∧ OnlyWrites s.mem s'.mem z.toNat 32)) := by
  refine ⟨ret, s0, (0x300000), hret, setup, ?pre, correctness (0x300000) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, dataByte, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
