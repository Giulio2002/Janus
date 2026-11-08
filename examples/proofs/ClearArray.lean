import Extracted

/-!
# `ClearArray(p *[5]uint64)`: `clear` on an array

**Guarantee.** For every pointer `p` to 40 writable bytes (`Ptr`) and every Go call state of
`example.com/basic.ClearArray`, the call returns (never faulting or panicking), obeys the ABI, all
40 bytes of `*p` are zero afterwards (the 320-bit little-endian value at `p` is `0`), and nothing
outside `[p, p + 40)` changes (`OnlyWrites`).

`clear(p[:])` of a 5-word array compiles to two `stp xzr, xzr` and one `str xzr`; no call to
`memclrNoHeapPointers`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p] (fun s => Ptr s.mem p 40 true)
      (fun s s' => s'.mem.readLE p.toNat 40 = 0 ∧ OnlyWrites s.mem s'.mem p.toNat 40) := by
  intro ret hret s hs ⟨hp, hp'⟩
  janus_intro hs
  janus_run
  rw [show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) from rfl, Memory.readLE_add, Memory.readLE_add,
    Memory.readLE_add, Memory.readLE_add]
  janus_simp


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


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
theorem nonvacuous : ∃ (ret : Nat) (s : State) (p : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [p] s ∧ (Ptr s.mem p 40 true) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.mem.readLE p.toNat 40 = 0 ∧ OnlyWrites s.mem s'.mem p.toNat 40)) := by
  refine ⟨ret, s0, (0x300000), hret, setup, ?pre, correctness (0x300000) ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp] <;> decide

end Witness

end Proof
