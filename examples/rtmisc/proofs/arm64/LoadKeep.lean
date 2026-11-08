import Extracted

/-!
# `LoadKeep(p *uint64) uint64`: a load followed by `runtime.KeepAlive(p)` (arm64)

```go
func LoadKeep(p *uint64) uint64 { v := *p; runtime.KeepAlive(p); return v }
```

**Guarantee.** For every pointer `p` whose 8 bytes are readable and every Go call state whose
spill slot `[SP+8, SP+16)` is writable and does not overlap them, the call returns, obeys the
ABI, returns the word at `p` read before the call, and its only write is `p` itself into the
spill slot.

**What `KeepAlive` is.** `runtime.KeepAlive` is a compiler intrinsic (`ssagen` `OpKeepAlive`):
there is no call and no runtime code. Its only effect on the machine code is that `p` stays
live until the intrinsic, which here is the store of `p` into its argument spill slot (a stack
slot the garbage collector scans). The model has no garbage collector, so the guarantee is this
machine-level one: the store happens, nothing else does. That the object stays reachable is a
property of the collector and is not stated (docs/RUNTIME-CONTRACTS.md, "Remaining runtime").
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p]
      (fun s => Ptr s.mem p 8 false ∧ StackOK s 0 16 ∧ Disjoint p.toNat 8 (s.sp.toNat + 8) 8)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE p.toNat 8 ∧
        s'.mem = s.mem.writeLE (s.sp.toNat + 8) 8 p.toNat) := by
  intro ret hret s hs ⟨⟨hp, hp'⟩, ⟨hal, _, hb, hw⟩, hd⟩
  simp only [Disjoint] at hd
  janus_intro hs
  janus_run

namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000


def bytes0 (a : Nat) : BitVec 8 :=
  0

def mem0 : Janus.Arm64.Memory := ⟨bytes0, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x1000, false⟩, ⟨0x300000, 0x100, false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000 : BitVec 64) else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0) with rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : Janus.Arm64.State) (p : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [p] s ∧ (Ptr s.mem p 8 false ∧ StackOK s 0 16 ∧ Disjoint p.toNat 8 (s.sp.toNat + 8) 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = s.mem.readLE p.toNat 8 ∧
        s'.mem = s.mem.writeLE (s.sp.toNat + 8) 8 p.toNat)) := by
  refine ⟨ret, s0, 0x300000, hret, setup, ?pre, correctness 0x300000 ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, mem0, bytes0, sp0, g0] <;> decide

end Witness

end Proof
