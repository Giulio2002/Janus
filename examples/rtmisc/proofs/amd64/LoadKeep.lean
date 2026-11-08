import Janus
import Extracted

/-!
# `LoadKeep(p *uint64) uint64`: a load followed by `runtime.KeepAlive(p)` (amd64)

```go
func LoadKeep(p *uint64) uint64 { v := *p; runtime.KeepAlive(p); return v }
```

**Guarantee.** For every pointer `p` whose 8 bytes are readable and every Go call state whose
spill slot `[RSP+8, RSP+16)` is writable and does not overlap them, the call returns, obeys the
ABI, returns the word at `p` read before the call in `RAX`, and its only write is `p` itself
into the spill slot.

**What `KeepAlive` is.** A compiler intrinsic (`ssagen` `OpKeepAlive`): no call and no runtime
code; its only machine-level effect is that `p` stays live until it, here the store of `p` into
its spill slot. See the arm64 proof and docs/RUNTIME-CONTRACTS.md, "Remaining runtime".
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p]
      (fun s => StackWritable s 0 16 ∧ Buffer s p 8 false ∧ Janus.Spec.Disjoint p.toNat 8 ((s.regs regSP).toNat + 8) 8)
      (fun s s' => (s'.regs 0).toNat = valueAt s p 8 ∧
        s'.mem = s.mem.writeLE ((s.regs regSP).toNat + 8) 8 p.toNat) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hpb, hp⟩, hd⟩
  janus64_intro hs
  simp only [regSP] at hacc hnw hd ⊢
  simp only [Janus.Spec.Disjoint] at hd
  simp only [valueAt]
  janus64_run

namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x108000
def g0 : Nat := 0x300000
def tls0 : Nat := 0x400000


def bytes0 (a : Nat) : BitVec 8 :=
  if a = sp0 + 2 then 0x20 else if a = tls0 + 2 then 0x30 else
  0

def mem0 : Janus.Arm64.Memory := ⟨bytes0, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x1000, false⟩, ⟨tls0, 0x100, false⟩, ⟨0x300000, 0x100, false⟩]⟩

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then (0x300000 : BitVec 64) else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0, fsBase := BitVec.ofNat 64 (tls0 + 8) }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64)] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0) with rfl <;> first | rfl | decide, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : Janus.Amd64.State) (p : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [p] s ∧ (StackWritable s 0 16 ∧ Buffer s p 8 false ∧ Janus.Spec.Disjoint p.toNat 8 ((s.regs regSP).toNat + 8) 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = valueAt s p 8 ∧
        s'.mem = s.mem.writeLE ((s.regs regSP).toNat + 8) 8 p.toNat)) := by
  refine ⟨ret, s0, 0x300000, hret, setup, ?pre, correctness 0x300000 ret hret s0 setup ?pre⟩
  case pre =>
    try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Program.DataLoaded]
    repeat' apply And.intro
    all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

end Witness

end Proof
