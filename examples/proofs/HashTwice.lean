import Extracted

/-!
# `HashTwice(h *MulHasher, x uint64) uint64` hashes twice through the method value `h.Hash`

**Guarantee.** For every `h` in `X0`, `x` in `X1` and every Go call state `s` of
`example.com/basic.HashTwice` such that the receiver's field `K` (8 bytes at `h`) is readable
and outside `[SP-120, SP)`, the stack-growth prologues of all three frames fall through
(`GuardOK s 80`; the guard word is outside the window) and `SP` is aligned with
`[SP-120, SP)` writable (the frames of `HashTwice`, `ApplyTwice` and the method value wrapper
`(*MulHasher).Hash-fm`), the call returns, obeys the ABI, and `X0 = x · K · K`.

**How the dynamic calls are resolved.** `HashTwice` builds the method value on its own stack (a
funcval: the address of `(*MulHasher).Hash-fm`, then `h`) and passes it to `ApplyTwice`, which
calls it twice with `BLR` and `X26` pointing at it. The funcval is written by the code being
proved, so no hypothesis is needed: the executor reads the code address back from the stack
store, and the `BLR` target is a literal. The extractor finds `Hash-fm` because `HashTwice`
computes its address (an inferred dynamic target, recorded in `identity.json`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (h x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [h, x]
      (fun s => Ptr s.mem h 8 false ∧ Disjoint h.toNat 8 (s.sp.toNat - 120) 120 ∧
        GuardOK s 80 ∧ StackOK s 120 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 120) 120)
      (fun s s' => s'.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8) *
        BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) := by
  intro ret hret s hs ⟨⟨hh, hhb⟩, hd, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hd hgd
  janus_run


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (3) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (3 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (h : BitVec 64) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [h, x] s ∧ (Ptr s.mem h 8 false ∧ Disjoint h.toNat 8 (s.sp.toNat - 120) 120 ∧
        GuardOK s 80 ∧ StackOK s 120 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 120) 120) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8) *
        BitVec.ofNat 64 (s.mem.readLE h.toNat 8))) := by
  refine ⟨ret, s0, (0x300000), (3), hret, setup, ?pre, correctness (0x300000) (3) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
