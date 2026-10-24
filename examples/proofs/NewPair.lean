import Extracted

/-!
# `NewPair(a, b uint64) *Pair` returns a fresh heap object holding `a` and `b`

**Guarantee.** For all `a`, `b`, every list `rt` of runtime-owned memory ranges and **every**
implementation of `runtime.newobject` that satisfies the allocation contract
`NewobjectContract` (`Janus/Contracts/Alloc.lean`: it returns a fresh, zeroed, aligned object of
`typ.Size_` bytes inside `rt` and changes nothing outside `rt` and its own stack), and every Go call
state of `example.com/basic.NewPair` in which the stack-growth prologue falls through, the stack
window `[SP-4144, SP+24)` (NewPair's 48-byte frame, 4096 bytes for the runtime, the two spill
slots) is writable and outside `rt`, and memory holds the program's read-only data (the type
descriptor of `Pair`): the call returns, obeys the ABI, and `X0` is a pointer `ptr` with

* `[ptr, ptr+16)` inside the runtime-owned ranges, so it is disjoint from every object the
  caller holds outside them (a *fresh* object), writable and 16-byte aligned;
* the word at `ptr` is `a` and the word at `ptr+8` is `b`;
* memory unchanged outside `rt` and the stack window.

**What is assumed.** The statement quantifies over the code at `runtime.newobject`
(`Extracted.program.link impl`) and assumes the contract for it (the hypothesis `hnew`). The
allocator itself is not executed: `janus extract --contract runtime.newobject` leaves it out
(`Extracted.program.contracts`), and the theorem holds for the real binary exactly when the real
runtime meets the contract (docs/RUNTIME-CONTRACTS.md).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt)
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 16 true = true ∧
        s'.mem.readLE ptr 8 = a.toNat ∧ s'.mem.readLE (ptr + 8) 8 = b.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout⟩
  janus_intro hs
  janus_data hd [hw]
  -- run to the instruction after `bl runtime.newobject`, using the contract at the call
  janus_run until [Extracted.entry + 0x34] calls [hnew.pos]
  -- the object is inside `rt`, the stack window outside it
  have hdj := InRanges.disjoint ‹InRanges _ 16 rt› hout
  janus_run
  refine ⟨_, rfl, ‹_›, ‹_›, ‹_›, ?_, ?_, ?_⟩
  · janus_simp
  · janus_simp
  · janus_frame

end Proof
