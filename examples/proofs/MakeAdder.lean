import Extracted

/-!
# `MakeAdder(a uint64) func(uint64) uint64`: creating an escaping closure

**Guarantee.** For every `a`, every list `rt` of runtime-owned memory ranges and **every**
implementation of `runtime.newobject` that satisfies the allocation contract
`NewobjectContract` (`Janus/Contracts/Alloc.lean`), and every Go call state of
`example.com/basic.MakeAdder` in which the stack-growth prologue falls through, the stack window
`[SP-4144, SP+24)` (the 48-byte frame, 4096 bytes for the runtime, the spill slot) is writable
and outside `rt`, and memory holds the program's read-only data (the type descriptor of the
closure's struct): the call returns, obeys the ABI, and `fv = X0` is a **fresh** funcval:

* `[fv, fv+16)` lies inside the runtime-owned ranges (disjoint from everything the caller holds
  outside them), writable, 16-byte aligned;
* its code word is the closure body `MakeAdder.func1` (`FuncvalIs`) and the captured variable
  after it is `a` (`ClosureCtx`): exactly the hypotheses under which a caller's theorem about
  calling `fv` (as `MapSum.lean` does) applies;
* memory is unchanged outside `rt` and the stack window.

The closure outlives the call, so the compiler allocates its funcval with `runtime.newobject`
(compare `Compose.lean`, where it stays in the frame) and fills in the code address and `a`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (a : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096) :
    Ensures (Extracted.program.link impl) Extracted.entry [a]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt)
      (fun s s' => InRanges (s'.regs 0).toNat 16 rt ∧ (s'.regs 0).toNat % 16 = 0 ∧
        s'.mem.accessible (s'.regs 0).toNat 16 true = true ∧
        FuncvalIs s'.mem (s'.regs 0) (segAddr Extracted.program "example.com/basic.MakeAdder.func1") ∧
        ClosureCtx s'.mem (s'.regs 0) [a] ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout⟩
  janus_intro hs
  janus_data hd [hw]
  janus_run until [Extracted.entry + 0x28] calls [hnew.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 16 rt› hout
  janus_run
  have hf : segAddr Extracted.program "example.com/basic.MakeAdder.func1" = janus_eval% segAddr Extracted.program "example.com/basic.MakeAdder.func1" := by decide
  refine ⟨‹_›, ‹_›, ‹_›, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · janus_simp
    exact accessible_sub ‹s.mem.accessible _ 16 true = true› (by simp) (by omega) (by omega)
  · rw [hf]; janus_simp
  · janus_simp
    simp only [List.length_cons, List.length_nil]
    exact accessible_sub ‹s.mem.accessible _ 16 true = true› (by simp) (by omega) (by omega)
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    obtain rfl : i = 0 := by omega
    janus_simp
    rfl
  · janus_frame

end Proof
