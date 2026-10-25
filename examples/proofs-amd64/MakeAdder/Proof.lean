import Janus
import Extracted

/-!
# `MakeAdder(a uint64) func(uint64) uint64` on amd64: creating an escaping closure

**Guarantee.** For every `a`, every list `rt` of runtime-owned ranges and **every**
implementation of `runtime.newobject` satisfying `NewobjectContract64`
(`Janus/Contracts/AllocAmd64.lean`), and every Go call state in which the stack-growth prologue
falls through, `RSP` is 8-aligned, the stack window `[RSP-4128, RSP+24)` is writable and outside
`rt`, and memory holds the read-only data (the closure struct's type descriptor): the call
returns, obeys the ABI, and `fv = RAX` is a fresh funcval: `[fv, fv+16)` inside `rt`, writable,
16-byte aligned, whose code word is `MakeAdder.func1` (`FuncvalIs`) and whose captured variable
is `a` (`ClosureCtx`); memory outside `rt` and the stack window is unchanged. The closure
escapes (it is the result), so its funcval comes from `runtime.newobject`, not the frame.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Spec

namespace Proof

set_option maxRecDepth 20000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (a : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096) :
    Ensures (Extracted.program.link impl) Extracted.entry [a]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4128 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4128) 4152 rt ∧ (s.regs 4).toNat % 8 = 0)
      (fun s s' => InRanges (s'.regs 0).toNat 16 rt ∧ (s'.regs 0).toNat % 16 = 0 ∧
        s'.mem.accessible (s'.regs 0).toNat 16 true = true ∧
        FuncvalIs s'.mem (s'.regs 0) (segAddr Extracted.program "example.com/basic.MakeAdder.func1") ∧
        ClosureCtx s'.mem (s'.regs 0) [a] ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal ⊢
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x1f] calls [hnew.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 16 rt› hout
  janus64_run
  refine ⟨‹_›, ‹_›, ‹_›, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · janus64_simp
    exact accessible_sub ‹Arm64.Memory.accessible s.mem _ 16 true = true› (by simp) (by omega) (by omega)
  · janus64_simp
  · janus64_simp
    simp only [List.length_cons, List.length_nil]
    exact accessible_sub ‹Arm64.Memory.accessible s.mem _ 16 true = true› (by simp) (by omega) (by omega)
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    obtain rfl : i = 0 := by omega
    janus64_simp
    rfl
  · janus_frame

end Proof
