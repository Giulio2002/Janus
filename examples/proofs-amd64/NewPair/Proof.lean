import Janus
import Extracted

/-!
# `NewPair(a, b uint64) *Pair` on amd64: a fresh heap object holding `a` and `b`

**Guarantee.** For all `a`, `b`, every list `rt` of runtime-owned ranges and **every**
implementation of `runtime.newobject` satisfying `NewobjectContract64`
(`Janus/Contracts/AllocAmd64.lean`), and every Go call state in which the stack-growth prologue
falls through, `RSP` is 8-aligned, the stack window `[RSP-4128, RSP+24)` (frame, return-address
slot, 4096 bytes for the runtime, two spill slots) is writable and outside `rt`, and memory holds
the read-only data (the `Pair` type descriptor): the call returns, obeys the ABI, and `RAX` is a
pointer `ptr` with `[ptr, ptr+16)` inside `rt` (fresh: disjoint from all caller data outside it),
writable and 16-byte aligned, holding `a` and `b`; memory outside `rt` and the stack window is
unchanged.

**What is assumed.** Only the contract hypothesis `hnew` for the code linked at
`runtime.newobject`, which is not extracted (`--contract`); see docs/RUNTIME-CONTRACTS.md.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Proof

set_option maxRecDepth 20000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (a b : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4128 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4128) 4152 rt ∧ (s.regs 4).toNat % 8 = 0)
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 16 true = true ∧
        s'.mem.readLE ptr 8 = a.toNat ∧ s'.mem.readLE (ptr + 8) 8 = b.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal ⊢
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x25] calls [hnew.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 16 rt› hout
  janus64_run
  refine ⟨_, rfl, ‹_›, ‹_›, ‹_›, ?_, ?_, ?_⟩
  · janus64_simp
  · janus64_simp
  · janus_frame

end Proof
