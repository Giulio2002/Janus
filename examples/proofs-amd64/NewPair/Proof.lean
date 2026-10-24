import Janus
import Extracted

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
