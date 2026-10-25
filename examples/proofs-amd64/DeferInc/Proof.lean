import Janus
import Extracted

/-! `example.com/basic.DeferInc(p, x)` on amd64: returns `x` and an open-coded deferred closure
increments `*p` on the normal return path. Example 2 of docs/COVERAGE.md R6 (an `Ensures` lifted
by `Ensures.toGo`: it never panics). -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.PanicAmd64

theorem correctness (P : Spec.PanicRuntime) (p x : BitVec 64) :
    EnsuresGo Extracted.program Extracted.entry [p, x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 64 48 ∧ Buffer s p 8 true ∧
        Spec.Disjoint p.toNat 8 ((s.regs regSP).toNat - 64) 112)
      (fun _ => goClass P)
      (fun s s' => s'.regs 0 = x ∧
        s'.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64)
      (fun _ _ _ => False) := by
  apply Ensures.toGo
  intro ret hret s hs hpre
  obtain ⟨hg, ⟨hle, hnw, hacc⟩, ⟨hbw, hb⟩, hd⟩ := hpre
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint]
    at hacc hle hnw hgl hgb hnw2 hgr hd
  janus64_run

end Proof
