import Janus
import Extracted

/-! `example.com/basic.AddThree` on amd64: `Add(Add(x, y), z)`, through the stack-check prologue and two calls. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (x y z : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y, z] 1
      (fun s => StackGuardOK s 0 ∧ StackWritable s 32 32)
      (fun r => r = [x + y + z]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, hle, hnw, hacc⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run

end Proof
