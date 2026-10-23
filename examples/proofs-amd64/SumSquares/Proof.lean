import Janus
import Extracted

/-! `example.com/basic.SumSquares` on amd64: `square(x) + square(y)`, through the stack-check
prologue and two calls of the helper `square` (`IMULQ AX, AX`). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (x y : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 1
      (fun s => StackGuardOK s 0 ∧ StackWritable s 32 32)
      (fun r => r = [x * x + y * y]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, hle, hnw, hacc⟩ := hpre
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgb hnw2 hgr
  janus64_run
  rw [BitVec.add_comm]

end Proof
