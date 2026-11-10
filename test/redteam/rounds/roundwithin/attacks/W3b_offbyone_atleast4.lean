import Extracted

/-! Expected-reason: Lean rejected the proof (the bound is too large). A lower bound of 4 where the shorter path executes 3. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem atLeast (x y : BitVec 64) :
    RunsAtLeastOnCall (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
