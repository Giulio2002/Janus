import Extracted

/-! Expected-reason: Lean rejected the proof (the bound is too small). Fuel off by one: `Max` needs 4 instructions on its longer path. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 3) Extracted.program Extracted.entry [x, y] (fun _ => True) (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega

end Proof
