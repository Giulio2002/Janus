import Extracted

/-! Expected-reason: the instruction bound mentions the execution of the program. The budget is computed from the final state of a run. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- the true bound: used by the attacks to obtain a kernel-checked statement of the weaker shape. -/
theorem real (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True) (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega

/-- the "bound" reads the result of running the program: it depends on the post-state. -/
def lenOf (s : State) : Nat :=
  match Extracted.program.run 8 s with
  | .ok (.returned s') => (s'.regs 0).toNat
  | _ => 0

theorem within (x y : BitVec 64) :
    EnsuresWithin (fun s => lenOf s + 4) Extracted.program Extracted.entry [x, y] (fun _ => True) (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) :=
  (real x y).mono_bound fun _ _ => Nat.le_add_left _ _

end Proof
