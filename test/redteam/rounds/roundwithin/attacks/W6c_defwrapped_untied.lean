import Extracted

/-! Expected-reason: no witness tied to `within`. The statement is def-wrapped; wrapping does not exempt it from the witness rule. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- the true bound: used by the attacks to obtain a kernel-checked statement of the weaker shape. -/
theorem real (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True) (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega

def Stmt (x y : BitVec 64) : Prop :=
  EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True) (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y)

theorem within (x y : BitVec 64) : Stmt x y := real x y

end Proof
