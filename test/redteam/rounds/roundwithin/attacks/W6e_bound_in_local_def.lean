import Extracted

/-! Expected-reason: the instruction bound mentions the execution of the program; the bound is hidden in a proof-local definition inside a visible EnsuresWithin (the audit expands it). -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- the true bound: used by the attacks to obtain a kernel-checked statement of the weaker shape. -/
theorem real (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True) (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega

def B (s : State) : Nat :=
  match Extracted.program.run 8 s with
  | .ok (.returned s') => (s'.regs 0).toNat + 4
  | _ => 4

theorem within (x y : BitVec 64) :
    EnsuresWithin B Extracted.program Extracted.entry [x, y] (fun _ => True) (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) :=
  (real x y).mono_bound fun _ _ => by unfold B; split <;> omega

end Proof
