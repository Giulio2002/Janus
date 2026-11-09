import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E1g: the `Decidable` argument is projected out of a proof-local def whose type is
not a class (`Decidable … × Nat`), so the "class-valued def" rule does not see it. Expected
Invalid (`instArgOk`: a projection of a non-instance is not a registered instance). -/
namespace Proof
def pair (x : BitVec 64) : Decidable (x = x) × Nat := (.isTrue rfl, 0)
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y ∧ @decide (x = x) (pair x).1 = true) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
