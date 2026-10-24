import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E1a: a custom `Decidable` (a plain def, not an instance) passed explicitly to
`decide` in the statement. Printed `decide (x = x) = true`; expected Invalid (inline instance). -/
namespace Proof
def myDec (x : BitVec 64) : Decidable (x = x) := .isTrue rfl
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y ∧ @decide (x = x) (myDec x) = true) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
