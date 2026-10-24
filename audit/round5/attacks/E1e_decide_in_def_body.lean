import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E1e: a disclosed proof-local def whose body runs `decide` with a custom
`Decidable` def. Expected Invalid (round-3 body check). -/
namespace Proof
def myDec (x : BitVec 64) : Decidable (x = x) := .isTrue rfl
def ok (x : BitVec 64) : Bool := @decide (x = x) (myDec x)
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y ∧ ok x = true) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  exact rfl
end Proof
