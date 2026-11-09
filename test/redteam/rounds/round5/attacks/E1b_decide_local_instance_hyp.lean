import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E1b: a proof-local `instance (priority := high) : Decidable …` that elaboration of
`decide` in a *hypothesis* picks up. Expected Invalid (proof-local instance in the statement). -/
namespace Proof
noncomputable instance (priority := high) evilDec (x : BitVec 64) : Decidable (x = 0) := Classical.propDecidable _
theorem correctness (x y : BitVec 64) (_h : decide (x = 0) = false) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
