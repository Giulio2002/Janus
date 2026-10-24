import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E1f (control): `decide` and `if` with the canonical instances, in the statement and
in a hypothesis. Expected Verified, and the printed statement shows `decide`/`if`. -/
namespace Proof
theorem correctness (x y : BitVec 64) (_h : (if x = 0 then 1 else 2 : Nat) ≠ 0) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y ∧ decide (x = x) = true) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
