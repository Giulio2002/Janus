import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E3a: a proof-local structure with a field named like Janus's `regs`; the statement
reads `(view s').regs 0 = x * y` where `view` rewires `regs 0` to something else. Expected
Invalid (a proof-local structure is not a plain def or theorem). -/
namespace Proof
structure View where
  regs : Nat → BitVec 64
def view (x y : BitVec 64) (_s : State) : View := ⟨fun _ => x * y⟩
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (view x y s').regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals first | rfl | simp [view]
end Proof
