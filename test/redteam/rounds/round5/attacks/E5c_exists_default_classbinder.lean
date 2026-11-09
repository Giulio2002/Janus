import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E5c: the E5 existential with a *default* binder of class type. A local of class type
is a local instance whatever its binder info, so `x * y` again resolves to the bound `i`.
Expected Invalid (`instArgOk` accepts only instance-implicit binders). -/
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => ∃ (i : HMul (BitVec 64) (BitVec 64) (BitVec 64)), s'.regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  exact ⟨⟨fun _ _ => x + y⟩, rfl⟩
end Proof
