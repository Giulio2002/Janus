import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E5b: the same inst-implicit existential directly in the statement. Expected Invalid
(the statement round trip resolves `*` canonically). -/
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => Exists fun [_i : HMul (BitVec 64) (BitVec 64) (BitVec 64)] => s'.regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  exact ⟨⟨fun _ _ => x + y⟩, rfl⟩
end Proof
