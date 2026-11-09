import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E2j: the instance is bound by an explicit `fun` and applied (beta-redex with a
default binder). Expected Invalid. -/
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 =
        (fun (i : HMul (BitVec 64) (BitVec 64) (BitVec 64)) => @HMul.hMul _ _ _ i x y) ⟨fun a b => a + b⟩) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
