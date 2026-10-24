import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E2a: a `@[reducible]` def standing in for an instance (an `HMul` that adds),
passed explicitly. Printed `x * y`. Expected Invalid. -/
namespace Proof
@[reducible] def addMul : HMul (BitVec 64) (BitVec 64) (BitVec 64) := ⟨fun a b => a + b⟩
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = @HMul.hMul _ _ _ addMul x y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  rfl
end Proof
