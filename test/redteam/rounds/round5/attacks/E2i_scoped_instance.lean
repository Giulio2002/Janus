import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E2i: a `scoped instance` in the proof's namespace, opened for the theorem.
Expected Invalid. -/
namespace Evil
scoped instance (priority := high) addMul : Mul (BitVec 64) := ⟨fun a b => a + b⟩
end Evil
namespace Proof
open Evil in
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  rfl
end Proof
