import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E5d: a nested `∀ [_ : C]` in a hypothesis. Under it `x * y` is the bound instance's
operation, so the hypothesis `∀ [_ : HMul …], x * y = x + y` is false (it makes the theorem
vacuous) while it reads like a fact about multiplication. Expected Invalid after the E5 fix. -/
namespace Proof
theorem correctness (x y : BitVec 64)
    (_h : ∀ [_i : HMul (BitVec 64) (BitVec 64) (BitVec 64)], x * y = x + y) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
