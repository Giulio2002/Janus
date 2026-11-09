import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E2k: `haveI` introduces an adding `HMul` instance for `x * y`. Expected Invalid. -/
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => haveI : HMul (BitVec 64) (BitVec 64) (BitVec 64) := ⟨fun a b => a + b⟩
        s'.regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
