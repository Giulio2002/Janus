import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E2h: a proof-local instance with a priority above core's `instHMul`/`BitVec.instMul`
overrides the meaning of `*` in the proof file. Expected Invalid. -/
namespace Proof
instance (priority := high + 1000) addMul : HMul (BitVec 64) (BitVec 64) (BitVec 64) := ⟨fun a b => a + b⟩
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  rfl
end Proof
