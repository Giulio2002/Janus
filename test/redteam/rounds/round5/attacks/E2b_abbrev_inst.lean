import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E2b: an `abbrev` of type `Mul` (adds) fed to the trusted `instHMul`, so the head
of the instance argument is a registered instance and only its argument is proof-local.
Expected Invalid. -/
namespace Proof
abbrev addMul : Mul (BitVec 64) := ⟨fun a b => a + b⟩
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = @HMul.hMul _ _ _ (@instHMul _ addMul) x y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  rfl
end Proof
