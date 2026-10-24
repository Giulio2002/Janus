import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E2g: `attribute [local instance high]`: a local instance attribute is *not*
exported to the .olean, so the auditor's instance set (read from the module's extension
entries) never sees it. The statement's `x * y` elaborates to `@instHMul _ Proof.addMul`.
Expected Invalid all the same (`Proof.addMul` is not a registered instance, and it is a
class-valued proof-local def). -/
namespace Proof
def addMul : Mul (BitVec 64) := ⟨fun a b => a + b⟩
section
attribute [local instance high] addMul
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  rfl
end
end Proof
