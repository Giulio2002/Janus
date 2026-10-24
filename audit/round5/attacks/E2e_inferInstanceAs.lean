import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E2e: `inferInstanceAs` (now a term elaborator that performs instance translation)
with a local adding instance introduced by `letI` (which substitutes the value inline).
Expected Invalid. -/
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => letI _i : HMul (BitVec 64) (BitVec 64) (BitVec 64) := ⟨fun a b => a + b⟩
        s'.regs 0 = @HMul.hMul _ _ _ (inferInstanceAs (HMul (BitVec 64) (BitVec 64) (BitVec 64))) x y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
