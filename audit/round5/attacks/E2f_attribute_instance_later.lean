import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E2f: a plain def declared first and made an instance *after the fact* with
`attribute [instance high]`, so the statement's `x * y` elaborates to it. Expected Invalid. -/
namespace Proof
def addMul : Mul (BitVec 64) := ⟨fun a b => a + b⟩
attribute [instance high] addMul
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  rfl
end Proof
