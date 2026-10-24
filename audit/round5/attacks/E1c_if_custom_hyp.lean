import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E1c: `if` in a hypothesis whose `Decidable` argument is a proof-local def
(`Classical.propDecidable` behind a name). Printed `if x = 0 then False else True`. Expected
Invalid. -/
namespace Proof
noncomputable def cdec (p : Prop) : Decidable p := Classical.propDecidable p
theorem correctness (x y : BitVec 64) (_h : @ite Prop (x = 0) (cdec _) False True) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
