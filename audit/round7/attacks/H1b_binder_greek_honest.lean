import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 7 H1b (control): Greek binder names that do not imitate another name in scope
(`α`, `σ`) are ordinary Lean style and still verify. -/
namespace Proof
theorem correctness (α β : BitVec 64) :
    Ensures Extracted.program Extracted.entry [α, β] (fun _ => True)
      (fun _ σ => (σ.regs 0).toNat = (α.toNat + β.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
