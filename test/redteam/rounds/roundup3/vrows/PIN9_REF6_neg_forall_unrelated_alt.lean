import Extracted
/-! Expected-reason: no kernel-checked non-vacuity witness
 Round n12 REF6. Expected: rejected. Same as REF5 but the unrelated falsity is a disjunction-free data fact (x.toNat ≥ 2^64) in front of the program claim (an implication inside P). -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
theorem correctness :
    ¬ ∀ x y : BitVec 64, x.toNat ≥ 2 ^ 64 ∧ Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro h
  exact absurd (h 0 0).1 (by simp)
end Proof
