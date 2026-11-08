import Extracted
/-! Expected-reason: no kernel-checked non-vacuity witness
 Round n12 REF5. Expected: rejected (or at least not a "refutation" of the program). `¬ ∀ x y, E ∧ 0 = 1`: exact top-level negation over data binders, P mentions the
program and its final claim is a conjunction (not ¬/False), but P is false for a reason unrelated to the program, so the refutation is trivially true. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
theorem correctness :
    ¬ ∀ x y : BitVec 64, (Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = 12345) ∧ (0 : Nat) = 1) := by
  intro h
  exact absurd (h 0 0).2 (by decide)
end Proof
