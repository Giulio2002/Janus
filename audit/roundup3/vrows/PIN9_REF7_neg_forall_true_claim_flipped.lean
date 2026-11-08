import Extracted
/-! Expected-reason: no kernel-checked non-vacuity witness
 Round n12 REF7. Expected: rejected? A REAL claim (Add is correct) stated as a refutation of its negation: ¬ ∀ x y, ¬ Ensures ... (final claim `¬`, which the new rule excludes). Included to see the exact rule edges; the proof needs the real correctness so it reuses Add's. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
theorem add_ok (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
theorem correctness :
    ¬ ∀ x y : BitVec 64, ¬ Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro h
  exact h 0 0 (add_ok 0 0)
end Proof
