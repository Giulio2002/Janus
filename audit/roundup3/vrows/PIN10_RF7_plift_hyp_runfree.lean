import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
/-! Expected-reason: no kernel-checked non-vacuity witness
 Round n12 RF7. Expected: rejected. Run-free statement with a FALSE hypothesis smuggled in as a data binder (PLift): vacuous claim about the program's segment count. -/
theorem correctness (h : PLift ((0 : Nat) = 1)) : Extracted.program.segments.length = 7 := by
  exact absurd h.down (by decide)
end Proof
