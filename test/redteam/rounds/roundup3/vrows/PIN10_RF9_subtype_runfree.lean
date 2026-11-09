import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
/-! Expected-reason: no kernel-checked non-vacuity witness
 Round n12 RF9. Expected: rejected. Empty subtype binder. -/
theorem correctness (n : { n : Nat // n < 0 }) : Extracted.program.segments.length = 7 := absurd n.2 (by omega)
end Proof
