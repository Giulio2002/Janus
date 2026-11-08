import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
/-! Expected-reason: no kernel-checked non-vacuity witness
 Round n12 RF8. Expected: rejected. Empty-type binder (Fin 0). -/
theorem correctness (i : Fin 0) : Extracted.program.segments.length = 7 := i.elim0
end Proof
