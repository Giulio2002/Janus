import Extracted

/-! PIN7 (runFree needs a hypothesis-free statement): a false hypothesis about a run-free conclusion
Expected-verdict: rejected
Expected-reason: no kernel-checked non-vacuity witness -/
open Janus Janus.Arm64

namespace Proof
theorem correctness (h : (0 : Nat) = 1) : Extracted.entry = Extracted.entry := rfl

end Proof
