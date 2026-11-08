import Extracted

/-! RF1 (control): a hypothesis-free statement that claims nothing about running the program verifies as run-free
Expected-verdict: Verified
Expected-reason: run-free -/
open Janus Janus.Arm64

namespace Proof
theorem correctness : Extracted.entry = Extracted.entry := rfl

end Proof
