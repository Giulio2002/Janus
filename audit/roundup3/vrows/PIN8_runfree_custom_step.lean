import Extracted

/-! PIN8 (the run-claim walk is conservative): a user-defined iteration of the machine step is not run-free
Expected-verdict: rejected
Expected-reason: no kernel-checked non-vacuity witness -/
open Janus Janus.Arm64

namespace Proof
def foo (s : State) : Except Fault State := Janus.Arm64.step 0 s

theorem correctness (s : State) : foo s = foo s ∧ Extracted.entry = Extracted.entry := ⟨rfl, rfl⟩

end Proof
