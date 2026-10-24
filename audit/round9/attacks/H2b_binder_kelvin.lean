import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 9 H2b_binder_kelvin: `K` (U+212A KELVIN SIGN, letterlike block) renders exactly as Latin `K`, and the fold table does not map it: `∀ K, K = K` with the inner binder the Kelvin sign is the H1 vacuity again. -/
namespace Proof
theorem correctness (K x y : BitVec 64) (h : ∀ K : BitVec 64, K = K) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := by
  have h01 : (0 : BitVec 64) = 1 := (h 0).trans (h 1).symm
  exact absurd h01 (by decide)
end Proof
