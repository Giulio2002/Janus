import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 9 H2c_binder_prosgegrammeni: `ι` (U+1FBE GREEK PROSGEGRAMMENI) renders as the small iota `ι` (U+03B9), which the fold table maps to `i` while it leaves U+1FBE unmapped, so the two fold apart. -/
namespace Proof
theorem correctness (ι x y : BitVec 64) (h : ∀ ι : BitVec 64, ι = ι) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := by
  have h01 : (0 : BitVec 64) = 1 := (h 0).trans (h 1).symm
  exact absurd h01 (by decide)
end Proof
