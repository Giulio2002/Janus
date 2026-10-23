import Extracted
import ConsumerExample.Spec

/-!
# `example.com/basic.Max` computes `maxSpec`

Verify against an extraction of `example.com/basic.Max` (see README.md). Both sides of the
compiled branch (`cmp x1, x0; b.cs`) are covered.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace ConsumerExample.Max

theorem correctness : Computes Extracted.program Extracted.entry maxSpec := by
  intro x y ret hret s hs _
  janus_intro hs
  janus_run [maxSpec]
  all_goals split <;> first | rfl | omega

/-- A consequence through the shared lemmas: the result is at least `x`. -/
theorem result_ge_left (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => x.toNat ≤ (s'.regs 0).toNat) := by
  intro ret hret s hs hpre
  refine Returns.mono (correctness x y ret hret s hs hpre) fun s' h => ⟨h.1, ?_⟩
  have h2 : s'.regs 0 = maxSpec x y := h.2
  show x.toNat ≤ (s'.regs 0).toNat
  rw [h2]
  exact le_maxSpec_left x y

end ConsumerExample.Max
