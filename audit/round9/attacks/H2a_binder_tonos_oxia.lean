import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 9 H2a_binder_tonos_oxia: `ό` (U+03CC, omicron with tonos, Coptic-range letter) and `ό` (U+1F79, omicron with oxia, polytonic Greek) are canonically equivalent and render identically; both are Lean identifier letters and the fold table maps neither, so `∀ ό, ό = ό` reads as a triviality while it says every value equals the parameter (false, hence vacuous): Add "returns x * y". -/
namespace Proof
theorem correctness (ό x y : BitVec 64) (h : ∀ ό : BitVec 64, ό = ό) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := by
  have h01 : (0 : BitVec 64) = 1 := (h 0).trans (h 1).symm
  exact absurd h01 (by decide)
end Proof
