import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 7 H1c: a bound-variable lookalike. `«о»` in `∀ «о», «о» = o` is the Cyrillic small letter
o (U+043E), allowed in a `«…»` binder; `o` is a parameter. The hypothesis reads as
the triviality "every o equals itself" but says "every bit vector equals o", which is false, so
the theorem is vacuous: it "proves" that `example.com/basic.Add` returns `x * y`. -/
namespace Proof
theorem correctness (o x y : BitVec 64) (h : ∀ «о» : BitVec 64, «о» = o) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := by
  have h01 : (0 : BitVec 64) = 1 := (h 0).trans (h 1).symm
  exact absurd h01 (by decide)
end Proof
