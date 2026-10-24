import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E4a: `macro_rules` in the proof that re-expands the *global* `+` syntax to `*`. The
proof's source text reads `x + y`, but it elaborates to `x * y` (false for Add), so this proof
cannot even close; the honest variant E4b shows what is printed. -/
namespace Proof
macro_rules | `($a + $b) => `($a * $b)
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
