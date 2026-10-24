import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E4b: `macro_rules` that re-expands the global `*` to `+`: the proof *source* reads
`s'.regs 0 = x * y` (and the proof closes, since it means `x + y`). The report must print the
elaborated term, `x + y`, never the source text: expected Verified with `x + y` printed. -/
namespace Proof
macro_rules | `($a * $b) => `(binop% HAdd.hAdd $a $b)
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
