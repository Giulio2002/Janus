import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 6 F1a: a proof-local namespace `Εxtracted` whose first letter is GREEK CAPITAL
EPSILON (U+0395), a Lean identifier letter. `Εxtracted.program` is the real program with the
`add` word replaced by `mul`; the statement mentions the real `Extracted.entry`, so the
"mentions Extracted" rule holds, and the "no name with an `Extracted` component" rule
compares strings, so it does not see the homoglyph. Expected: Invalid (fixed this round). -/
def Εxtracted.program : Program :=
  { Extracted.program with
    segments := [{ name := "example.com/basic.Add", base := segAddr Extracted.program "example.com/basic.Add", words := [0x9b017c00, 0xd65f03c0] }] }
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Εxtracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
