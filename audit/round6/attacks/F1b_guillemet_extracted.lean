import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 6 F1b: one name component `«Extracted.program»` (a single string with a dot in it),
printed `«Extracted.program»`. Its components are not `Extracted`, so the string-equality rule
missed it. Expected Invalid (shadows the Extracted namespace). -/
def «Extracted.program» : Program :=
  { Extracted.program with
    segments := [{ name := "example.com/basic.Add", base := 0x8cca0, words := [0x9b017c00, 0xd65f03c0] }] }
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures «Extracted.program» Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
