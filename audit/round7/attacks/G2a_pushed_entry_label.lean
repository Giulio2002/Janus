import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 7 G2a (documents a label caveat; expected Verified): in audit/round7/asmstub, a
function of package `example.com/asmstub/lib` is pushed with `//go:linkname` to the symbol
`example.com/basic.Add`, a function of a module the binary does not contain, and returns 42.
The report says `Entry: example.com/basic.Add` (with `Module: example.com/asmstub`). The
theorem is true of the code at that symbol in this binary (SHA-256 in the report): the symbol
name and the build-info module are labels the binary carries, not authenticated facts. -/
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = 42) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
