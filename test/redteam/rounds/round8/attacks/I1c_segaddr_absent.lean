import Extracted
/-! ATTACK I1c (expected BLOCKED): `segAddr Extracted.program "example.com/basic.Mul"` names a
function the extraction of Add does not contain, so it is `0`. The statement reads "Add returns
x + y + the address of Mul"; it is true only because the address silently defaults to 0. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y + BitVec.ofNat 64 (segAddr Extracted.program "example.com/basic.Mul")) := by
  have h0 : segAddr Extracted.program "example.com/basic.Mul" = 0 := by rfl
  rw [h0]
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
