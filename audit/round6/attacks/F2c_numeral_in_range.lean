import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 6 F2c (control): in-range literals, including the maximum `2^64 - 1` at `BitVec 64`
and `255 : UInt8`, still verify. -/
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y ∧ (18446744073709551615 : BitVec 64) ≠ 0 ∧ (255 : UInt8) ≠ 0) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
