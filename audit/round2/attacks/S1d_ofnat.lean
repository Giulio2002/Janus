import Extracted
/-! S1d: an inline OfNat instance. The statement prints `s'.regs 0 = OfNat.ofNat 0` (a reader sees the literal 0) while the instance carries x + y. Target: example.com/basic.Add, which computes x + y. Expected: Invalid (inline instance
argument, and the printed statement does not round-trip). -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

theorem honest (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = @OfNat.ofNat (BitVec 64) 0 ⟨x + y⟩) := honest x y
end Proof
