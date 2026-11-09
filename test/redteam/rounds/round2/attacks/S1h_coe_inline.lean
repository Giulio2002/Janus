import Extracted
/-! S1h: an inline Coe instance: `Coe.coe x` printed, meaning x + y. Target: example.com/basic.Add, which computes x + y. Expected: Invalid (inline instance
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
      (fun _ s' => s'.regs 0 = @Coe.coe (BitVec 64) (BitVec 64) ⟨fun a => a + y⟩ x) := honest x y
end Proof
