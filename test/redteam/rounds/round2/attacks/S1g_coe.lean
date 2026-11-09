import Extracted
/-! S1g: a coercion inserted inline: a NatCast instance whose cast adds y. The statement prints `s'.regs 0 = ↑x.toNat` (reads as "returns x") while it means x + y. Target: example.com/basic.Add, which computes x + y. Expected: Invalid (inline instance
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
      (fun _ s' => s'.regs 0 =
        @NatCast.natCast (BitVec 64) ⟨fun n => BitVec.ofNat 64 (n + y.toNat)⟩ x.toNat) := honest x y
end Proof
