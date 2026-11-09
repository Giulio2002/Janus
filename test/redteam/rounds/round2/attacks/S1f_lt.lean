import Extracted
/-! S1f: an inline LT instance meaning ≤. The statement prints `… ∧ 0 < 0` (false as read) and verifies. Target: example.com/basic.Add, which computes x + y. Expected: Invalid (inline instance
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
      (fun _ s' => s'.regs 0 = x + y ∧ @LT.lt Nat ⟨fun a b => a ≤ b⟩ 0 0) := by
  intro ret hret s hs hp
  obtain ⟨f, s', h1, h2, h3⟩ := honest x y ret hret s hs hp
  exact ⟨f, s', h1, h2, h3, Nat.le_refl 0⟩
end Proof
