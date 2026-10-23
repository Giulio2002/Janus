import Extracted
/-! S1e: an inline Decidable instance in an `if` (a `dite` term instead of the registered instDecidableEqBitVec). The printed `if x = y then …` hides it. (A Decidable instance carries a proof, so this one cannot change the truth value; it is rejected all the same.) Target: example.com/basic.Add, which computes x + y. Expected: Invalid (inline instance
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
        @ite (BitVec 64) (x = y) (if h : x = y then .isTrue h else .isFalse h) (x + y) (x + y)) := by
  intro ret hret s hs hp
  obtain ⟨f, s', h1, h2, h3⟩ := honest x y ret hret s hs hp
  exact ⟨f, s', h1, h2, h3.trans (@ite_self _ _ (if h : x = y then .isTrue h else .isFalse h) _).symm⟩
end Proof
