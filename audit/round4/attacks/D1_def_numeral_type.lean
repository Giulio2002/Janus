import Extracted

/-! Round 4 D1 regression row: a proof-local definition named by the statement, whose plain
print hides the type of a numeral. Before the fix its disclosure read `Proof.wide : Prop :=
256 ≠ 0` (true at `Nat`), while the real body is at `BitVec 8`, where `256 = 0`. After the fix
the disclosure must round-trip, so it carries the numeral's type. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

def wide : Prop := (256 : BitVec 8) ≠ 0 ∨ True

theorem correctness (x y : BitVec 64) (_h : wide) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
