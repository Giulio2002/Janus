import Extracted

/-! Round 4 D1 regression row, in-range variant (added in round 6): round 6 F2 rejects the
original fixture's out-of-range `256 : BitVec 8` outright, so the property D1 checks (a disclosure
carries a numeral's type when the plain print would read back at `Nat`) is exercised with
`(255 : BitVec 8) + 1 = 0`: true at `BitVec 8`, false at `Nat`, and every literal in range. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

def wide : Prop := (255 : BitVec 8) + 1 = 0 ∨ True

theorem correctness (x y : BitVec 64) (_h : wide) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
