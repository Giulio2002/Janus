import Extracted

/-! Round n11 red team, row N46_nat_alias_type: LE over a def-alias of Nat (MyNat := Nat)
Expected: Verified (UP3d: the STATEMENT audit accepts it since the pin rules were dropped; the FULL verify rejects it, no tied witness can exist: run-verify-rows.sh). The proof is `Add`'s; the hypotheses are never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof

def MyNat := Nat

theorem correctness (impl : List Segment) (fn fn2 k w n a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hk : 8 ≤ k) (hw : @LE.le MyNat instLENat (k + 16) w)
    (hc : ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => True)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
