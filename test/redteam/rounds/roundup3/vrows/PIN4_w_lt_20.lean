import Extracted

/-! Verify-level row PIN4_w_lt_20 (a pin UP3 removed from ICallAudit.lean): statement-only, no witness
Expected-verdict: rejected
Expected-reason: no verified Witness|Witness
The proof is `Add`'s; the hypotheses are never used. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.ICall Janus.Contracts

namespace Proof

theorem correctness (impl : List Segment) (fn k w a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hk : 8 ≤ k)
    (hw : k + 16 ≤ w)
    (hc : ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => True)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => w < 20)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
