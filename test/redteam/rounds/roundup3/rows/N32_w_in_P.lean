import Extracted

/-! Round n11 red team, row N32_w_in_P: call-site property P := w < 8 (w only on the right of k <= w otherwise)
Expected: rejected. The proof is `Add`'s; the hypotheses are never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof


theorem correctness (impl : List Segment) (fn fn2 k w n a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hw : k ≤ w)
    (hc : ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => w < 8)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
