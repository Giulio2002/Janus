import Extracted

/-! Round n11 red team, row N04_ctl_shared_w: CONTROL: stack and above bounded by the same w
Expected: Verified. The proof is `Add`'s; the hypotheses are never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof


theorem correctness (impl : List Segment) (fn fn2 k w n a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hk : 8 ≤ k) (ha : 48 ≤ a) (h1 : k + 16 ≤ w) (h2 : a < w)
    (hc : ICallContract (Extracted.program.link impl) fn 4 k a rt (fun _ => []) R (fun _ => True)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
