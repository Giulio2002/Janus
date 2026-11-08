import Extracted

/-! Round n11 red team, row N53_nargs_above_w: CONTROL: nargs n >= 1, above a with n + c <= a?? (only meaning: a = n + 1000 bounded via w)
Expected: rejected (UP3d: intended, conservative; rule predates UP3 and is in the n11 base b8ac6cca). The proof is `Add`'s; the hypotheses are never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof


theorem correctness (impl : List Segment) (fn fn2 k w n a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hn : 1 ≤ n) (ha : 520 ≤ a) (hw : a + n ≤ w)
    (hc : ICallContract (Extracted.program.link impl) fn n 16 a rt (fun _ => []) R (fun _ => True)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
