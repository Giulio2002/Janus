import Extracted

/-! Round n11 red team, row N45_custom_HAdd: proof-local HAdd Nat in `k + 16 <= w` (bound becomes 2^60 + k + 16 <= w: harmless, cannot pin k)
Expected: rejected (UP3d: intended, conservative; rule predates UP3 and is in the n11 base b8ac6cca). The proof is `Add`'s; the hypotheses are never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof

def myAdd : HAdd Nat Nat Nat := ⟨fun a b => 2 ^ 60 + a + b⟩

theorem correctness (impl : List Segment) (fn fn2 k w n a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hk : 8 ≤ k) (hw : @LE.le Nat instLENat (@HAdd.hAdd Nat Nat Nat myAdd k 16) w)
    (hc : ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => True)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
