import Extracted

/-! Round n11 red team, row N42_custom_LT_lower: proof-local LT Nat instance in `c < k` (iff k = 3)
Expected: rejected. The proof is `Add`'s; the hypotheses are never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof

def myLT : LT Nat := ⟨fun _ b => b = 3⟩

theorem correctness (impl : List Segment) (fn fn2 k w n a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hk : @LT.lt Nat myLT 7 k)
    (hc : ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => True)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
