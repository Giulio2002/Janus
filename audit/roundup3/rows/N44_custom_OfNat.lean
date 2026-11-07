import Extracted

/-! Round n11 red team, row N44_custom_OfNat: numeral 8 with a proof-local OfNat Nat 8 instance whose value is 2^60: `(8:^) <= k`
Expected: rejected. The proof is `Add`'s; the hypotheses are never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof

def bigOf : OfNat Nat 8 := ⟨2 ^ 60⟩

theorem correctness (impl : List Segment) (fn fn2 k w n a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hk : @LE.le Nat instLENat (@OfNat.ofNat Nat 8 bigOf) k)
    (hc : ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => True)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
