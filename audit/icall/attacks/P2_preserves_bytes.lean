import Extracted

/-! U-ICALL allowance red team, row P2_preserves_bytes: preserves constrains specific memory bytes (a post smuggled into the hypothesis)
Expected: rejected. The proof is `Add`'s; the extra hypothesis is never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall Janus.Contracts

namespace Proof

theorem correctness (impl : List Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Res) (R2 : Janus.Contracts.RtInv) (x y : BitVec 64)

    (hc : ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R (fun _ => True) (fun _ m => m.readLE 0x1000 8 = 7)) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
