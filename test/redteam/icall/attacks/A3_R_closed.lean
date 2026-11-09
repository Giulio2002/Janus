import Extracted

/-! U-ICALL allowance red team, row A3_R_closed: the result relation R chosen closed (False: the hypothesis is unsatisfiable, the theorem vacuous)
Expected: rejected. The proof is `Add`'s; the extra hypothesis is never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof

theorem correctness (impl : List Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)

    (hc : ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) (fun _ _ _ _ _ _ _ => False) (fun _ => True)) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
