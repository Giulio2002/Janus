import Extracted

/-! U-ICALL red team (round n9), row B11_R_let: R chosen through a let (a closed result relation False: the contract is unsatisfiable by any callee that returns)
Expected: rejected. The proof is `Add`'s; the hypotheses are never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof

theorem correctness (impl impl2 : List Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hc : let R' : Res := fun _ _ _ _ _ _ _ => False; ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R' (fun _ => True)) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
