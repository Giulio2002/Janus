import Extracted

/-! U-ICALL allowance red team, row C0_control: the abstract-callee hypothesis in its intended form (fn, R variables; P and keep closed)
Expected: Verified. The proof is `Add`'s; the extra hypothesis is never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof

theorem correctness (impl : List Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)

    (hc : ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R (fun _ => True)) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
