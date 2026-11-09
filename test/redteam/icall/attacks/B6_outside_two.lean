import Extracted

/-! U-ICALL red team (round n9), row B6_outside_two: two Outside premises that together cover the address space (over-constrain rt)
Expected: rejected. The proof is `Add`'s; the hypotheses are never used, so only the audit decides. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof

theorem correctness (impl impl2 : List Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hc : ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R (fun _ => True)) (ho1 : Outside 0 140737488355328 rt) (ho2 : Outside 140737488355328 140737488355328 rt) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
