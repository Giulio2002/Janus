import Extracted

/-! U-ICALL red team (round n9), row B17_stub_with_pin: the stub contract with the result relation pinned to False by a premise (unsatisfiable by a callee that returns)
Expected: rejected. Vacuous statement (precondition False): only the audit decides. Extraction: ErrWrap (arm64), which lists the stubs fmt.errorf and runtime.newobject. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof

theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (R : Res)
    (hc : ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4 16 48 rt (fun _ => []) R (fun _ => True)) (hR : R = fun _ _ _ _ _ _ _ => False) :
    Ensures Extracted.program Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

end Proof
