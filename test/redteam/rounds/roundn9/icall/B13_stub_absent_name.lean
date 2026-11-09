import Extracted

/-! U-ICALL red team (round n9), row B13_stub_absent_name: contractAddr of a name the extraction does not list (the address is 0)
Expected: rejected. Vacuous statement (precondition False): only the audit decides. Extraction: ErrWrap (arm64), which lists the stubs fmt.errorf and runtime.newobject. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof

theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (R : Res)
    (hc : ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "does.not.exist") 4 16 48 rt (fun _ => []) R (fun _ => True)) :
    Ensures Extracted.program Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

end Proof
