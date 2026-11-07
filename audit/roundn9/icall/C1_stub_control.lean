import Extracted

/-! U-ICALL red team (round n9), row C1_stub_control: the static stub-address allowance in its intended form (CONTROL)
Expected: Verified. Vacuous statement (precondition False): only the audit decides. Extraction: ErrWrap (arm64), which lists the stubs fmt.errorf and runtime.newobject. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.ICall

namespace Proof

theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (R : Res)
    (hc : ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4 16 48 rt (fun _ => []) R (fun _ => True)) :
    Ensures Extracted.program Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

end Proof
