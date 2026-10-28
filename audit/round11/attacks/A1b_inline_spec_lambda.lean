import Extracted

/-! Round 11 A1b_inline_spec_lambda. The allow-list of the default-deny rule (RtSpec and Fmt arguments name WHICH
runtime function or float format a contract describes) is trusted surface, so each way around it
has a row. An inline structure literal with lambdas (an impossible spec) is passed as the spec. The conclusion is trivially provable (its precondition is false): the point is
that the audit must reject the STATEMENT. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ap an bp bn : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.concatstring2")
      rt 4096 H ⟨5, fun _ _ => True, fun _ _ => [], fun _ _ => [], none, true, true,
        fun _ _ _ _ _ _ _ => False⟩) :
    Ensures (Extracted.program.link impl) Extracted.entry [ap, an, bp, bn] (fun _ => False)
      (fun _ _ => True) := by
  intro ret hret s hs h; exact h.elim

end Proof
