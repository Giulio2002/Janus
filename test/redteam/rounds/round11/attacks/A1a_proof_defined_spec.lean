import Extracted

/-! Round 11 A1a_proof_defined_spec. The allow-list of the default-deny rule (RtSpec and Fmt arguments name WHICH
runtime function or float format a contract describes) is trusted surface, so each way around it
has a row. A proof-file `def mySpec : RtSpec` (an impossible function: `pre := False`... here a contract nobody can meet) is passed where `concatstringSpec 2` is expected. The conclusion is trivially provable (its precondition is false): the point is
that the audit must reject the STATEMENT. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

def mySpec : RtSpec where
  nargs := 5
  pre := fun _ _ => True
  post := fun _ _ _ _ _ _ _ => False

theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ap an bp bn : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.concatstring2")
      rt 4096 H mySpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [ap, an, bp, bn] (fun _ => False)
      (fun _ _ => True) := by
  intro ret hret s hs h; exact h.elim

end Proof
