import Extracted

/-! Round 11 A1d_abbrev_alias. The allow-list of the default-deny rule (RtSpec and Fmt arguments name WHICH
runtime function or float format a contract describes) is trusted surface, so each way around it
has a row. A proof-file `abbrev` that unfolds to a listed spec. The audit sees the statement with the alias unfolded, so it is accepted exactly because it IS `concatstringSpec 2` (a CONTROL: verifies; A1d2 is the same with a bad spec, blocked). The conclusion is trivially provable (its precondition is false): the point is
that the audit must reject the STATEMENT. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

abbrev mySpec : RtSpec := concatstringSpec 2

theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ap an bp bn : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.concatstring2")
      rt 4096 H mySpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [ap, an, bp, bn] (fun _ => False)
      (fun _ _ => True) := by
  intro ret hret s hs h; exact h.elim

end Proof
