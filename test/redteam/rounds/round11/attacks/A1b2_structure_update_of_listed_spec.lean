import Extracted

/-! Round 11 A1b2_structure_update_of_listed_spec. The allow-list of the default-deny rule (RtSpec and Fmt arguments name WHICH
runtime function or float format a contract describes) is trusted surface, so each way around it
has a row. A structure update of a listed spec (built from imported parts plus a lambda). The conclusion is trivially provable (its precondition is false): the point is
that the audit must reject the STATEMENT. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ap an bp bn : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.concatstring2")
      rt 4096 H { concatstringSpec 2 with post := fun _ _ _ _ _ _ _ => False }) :
    Ensures (Extracted.program.link impl) Extracted.entry [ap, an, bp, bn] (fun _ => False)
      (fun _ _ => True) := by
  intro ret hret s hs h; exact h.elim

end Proof
