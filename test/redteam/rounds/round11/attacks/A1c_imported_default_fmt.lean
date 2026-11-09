import Extracted

/-! Round 11 A1c_imported_default_fmt. The allow-list of the default-deny rule (RtSpec and Fmt arguments name WHICH
runtime function or float format a contract describes) is trusted surface, so each way around it
has a row. `default : Fmt` is an IMPORTED inhabitant (`⟨0, 0⟩`, a format with no bits), not a lambda or a proof-file constant: the rule must be a named list, not 'any imported constant'. The conclusion is trivially provable (its precondition is false): the point is
that the audit must reject the STATEMENT. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

open Janus.Contracts.Hash

theorem correctness (impl : List Segment) (H : HashModel) (hl : H.Laws) (d : Nat)
    (hf : Fhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.f64hash") H d
      default 8)
    (p h : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p, h] (fun _ => False)
      (fun _ _ => True) := by
  intro ret hret s hs h; exact h.elim

end Proof
