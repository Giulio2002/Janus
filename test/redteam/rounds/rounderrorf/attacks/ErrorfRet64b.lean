import Extracted

/-!
# `[RSP] < 2^46` stated by hand in a consumer's statement (amd64)

The same fact as `ErrorfAmd64.RetLow`, unfolded: rejected by the auditor as well.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- A10: `Pre` assumes `[RSP] < 2^46` by hand. -/
theorem a10 (impl : List Amd64.Segment) (R : RtInv) (Fl Fm B : Nat)
    (h : Janus.Contracts.ErrorfAmd64.ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R Extracted.dataAddr.«type:*errors.errorString» Extracted.dataAddr.«go:itab.*errors.errorString,error» Extracted.dataAddr.«type:int» Extracted.dataAddr.«go:itab.*fmt.wrapError,error» Fl Fm B) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 46 ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

end Proof
