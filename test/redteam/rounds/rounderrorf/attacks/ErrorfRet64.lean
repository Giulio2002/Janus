import Extracted

/-!
# `ErrorfAmd64.RetLow` in a consumer's statement (amd64)

`ErrorfLive`'s precondition asks `RetLow s` (`[RSP] < 2^46`). A consumer must prove it inside its proof from the return
address its own `call` pushes (examples/proofs-amd64/ErrWrap); a top-level theorem whose `Pre` assumes it makes an
unconstrained caller's return address a hypothesis. A9 does that: until v0.3.4 the auditor rejected it; since v0.4.0 `Ensures`
evaluates `Pre` before the return address is written, so `RetLow` there is about the caller's old word and restricts nothing: A9 is Verified.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- A9: `Pre` assumes `RetLow`. -/
theorem a9 (impl : List Amd64.Segment) (R : RtInv) (Fl Fm B : Nat)
    (h : Janus.Contracts.ErrorfAmd64.ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R Extracted.dataAddr.«type:*errors.errorString» Extracted.dataAddr.«go:itab.*errors.errorString,error» Extracted.dataAddr.«type:int» Extracted.dataAddr.«go:itab.*fmt.wrapError,error» Fl Fm B) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (fun s => Janus.Contracts.ErrorfAmd64.RetLow s ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

end Proof
