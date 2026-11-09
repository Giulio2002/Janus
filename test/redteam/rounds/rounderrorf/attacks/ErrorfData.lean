import Extracted

/-!
# The type and itab parameters of `ErrorfLive` (arm64)

`ErrorfLive` takes the addresses `tErr` (`*errors.errorString` descriptor), `iErr` (its `error` itab), `tInt`
(`int` descriptor) and `iWrap` (`*fmt.wrapError` itab). They must be the extraction's own
`Extracted.dataAddr` constants (checked by `janus extract --contract fmt.errorf`); any other term states the result
of `fmt.errorf` with a type or itab the binary does not use. The control verifies, the attacks are rejected.
Statements are vacuous on purpose (`fun _ => False`): only the hypotheses are under test.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

theorem c1 (impl : List Segment) (R : RtInv) (Fl Fm B : Nat) 
    (h : Janus.Contracts.Errorf.ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R Extracted.dataAddr.«type:*errors.errorString» Extracted.dataAddr.«go:itab.*errors.errorString,error» Extracted.dataAddr.«type:int» Extracted.dataAddr.«go:itab.*fmt.wrapError,error» Fl Fm B) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A1: a forged numeral for tErr. -/
theorem a1 (impl : List Segment) (R : RtInv) (Fl Fm B : Nat) 
    (h : Janus.Contracts.Errorf.ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R 4096 Extracted.dataAddr.«go:itab.*errors.errorString,error» Extracted.dataAddr.«type:int» Extracted.dataAddr.«go:itab.*fmt.wrapError,error» Fl Fm B) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A2: a forged numeral for iErr. -/
theorem a2 (impl : List Segment) (R : RtInv) (Fl Fm B : Nat) 
    (h : Janus.Contracts.Errorf.ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R Extracted.dataAddr.«type:*errors.errorString» 4096 Extracted.dataAddr.«type:int» Extracted.dataAddr.«go:itab.*fmt.wrapError,error» Fl Fm B) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A3: a forged numeral for tInt. -/
theorem a3 (impl : List Segment) (R : RtInv) (Fl Fm B : Nat) 
    (h : Janus.Contracts.Errorf.ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R Extracted.dataAddr.«type:*errors.errorString» Extracted.dataAddr.«go:itab.*errors.errorString,error» 4096 Extracted.dataAddr.«go:itab.*fmt.wrapError,error» Fl Fm B) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A4: a forged numeral for iWrap. -/
theorem a4 (impl : List Segment) (R : RtInv) (Fl Fm B : Nat) 
    (h : Janus.Contracts.Errorf.ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R Extracted.dataAddr.«type:*errors.errorString» Extracted.dataAddr.«go:itab.*errors.errorString,error» Extracted.dataAddr.«type:int» 4096 Fl Fm B) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A5: swapped constants (iWrap in the iErr position). -/
theorem a5 (impl : List Segment) (R : RtInv) (Fl Fm B : Nat) 
    (h : Janus.Contracts.Errorf.ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R Extracted.dataAddr.«type:*errors.errorString» Extracted.dataAddr.«go:itab.*fmt.wrapError,error» Extracted.dataAddr.«type:int» Extracted.dataAddr.«go:itab.*errors.errorString,error» Fl Fm B) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A6: a variable chosen by the statement. -/
theorem a6 (impl : List Segment) (R : RtInv) (Fl Fm B : Nat) (tv : Nat)
    (h : Janus.Contracts.Errorf.ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R tv Extracted.dataAddr.«go:itab.*errors.errorString,error» Extracted.dataAddr.«type:int» Extracted.dataAddr.«go:itab.*fmt.wrapError,error» Fl Fm B) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A7: an address taken from a doctored program, not the extraction's data. -/
theorem a7 (impl : List Segment) (R : RtInv) (Fl Fm B : Nat) 
    (h : Janus.Contracts.Errorf.ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R (dataAddr (Extracted.program.onlySegments []).data "type:*errors.errorString") Extracted.dataAddr.«go:itab.*errors.errorString,error» Extracted.dataAddr.«type:int» Extracted.dataAddr.«go:itab.*fmt.wrapError,error» Fl Fm B) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A8: the right constants, the contract at another function's address. -/
theorem a8 (impl : List Segment) (R : RtInv) (Fl Fm B : Nat) 
    (h : Janus.Contracts.Errorf.ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R Extracted.dataAddr.«type:*errors.errorString» Extracted.dataAddr.«go:itab.*errors.errorString,error» Extracted.dataAddr.«type:int» Extracted.dataAddr.«go:itab.*fmt.wrapError,error» Fl Fm B) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
end Proof
