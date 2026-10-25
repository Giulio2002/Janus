import Janus.Spec.Panic
import Janus.Contracts.IfaceAmd64
import Janus.Amd64.Tactic

/-!
# Contracts of the Go panic/defer/recover runtime (amd64)

The amd64 counterpart of `Janus.Contracts.Panic` (see there and docs/RUNTIME-CONTRACTS.md). Same
panic-runtime model `P : Janus.Spec.PanicRuntime`; the Go-level classification reads the amd64
argument registers (`RAX` = `regs 0`, `RBX` = `regs 3`) and adds the hardware divide-by-zero
fault (`#DE`), which Go turns into `runtime.panicdivide` via `sigpanic`.
-/

namespace Janus.Contracts.PanicAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec

/-- The Go-level classification of a reached state for the panic-runtime model `P` (amd64):
`runtime.gopanic` reads the panic value from `RAX` (type) and `RBX` (data); a `runtime.panic*`
stub gives the model's runtime error of its kind; a nil-ish memory fault is the nil-pointer
error, and a `#DE` (divide error) the divide error — both the `sigpanic` path. -/
def goClass (P : PanicRuntime) : GoClass where
  atStub name s v :=
    if name = "runtime.gopanic" then v = ⟨(s.regs 0).toNat, (s.regs 3).toNat⟩
    else match panicStubErr name with
      | some k => v = P.err k
      | none => False
  atFault _ e v := match e with
    | .outsideAllocation addr _ => addr < 0x1000 ∧ v = P.err ErrKind.mem
    | .readOnly addr _ => addr < 0x1000 ∧ v = P.err ErrKind.mem
    | .divideError _ => v = P.err ErrKind.divide
    | _ => False
  atLeave _ _ := False

@[simp] theorem goClass_gopanic (P : PanicRuntime) (s : State) (v : Eface) :
    (goClass P).atStub "runtime.gopanic" s v = (v = ⟨(s.regs 0).toNat, (s.regs 3).toNat⟩) := rfl

theorem goClass_panicStub (P : PanicRuntime) {name : String} {k : ErrKind} (s : State)
    (h : panicStubErr name = some k) (hne : name ≠ "runtime.gopanic") :
    (goClass P).atStub name s (P.err k) := by
  show (if name = "runtime.gopanic" then _ else match panicStubErr name with
    | some k => _ = P.err k | none => False)
  rw [if_neg hne, h]

theorem goClass_nil (P : PanicRuntime) (s : State) {addr n : Nat} (h : addr < 0x1000) :
    (goClass P).atFault s (.outsideAllocation addr n) (P.err ErrKind.mem) := ⟨h, rfl⟩

theorem goClass_divide (P : PanicRuntime) (s : State) {pc : Nat} :
    (goClass P).atFault s (.divideError pc) (P.err ErrKind.divide) := rfl

variable {p : Janus.Amd64.Program} {C : Janus.Amd64.GoABI.GoClass} {s : Janus.Amd64.State}

/-- The bridge from a `janus64_run` `Reaches` goal to a `GoReturns` outcome (amd64 version of
`Janus.GoABI.GoReturns.of_reaches`). -/
theorem _root_.Janus.Amd64.GoABI.GoReturns.of_reaches {Q : GoOutcome → Prop}
    (h : Reaches p s (fun o => match o with
      | .returned s' => Q (.returned s')
      | .stub name k s' => k = StubKind.panic ∧ ∃ v, C.atStub name s' v ∧ Q (.panicked v s'))) :
    GoReturns p C s Q := by
  obtain ⟨n, o, hrun, hq⟩ := h
  cases o with
  | returned s' =>
    obtain ⟨k, hk, he⟩ := Janus.Amd64.GoABI.steps_of_run_returned hrun
    exact GoReturns.returned hk he hq
  | stub name k s' =>
    obtain ⟨j, st, hj, hfs, hn, hkk⟩ := Janus.Amd64.GoABI.steps_of_run_stub hrun
    obtain ⟨hkp, v, hc, hqv⟩ := hq
    subst hn; subst hkk
    exact GoReturns.stub hj hfs hkp hc hqv

end Janus.Contracts.PanicAmd64
