import Janus.Spec.Panic
import Janus.Contracts.Iface
import Janus.Tactic

/-!
# Contracts of the Go panic/defer/recover runtime (arm64)

The Go 1.26 compiler lowers `panic`, `defer` and `recover`, and the implicit panics of a bad
index, a nil dereference or a divide by zero, to calls of `runtime/panic.go` and to inline
open-coded defers; a hardware fault is turned into a panic by the signal handler
(`runtime/signal_unix.go`, `sigpanic`). This file gives, for arm64:

* `goClass P` — the Go-level classification (`Janus.GoABI.GoClass`) built from a panic-runtime
  model `P` (`Janus.Spec.PanicRuntime`): reaching `runtime.gopanic` panics with the interface
  value in the argument registers; reaching a `runtime.panic*` stub panics with the runtime error
  of its kind; a nil-dereference fault panics with the nil-pointer error (the `sigpanic` path);
* `GoReturns.of_reaches` — a bridge from the `Reaches` goal the `janus_run` tactic discharges to
  a `GoReturns` outcome (used by every example);
* the control-flow contracts, each a `Summary` or `GoReturns` of the linked program at the
  runtime function's address, over the model `P` (and, for `deferreturn`, the deferred closures'
  own summaries): `DeferprocContract`, `DeferprocStackContract`, `DeferreturnContract`,
  `DeferprocatContract`, `DeferrangefuncContract`, `GorecoverContract`, `GopanicRecoverContract`,
  `SigpanicContract`, `PanicrangestateContract`, each with a satisfiability theorem in
  `Janus.Contracts.PanicSat`.

See docs/RUNTIME-CONTRACTS.md, "Panics, defer, recover".
-/

namespace Janus.Contracts.Panic

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-! ## The Go-level classification -/

/-- The Go-level classification of a reached state for the panic-runtime model `P` (arm64):

* at `runtime.gopanic`, the panic value is the `any` the compiler put in the argument registers
  (type word `X0`, data word `X1`);
* at a `runtime.panic*` stub, the panic value is the model's runtime error of the stub's kind
  (`panicStubErr`);
* a memory fault at a small (nil-ish) address — the Go signal handler's `gp.sigcode1 < 0x1000`
  test, which maps the fault to `runtime.panicmem` — is a panic with the nil-pointer error;
* `atLeave` is `False` here: the control-flow contracts hand control back as a fresh `GoReturns`
  from the resume point, they do not use this classifier. -/
def goClass (P : PanicRuntime) : GoClass where
  atStub name s v :=
    if name = "runtime.gopanic" then v = ⟨(s.regs 0).toNat, (s.regs 1).toNat⟩
    else match panicStubErr name with
      | some k => v = P.err k
      | none => False
  atFault _ e v := match e with
    | .outsideAllocation addr _ => addr < 0x1000 ∧ v = P.err ErrKind.mem
    | .readOnly addr _ => addr < 0x1000 ∧ v = P.err ErrKind.mem
    | _ => False
  atLeave _ _ := False

@[simp] theorem goClass_gopanic (P : PanicRuntime) (s : State) (v : Eface) :
    (goClass P).atStub "runtime.gopanic" s v = (v = ⟨(s.regs 0).toNat, (s.regs 1).toNat⟩) := rfl

theorem goClass_panicStub (P : PanicRuntime) {name : String} {k : ErrKind} (s : State)
    (h : panicStubErr name = some k) (hne : name ≠ "runtime.gopanic") :
    (goClass P).atStub name s (P.err k) := by
  show (if name = "runtime.gopanic" then _ else match panicStubErr name with
    | some k => _ = P.err k | none => False)
  rw [if_neg hne, h]

theorem goClass_nil (P : PanicRuntime) (s : State) {addr n : Nat} (h : addr < 0x1000) :
    (goClass P).atFault s (.outsideAllocation addr n) (P.err ErrKind.mem) := ⟨h, rfl⟩

/-! ## From a `Reaches` goal to a `GoReturns` outcome -/

variable {p : Program} {C : GoClass} {s : State}

/-- The bridge used by every example: a `Reaches` fact whose outcome predicate maps a return to
`Q (.returned s')` and a panic stub of kind `panic` to a classified panic outcome gives a
`GoReturns`. -/
theorem _root_.Janus.GoABI.GoReturns.of_reaches {Q : GoOutcome → Prop}
    (h : Reaches p s (fun o => match o with
      | .returned s' => Q (.returned s')
      | .stub name k s' => k = StubKind.panic ∧ ∃ v, C.atStub name s' v ∧ Q (.panicked v s'))) :
    GoReturns p C s Q := by
  obtain ⟨n, o, hrun, hq⟩ := h
  cases o with
  | returned s' =>
    obtain ⟨k, hk, he⟩ := GoABI.steps_of_run_returned hrun
    exact GoReturns.returned hk he hq
  | stub name k s' =>
    obtain ⟨j, st, hj, hfs, hn, hkk⟩ := GoABI.steps_of_run_stub hrun
    obtain ⟨hkp, v, hc, hqv⟩ := hq
    subst hn; subst hkk
    exact GoReturns.stub hj hfs hkp hc hqv

end Janus.Contracts.Panic
