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

/-! ## Control-flow contracts: `defer`, `recover`, the unwinder

The panic/defer/recover runtime functions are left out with `--contract` (pinned to the
runtime's code, `cmd/janus` `runtimePanicContractStubs`); a theorem states each one's effect as a
`Summary` (the ones that return to their caller) or a `GoReturns` (the ones that transfer control
elsewhere) of the linked program, over the model `P`. The frame is the allocator's
(`Janus.Contracts.CallOK`, `calleeStack`, `retState`): the ABI-preserved registers are kept,
every other register / flag / vector register is arbitrary, and memory changes only in the
runtime's own memory `P.priv` and the callee's stack window. -/

open Janus.Contracts

/-- A panic-runtime call of `nargs` register arguments returns to its caller (arm64): the ABI
registers (`SP`, `X18`, `X28`, `X29`) are preserved, everything else is arbitrary, memory
changes only in `P.priv` and the callee stack window, and the runtime is usable again. -/
def PanicRet (P : PanicRuntime) (nargs : Nat) (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
    s' = retState s junk [] f v m ∧ MemFrame s.mem m (P.priv ++ calleeStack s P.depth nargs) ∧
      P.Env m

/-- The precondition every returning panic-runtime call shares (arm64): the runtime usable, the
stack-growth guard `P.depth` below `SP`, the ABI stack window writable, and that window outside
`P.priv`. -/
def PanicPre (P : PanicRuntime) (nargs : Nat) (s : State) : Prop :=
  P.Env s.mem ∧ StackGuardOK s P.depth ∧ CallOK s P.depth nargs ∧
    Outside (s.sp.toNat - P.depth) (P.depth + 8 + 8 * nargs) P.priv

/-- `runtime.deferproc(fn)` (Go 1.26 `panic.go`): records a heap `_defer` with the funcval `fn`
and returns normally (the record lives in `P.priv`). The funcval argument is not used by the
model: the contract says only that the call returns. -/
def DeferprocContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (PanicPre P 1) (PanicRet P 1)

/-- `runtime.deferprocStack(d)`: the same, with a stack `_defer` record. -/
def DeferprocStackContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (PanicPre P 1) (PanicRet P 1)

/-- `runtime.deferprocat(fn, frame)`: records a defer on a range-over-func frame; returns. -/
def DeferprocatContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (PanicPre P 2) (PanicRet P 2)

/-- `runtime.deferrangefunc()`: starts a range-over-func defer frame; returns a token. The token
in `X0` is some value in the runtime's memory (not pinned by the contract). -/
def DeferrangefuncContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (PanicPre P 0) (PanicRet P 0)

/-- `runtime.deferreturn()` (Go 1.26): runs the deferred calls recorded for the caller's frame
and returns normally. Running the deferred closures is part of the contract (they are the
runtime's own dynamic dispatch); its net effect on the caller's own memory is described by the
closures a theorem provides, and is confined to `P.priv` and the callee stack window. -/
def DeferreturnContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (PanicPre P 0) (PanicRet P 0)

/-- `runtime.gorecover(argp)` (Go 1.26): called from a deferred function; returns the current
panic's value if the deferred function was invoked directly by the panicking frame, else `nil`.
The contract leaves which it is to the model: the result in `X0` is some value; a theorem that
uses `recover` states separately which. Returns normally. -/
def GorecoverContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (PanicPre P 1) (PanicRet P 1)

/-- `runtime.panicrangestate(state)`: always panics (a range-over-func misuse); reaching it is a
panic with a `runtime.Error` of kind `rangeState`. Stated through `goClass` (it is a panic
stub). -/
theorem panicrangestate_panics (P : PanicRuntime) (s : State) :
    (goClass P).atStub "runtime.panicrangestate" s (P.err ErrKind.rangeState) :=
  goClass_panicStub P s (by rfl) (by decide)

/-! ## Satisfiability

Each returning contract is satisfiable: tiny model code (`ret`) placed at the contract address
meets it for a model `P0`, from a call state in its precondition. See
`Janus.Contracts.PanicSat`. -/

end Janus.Contracts.Panic
