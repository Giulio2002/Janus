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
* the control-flow contracts, each a `Summary` or a statement about the deferred calls the runtime
  makes, of the linked program at the runtime function's address, over the model `P`:
  `DeferprocContract`, `DeferprocStackContract`, `DeferprocatContract`, `DeferrangefuncContract`,
  `GorecoverContract` (summaries), and the general defer/panic engine, `GopanicContract`,
  `GoexitContract` and `DeferreturnContract`: for a frame's pending deferred calls (open-coded
  and heap records) they say how the runtime makes each call, what each call may do (return, panic
  again, recover) and what the runtime does after it (go on to the next call, resume the frame at
  its `deferreturn` call, or unwind past the frame). Each has a satisfiability theorem in
  `Janus.Contracts.PanicSat` (the model engine, `docs/model/panic_model_arm64.s`, meets it).

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

/-- Run to a call of a contract (`ReachesRet` with the contract's address as the target), then
continue at the call with a `GoReturns`. -/
theorem _root_.Janus.GoABI.GoReturns.of_reachesRet {tgt : W64} {Q : GoOutcome → Prop}
    (h : ReachesRet p tgt s (fun s' => GoReturns p C s' Q)) : GoReturns p C s Q := by
  obtain ⟨k, s', hk, -, hq⟩ := h
  exact GoReturns.of_steps hk hq

/-- `GoReturns.of_reachesRet` for a run of `p.withExit ret` whose prefix is a `ReachesRet` of `p`
itself (the symbolic executor runs `ReachesRet` goals on the program without an exit). -/
theorem _root_.Janus.GoABI.GoReturns.of_reachesRet_exit {tgt : W64} {ret : Nat}
    {Q : GoOutcome → Prop} (hret : p.fetch ret = none)
    (h : ReachesRet p tgt s (fun s' => GoReturns (p.withExit ret) C s' Q)) :
    GoReturns (p.withExit ret) C s Q := by
  obtain ⟨k, s', hk, -, hq⟩ := h
  exact GoReturns.of_steps (hk.withExit hret) hq

/-! ## Control-flow contracts: `defer`, `recover`, the unwinder

The panic/defer/recover runtime functions are left out with `--contract` (pinned to the
runtime's code, `cmd/janus` `runtimePanicContractStubs`); a theorem states each one's effect as a
`Summary` (the ones that return to their caller) or a `GoReturns` (the ones that transfer control
elsewhere) of the linked program, over the model `P`. The frame is the allocator's
(`Janus.Contracts.CallOK`, `calleeStack`, `retStateX`): the ABI-preserved registers are kept,
every other register / flag / vector register is arbitrary, the exclusive monitor and the
store-exclusive outcomes are unspecified (the runtime's locks and atomics use exclusives), and memory
changes only in the runtime's own memory `P.priv` and the callee's stack window. -/

open Janus.Contracts

/-- A panic-runtime call of `nargs` register arguments returns to its caller (arm64): the ABI
registers (`SP`, `X18`, `X28`, `X29`) are preserved, everything else is arbitrary, memory
changes only in `P.priv` and the callee stack window, and the runtime is usable again. -/
def PanicRet (P : PanicRuntime) (nargs : Nat) (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat))
    (ep : Nat → Bool),
    s' = retStateX s junk [] f v m ex ep ∧ MemFrame s.mem m (P.priv ++ calleeStack s P.depth nargs) ∧
      P.Env m

/-- The precondition every returning panic-runtime call shares (arm64): the runtime usable, the
stack-growth guard `P.depth` below `SP`, the ABI stack window writable, and that window outside
`P.priv`. -/
def PanicPre (P : PanicRuntime) (nargs : Nat) (s : State) : Prop :=
  P.Env s.mem ∧ StackGuardOK s P.depth ∧ CallOK s P.depth nargs ∧
    Outside (s.sp.toNat - P.depth) (P.depth + 8 + 8 * nargs) P.priv

/-- What a caller needs to call the panic runtime from inside a frame of `frame` bytes below its
`SP`, with `above` bytes of its caller's frame it may write (the interface runtime's
`Iface.CallerOK`, for the model `P`): the runtime usable, the stack guard `P.depth + frame` below
`SP`, the window `[SP - P.depth - frame, SP + above)` writable and outside `P.priv`, and the
goroutine's guard word `16(g)` outside the window and `P.priv`. -/
def PanicCallerOK (P : PanicRuntime) (s : State) (frame above : Nat) : Prop :=
  P.Env s.mem ∧ StackGuardOK s (P.depth + frame) ∧ s.sp.toNat % 16 = 0 ∧
    8 ≤ P.depth ∧ P.depth + frame ≤ s.sp.toNat ∧ s.sp.toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible (s.sp.toNat - (P.depth + frame)) (P.depth + frame + above) true = true ∧
    Outside (s.sp.toNat - (P.depth + frame)) (P.depth + frame + above) P.priv ∧
    Spec.Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - (P.depth + frame)) (P.depth + frame + above) ∧
    Outside ((s.regs 28).toNat + 16) 8 P.priv

/-- `PanicPre` at a call site `S`, from the caller's `PanicCallerOK` at its entry `s`. -/
theorem PanicPre.of_parts {P : PanicRuntime} {s S : State} {frame above nargs : Nat}
    (hc : PanicCallerOK P s frame above) (henv : P.Env S.mem)
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (hguard : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) (hfr : frame % 16 = 0)
    (hn : 8 + 8 * nargs ≤ frame + above) : PanicPre P nargs S := by
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, -⟩ := hc
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  refine ⟨henv, ⟨?_, ?_, ?_⟩, ⟨hlr, hlr', ?_, ?_, hd8, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hacc]; exact hg2
  · simp only [stackguard0, regG, stackguard0Offset, hg, hguard, hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hacc]; exact Memory.accessible_mono _ hst (by omega) (by omega)
  · rw [hsp]; exact Outside.of_sub hout (by omega) (by omega)

/-- `PanicPre.of_parts` for a call whose state's memory differs from the caller's entry memory
only inside the caller's window. -/
theorem PanicPre.of_caller {P : PanicRuntime} (hl : P.Laws) {s S : State}
    {frame above nargs : Nat} (hc : PanicCallerOK P s frame above)
    (hf : MemFrame s.mem S.mem [(s.sp.toNat - (P.depth + frame), s.sp.toNat + above)])
    (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) (hfr : frame % 16 = 0)
    (hn : 8 + 8 * nargs ≤ frame + above) : PanicPre P nargs S := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, -, -⟩, -, -, -, -, -, hout, hgd, -⟩ := hc'
  simp only [regG, stackguard0Offset, Spec.Disjoint] at hg1 hgd
  refine PanicPre.of_parts hc (hl.env_frame _ _ henv
    (Map.Agrees.of_window hf (Outside.of_sub hout (by omega) (by omega)))) hf.accessible
    (hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)) hsp hg hlr hlr' hfr hn

/-- `PanicPre` at a later call site `S`: memory changed only in `P.priv` and the caller's window
since the entry `s` (earlier runtime calls), and the runtime usable in `S.mem`. -/
theorem PanicPre.of_frame {P : PanicRuntime} {s S : State} {frame above nargs : Nat}
    (hc : PanicCallerOK P s frame above)
    (hf : MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + frame), s.sp.toNat + above)]))
    (henv : P.Env S.mem)
    (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) (hfr : frame % 16 = 0)
    (hn : 8 + 8 * nargs ≤ frame + above) : PanicPre P nargs S := by
  have hc' := hc
  obtain ⟨-, ⟨hg1, -, -⟩, -, -, -, -, -, -, hgd, hgo⟩ := hc'
  simp only [regG, stackguard0Offset, Spec.Disjoint] at hg1 hgd
  refine PanicPre.of_parts hc henv hf.accessible (hf.readLE _ _ ?_) hsp hg hlr hlr' hfr hn
  rw [outside_append]; exact ⟨hgo, by simp only [outside_cons, outside_nil, and_true]; omega⟩

/-- `PanicPre` at any call site `S` whose `SP` lies inside the caller's window (at most `frame`
bytes below the caller's entry `SP`, its argument area inside the window): memory changed only in
`P.priv` and the window since the entry, and the runtime usable in `S.mem`. -/
theorem PanicPre.of_within {P : PanicRuntime} {s S : State} {frame above nargs : Nat}
    (hc : PanicCallerOK P s frame above)
    (hf : MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + frame), s.sp.toNat + above)]))
    (henv : P.Env S.mem) (hlo : s.sp.toNat - frame ≤ S.sp.toNat)
    (hhi : S.sp.toNat + 8 + 8 * nargs ≤ s.sp.toNat + above) (hal : S.sp.toNat % 16 = 0)
    (hg : S.regs 28 = s.regs 28)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) : PanicPre P nargs S := by
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, -, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd
  have hguard : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hf.readLE _ _ (by rw [outside_append]; exact ⟨hgo, by simp only [outside_cons, outside_nil, and_true]; omega⟩)
  refine ⟨henv, ⟨?_, ?_, ?_⟩, ⟨hlr, hlr', hal, ?_, hd8, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hf.accessible]; exact hg2
  · simp only [stackguard0, regG, stackguard0Offset, hg, hguard]; omega
  · omega
  · omega
  · rw [hf.accessible]; exact Memory.accessible_mono _ hst (by omega) (by omega)
  · exact Outside.of_sub hout (by omega) (by omega)

/-! ### The bookkeeping a returning runtime call leaves

`g` is the goroutine of the call (`X28`). A call that records nothing keeps the panic chain,
the defer chain, the saved open-coded state and the deferred call's return point, and does not
consume `room`; a call that adds a record changes the defer chain as its contract says and
consumes at most one unit of `room`. -/

/-- The goroutine of an arm64 Go state: `X28`. -/
abbrev gOf (s : State) : Nat := (s.regs 28).toNat

/-- The bookkeeping of goroutine `g` other than the defer chain is the same in `m'` as in `m`, and
`m'` has at least `room m g - used` room. -/
def KeepsBut (P : PanicRuntime) (g used : Nat) (m m' : Memory) : Prop :=
  P.panics m' g = P.panics m g ∧ P.saved m' g = P.saved m g ∧ P.rp m' g = P.rp m g ∧
    P.room m g ≤ P.room m' g + used

/-- A panic-runtime call returns (arm64) with the frame of `PanicRet`, and may also write the
ranges `extra` (a `_defer` record on the caller's stack). -/
def PanicRetW (P : PanicRuntime) (nargs : Nat) (extra : List (Nat × Nat)) (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat))
    (ep : Nat → Bool),
    s' = retStateX s junk [] f v m ex ep ∧ MemFrame s.mem m (P.priv ++ calleeStack s P.depth nargs ++ extra) ∧
      P.Env m

/-- `runtime.deferproc(fn)` (Go 1.26 `panic.go`, `X0` = the funcval): records a heap `_defer` for
the caller's frame (`d.sp` = the caller's `SP`, `d.fn = fn`) on top of the goroutine's chain and
returns. It allocates the record (`newdefer`: the deferpool or `mallocgc`), so it needs
`0 < P.room`. -/
def DeferprocContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (fun s => PanicPre P 1 s ∧ 0 < P.room s.mem (gOf s))
    (fun s s' => PanicRet P 1 s s' ∧
      P.defers s'.mem (gOf s) = { sp := s.sp.toNat, fns := [(s.regs 0).toNat] } :: P.defers s.mem (gOf s) ∧
      KeepsBut P (gOf s) 1 s.mem s'.mem)

/-- `runtime.deferprocStack(d)` (`X0` = a 48-byte `_defer` on the caller's stack whose `fn`, at
`d + 24`, the compiler has set): links `d` (writing its `sp`, `pc`, `link`, … fields) on top of the
goroutine's chain as a record of the caller's frame and returns. `d` must be writable and outside
`P.priv`. -/
def DeferprocStackContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (fun s => PanicPre P 1 s ∧ 0 < P.room s.mem (gOf s) ∧
      (s.regs 0).toNat + 48 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 48 true = true ∧
      Outside (s.regs 0).toNat 48 P.priv)
    (fun s s' => PanicRetW P 1 [((s.regs 0).toNat, (s.regs 0).toNat + 48)] s s' ∧
      P.defers s'.mem (gOf s) =
        { sp := s.sp.toNat, fns := [s.mem.readLE ((s.regs 0).toNat + 24) 8] } :: P.defers s.mem (gOf s) ∧
      KeepsBut P (gOf s) 1 s.mem s'.mem)

/-- `runtime.deferrangefunc()`: starts the range-over-func defer list of the caller's frame (a
`_defer` with `rangefunc` set, on top of the chain) and returns its token, a non-nil `any`
(`X0` its type word, `X1` the token). It allocates. -/
def DeferrangefuncContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (fun s => PanicPre P 0 s ∧ 0 < P.room s.mem (gOf s))
    (fun s s' => PanicRet P 0 s s' ∧ (s'.regs 0).toNat ≠ 0 ∧
      P.defers s'.mem (gOf s) =
        { sp := s.sp.toNat, fns := [], token := some (s'.regs 1).toNat } :: P.defers s.mem (gOf s) ∧
      KeepsBut P (gOf s) 1 s.mem s'.mem)

/-- `runtime.deferprocat(fn, frame)` (`X0` = the funcval, `X1`/`X2` = the token `any`): adds `fn`
to the front of the range-over-func list whose token is `frame` (it allocates the record). The
contract covers the case where that list is the record on top of the goroutine's chain (the loop
body runs below the frame that owns it; an iterator that has its own records pending is not
covered). -/
def DeferprocatContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (fun s => PanicPre P 2 s ∧ 0 < P.room s.mem (gOf s) ∧
      ∃ r rest, P.defers s.mem (gOf s) = r :: rest ∧ r.token = some (s.regs 2).toNat)
    (fun s s' => PanicRet P 2 s s' ∧
      (∀ r rest, P.defers s.mem (gOf s) = r :: rest →
        P.defers s'.mem (gOf s) = { r with fns := (s.regs 0).toNat :: r.fns } :: rest) ∧
      KeepsBut P (gOf s) 1 s.mem s'.mem)

/-- `runtime.gorecover()` (Go 1.26 `panic.go`, no arguments): `recover()`. With no active panic,
or a `Goexit` or an already recovered panic on top of the chain, it returns `nil` and changes
nothing. Otherwise, if it was called directly by the deferred call the active panic is running —
its caller is not a wrapper and the caller's saved return address, `[X29 + 8]` on the
frame-pointer chain at entry, is that call's return point `P.rp` — it marks the panic recovered and
returns its value. In every other situation the contract says nothing about the result. It
returns normally and keeps the defer chain, the saved state and `room`. -/
def GorecoverContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr
    (fun s => PanicPre P 0 s ∧ s.mem.accessible ((s.regs 29).toNat + 8) 8 false = true ∧
      (s.regs 29).toNat + 16 ≤ 2 ^ 48)
    (fun s s' => PanicRet P 0 s s' ∧ P.defers s'.mem (gOf s) = P.defers s.mem (gOf s) ∧
      P.saved s'.mem (gOf s) = P.saved s.mem (gOf s) ∧ P.rp s'.mem (gOf s) = P.rp s.mem (gOf s) ∧
      P.room s.mem (gOf s) ≤ P.room s'.mem (gOf s) ∧
      ((P.panics s.mem (gOf s) = [] ∨ ∃ r rs, P.panics s.mem (gOf s) = r :: rs ∧
          (r.goexit = true ∨ r.recovered = true)) →
        s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ P.panics s'.mem (gOf s) = P.panics s.mem (gOf s)) ∧
      (∀ r rs, P.panics s.mem (gOf s) = r :: rs → r.goexit = false → r.recovered = false →
        ¬ P.wrapper (s.regs 30).toNat → s.mem.readLE ((s.regs 29).toNat + 8) 8 = P.rp s.mem (gOf s) →
        (s'.regs 0).toNat = r.arg.typ ∧ (s'.regs 1).toNat = r.arg.data ∧
          P.panics s'.mem (gOf s) = { r with recovered := true } :: rs))

/-! ### Running a frame's deferred calls

`runtime.gopanic`, `runtime.Goexit` and `runtime.deferreturn` share one loop (`_panic.nextDefer`):
for the frame being processed, first its pending open-coded defers (highest `deferBits` bit first:
the runtime clears the bit and calls the closure in the slot), then the records of the goroutine's
chain that belong to the frame (`d.sp` = the frame's `SP`; a range-over-func record is first
converted into one record per call). `Engine` states this loop as a continuation: for each call
the runtime makes, it reaches the closure's entry; for **every** state the closure may return in
(or, for a panic, every state in which a nested panic left the closure), the runtime goes on; after
the last call it reaches `Fin`. -/

/-- How the loop was entered: a panic (`gopanic`), a `Goexit`, or a function's exit
(`deferreturn`). -/
inductive DeferMode where
  | panic | goexit | ret
deriving DecidableEq, Repr

/-- The frame whose deferred calls the loop runs: its `SP`, its entry `SP` (`bound`: leaving the
frame means unwinding past it), where a recovery resumes it (its `deferreturn` call), and, when
the runtime runs its open-coded defers, the addresses of its `deferBits` byte and first slot. -/
structure Frame where
  sp : Nat
  bound : Nat
  resume : Nat
  openAt : Option (Nat × Nat)
deriving DecidableEq, Repr

/-- One deferred call the loop makes: the funcval, the `deferBits` byte at the call (an open-coded
defer: the byte with this call's bit and every higher one cleared), and the goroutine's defer chain
at the call (a record's call: the record popped). -/
structure Item where
  fn : Nat
  bits : Option Nat
  chain : List DeferRec
deriving DecidableEq, Repr

/-- The calls of one record's funcvals `fs` (the record already popped; a range-over-func record
converted by `deferconvert` into one plain record per call, `rs` the chain below it), each with
the chain at its call: the record's calls still to run, as plain records, then `rs`. -/
def fnItems (sp : Nat) (rs : List DeferRec) : List Nat → List Item
  | [] => []
  | f :: fs => { fn := f, bits := none, chain := fs.map (fun g => ({ sp := sp, fns := [g] } : DeferRec)) ++ rs } ::
      fnItems sp rs fs

/-- The calls of the records of frame `sp` at the top of the chain, in order (`nextDefer`'s
`Recheck` loop: a record of the frame is popped, a range-over-func one converted first). -/
def recItems (sp : Nat) : List DeferRec → List Item
  | [] => []
  | r :: rs => if r.sp = sp then fnItems sp rs r.fns ++ recItems sp rs else []

/-- The calls of the open-coded defers pending in the byte `b` (slots from `sa`). -/
def openItems (m : Memory) (sa b : Nat) (ds : List DeferRec) : List Item :=
  (openBits b).map (fun i => { fn := m.readLE (sa + 8 * i) 8, bits := some (b % 2 ^ i), chain := ds })

/-- Every call the loop makes for frame `F` from memory `m` and defer chain `ds`, in order. -/
def frameItems (m : Memory) (F : Frame) (ds : List DeferRec) : List Item :=
  (match F.openAt with
    | none => []
    | some (ba, sa) => openItems m sa (m.readLE ba 1) ds) ++
  recItems F.sp ds

/-- The memory the runtime reads again between calls, which the deferred calls must leave alone:
the `deferBits` byte, the slots of the pending open-coded defers, and the first word (the code
pointer) of every funcval still to be called. -/
def frameKeep (m : Memory) (F : Frame) (items : List Item) : List (Nat × Nat) :=
  (match F.openAt with
    | none => []
    | some (ba, sa) => (ba, ba + 1) :: (openBits (m.readLE ba 1)).map (fun i => (sa + 8 * i, sa + 8 * i + 8))) ++
  items.map (fun it => (it.fn, it.fn + 8))

/-- The runtime's stack window below the frame (arm64): `[F.sp - P.depth, F.sp - 8)` (never the
frame's saved frame pointer at `F.sp - 8`). -/
def rtWin (P : PanicRuntime) (F : Frame) : List (Nat × Nat) := [(F.sp - P.depth, F.sp - 8)]

/-- The frame's `deferBits` byte, which the runtime writes, if it runs open-coded defers. -/
def bitsWin (F : Frame) : List (Nat × Nat) :=
  match F.openAt with
  | none => []
  | some (ba, _) => [(ba, ba + 1)]

/-- What the loop needs of the frame's memory: the `deferBits` byte writable, below `2^48`, outside
`P.priv` and in the frame (at or above its `SP`: the runtime's own stack window is below), the
pending slots readable and apart from the `deferBits` byte (the runtime re-reads a slot after
clearing the byte; the compiler gives them distinct stack slots), in the frame and outside
`P.priv`, and every funcval apart from that byte; and of every call: its funcval readable, with an
admissible code word (4-aligned, below `2^48`), outside `P.priv` and outside the runtime's stack
window below the frame (a funcval is a global, a heap closure or a closure in the frame). -/
def FrameOK (P : PanicRuntime) (m : Memory) (F : Frame) (items : List Item) : Prop :=
  (match F.openAt with
    | none => True
    | some (ba, sa) => ba + 1 ≤ 2 ^ 48 ∧ m.accessible ba 1 true = true ∧ Outside ba 1 P.priv ∧ F.sp ≤ ba ∧
        (∀ i ∈ openBits (m.readLE ba 1), sa + 8 * i + 8 ≤ 2 ^ 48 ∧ m.accessible (sa + 8 * i) 8 false = true ∧
          (sa + 8 * i + 8 ≤ ba ∨ ba + 1 ≤ sa + 8 * i) ∧ F.sp ≤ sa + 8 * i ∧ Outside (sa + 8 * i) 8 P.priv) ∧
        ∀ it ∈ items, it.fn + 8 ≤ ba ∨ ba + 1 ≤ it.fn) ∧
  ∀ it ∈ items, it.fn + 8 ≤ 2 ^ 48 ∧ m.accessible it.fn 8 false = true ∧
    m.readLE it.fn 8 % 4 = 0 ∧ m.readLE it.fn 8 < 2 ^ 48 ∧ Outside it.fn 8 P.priv ∧
    (it.fn + 8 ≤ F.sp - P.depth ∨ F.sp ≤ it.fn)

/-- A deferred call as the runtime makes it (arm64): control at the funcval's code word with the
closure context `X26` = the funcval, the goroutine `X28` and platform register `X18` of the
frame's code, the runtime's frame pointer `X29 = SP - 8`, a 16-aligned `SP` at most `P.depth`
bytes below the frame's and 16 below it, an admissible return point in `X30`, the runtime usable. -/
def DeferCall (P : PanicRuntime) (x28 x18 : W64) (fsp fn : Nat) (e : State) : Prop :=
  e.pc = BitVec.ofNat 64 (e.mem.readLE fn 8) ∧ e.regs 26 = BitVec.ofNat 64 fn ∧
    e.regs 28 = x28 ∧ e.regs 18 = x18 ∧ e.regs 29 = e.sp - 8 ∧ e.sp.toNat % 16 = 0 ∧
    fsp - P.depth ≤ e.sp.toNat ∧ e.sp.toNat + 16 ≤ fsp ∧ (e.regs 30).toNat % 4 = 0 ∧
    (e.regs 30).toNat < 2 ^ 48 ∧ P.Env e.mem

/-- A deferred call `e` returned normally in `e'` (arm64): at its return point with `SP`, `X28` and
`X18` restored, the runtime's stack between the call's `SP` and the frame's, and the memory `keep`,
unchanged, the runtime usable, the defer chain and saved state as at the call, no room consumed. -/
def DeferReturned (P : PanicRuntime) (x28 x18 : W64) (fsp : Nat) (keep : List (Nat × Nat))
    (e e' : State) : Prop :=
  e'.pc = e.regs 30 ∧ e'.sp = e.sp ∧ e'.regs 28 = x28 ∧ e'.regs 18 = x18 ∧
    Map.Agrees e.mem e'.mem ((e.sp.toNat, fsp) :: keep) ∧ P.Env e'.mem ∧
    P.defers e'.mem x28.toNat = P.defers e.mem x28.toNat ∧
    P.saved e'.mem x28.toNat = P.saved e.mem x28.toNat ∧ P.room e.mem x28.toNat ≤ P.room e'.mem x28.toNat

/-- What `runtime.recovery` does after the deferred call (whose item is `it`) returned in `e'`
with the panic recovered (arm64): it resumes the frame at its `deferreturn` call with `SP` the
frame's and `X29 = SP - 8`, `X28`/`X18` kept, memory changed only in `P.priv` and the runtime's
window; it drops every panic started at or below the frame (`p.startSP < sp`); if the frame still
has open-coded defers pending, it leaves them for `deferreturn` (`saved`). -/
def Recovers (p : Program) (P : PanicRuntime) (x28 x18 : W64) (F : Frame) (it : Item) (e' : State) :
    Prop :=
  ∃ k d, Program.Steps p e' k d ∧ d.pc = BitVec.ofNat 64 F.resume ∧ d.sp = BitVec.ofNat 64 F.sp ∧
    d.regs 29 = d.sp - 8 ∧ d.regs 28 = x28 ∧ d.regs 18 = x18 ∧
    MemFrame e'.mem d.mem (P.priv ++ rtWin P F) ∧ P.Env d.mem ∧
    P.panics d.mem x28.toNat = (P.panics e'.mem x28.toNat).dropWhile (·.start ≤ F.sp) ∧
    P.defers d.mem x28.toNat = P.defers e'.mem x28.toNat ∧
    P.saved d.mem x28.toNat = (if it.bits.getD 0 = 0 then none else F.openAt) ∧
    P.room e'.mem x28.toNat ≤ P.room d.mem x28.toNat

/-- The loop over a frame's deferred calls (arm64), from the runtime state `c` (the entry of the
runtime function, or the state where the previous call returned), with the goroutine's panic
chain `ch` and at least `rm` room, for the calls `items`:

* no call left: the runtime reaches a state `d` with `Fin ch rm c d`;
* a call `it`: the runtime reaches the call `e` (`DeferCall`), having changed memory only in
  `P.priv`, its window and the `deferBits` byte (which holds `it.bits`), with the chain `it.chain`,
  the panic chain `ch`, at least `rm` room, and (panic, `Goexit`) the return point recorded for
  `recover` (`P.rp`; `deferreturn` keeps it and clears `saved`). Then for every normal return `e'`
  of the call: with the panic chain unchanged the loop goes on; (panic) with the active panic
  recovered — and no `Goexit` among the panics the recovery drops — the runtime `Recovers`. And
  (panic) for every state `u` in which a nested panic, with the outer one still in the chain below
  it, left the deferred call (`U u g e.sp`), the loop goes on with the new panic on top. -/
def Engine (p : Program) (P : PanicRuntime) (U : State → Nat → Nat → Prop) (x28 x18 : W64)
    (F : Frame) (keep : List (Nat × Nat)) (mode : DeferMode)
    (Fin : List PanicRec → Nat → State → State → Prop) :
    List PanicRec → Nat → List Item → State → Prop
  | ch, rm, [], c => ∃ k d, Program.Steps p c k d ∧ Fin ch rm c d
  | ch, rm, it :: rest, c => ∃ k e, Program.Steps p c k e ∧ DeferCall P x28 x18 F.sp it.fn e ∧
      MemFrame c.mem e.mem (P.priv ++ rtWin P F ++ bitsWin F) ∧
      (∀ b ba sa, it.bits = some b → F.openAt = some (ba, sa) → e.mem.readLE ba 1 = b) ∧
      P.defers e.mem x28.toNat = it.chain ∧ P.panics e.mem x28.toNat = ch ∧
      rm ≤ P.room e.mem x28.toNat ∧
      (if mode = .ret then P.rp e.mem x28.toNat = P.rp c.mem x28.toNat ∧ P.saved e.mem x28.toNat = none
       else P.rp e.mem x28.toNat = (e.regs 30).toNat ∧ P.saved e.mem x28.toNat = P.saved c.mem x28.toNat) ∧
      (∀ e', DeferReturned P x28 x18 F.sp keep e e' →
        (P.panics e'.mem x28.toNat = ch → Engine p P U x28 x18 F keep mode Fin ch rm rest e') ∧
        (mode = .panic → ∀ r rs, ch = r :: rs →
          P.panics e'.mem x28.toNat = { r with recovered := true } :: rs →
          (∀ q ∈ (P.panics e'.mem x28.toNat).takeWhile (·.start ≤ F.sp), q.goexit = false) →
          Recovers p P x28 x18 F it e')) ∧
      (mode = .panic → ∀ u r2, U u x28.toNat e.sp.toNat →
        Map.Agrees e.mem u.mem ((e.sp.toNat, F.sp) :: keep) → P.Env u.mem →
        P.defers u.mem x28.toNat = P.defers e.mem x28.toNat →
        P.saved u.mem x28.toNat = P.saved e.mem x28.toNat →
        P.panics u.mem x28.toNat = r2 :: ch → r2.goexit = false → r2.recovered = false →
        r2.start ≤ e.sp.toNat → rm ≤ P.room u.mem x28.toNat + 1 →
        Engine p P U x28 x18 F keep mode Fin (r2 :: ch) (rm - 1) rest u)

/-- The end of a panic's or `Goexit`'s loop over frame `F` (entered with defer chain `ds`): the
runtime unwinds past the frame (`U d g F.bound`) with the panic chain `ch`, the frame's records
popped, memory changed only in `P.priv`, its window and the `deferBits` byte, the saved
open-coded state kept. -/
def LeftFrame (P : PanicRuntime) (U : State → Nat → Nat → Prop) (x28 : W64) (F : Frame)
    (ds : List DeferRec) (ch : List PanicRec) (rm : Nat) (c d : State) : Prop :=
  U d x28.toNat F.bound ∧ P.panics d.mem x28.toNat = ch ∧ P.defers d.mem x28.toNat = frameRest F.sp ds ∧
    MemFrame c.mem d.mem (P.priv ++ rtWin P F ++ bitsWin F) ∧ P.Env d.mem ∧ rm ≤ P.room d.mem x28.toNat ∧
    P.saved d.mem x28.toNat = P.saved c.mem x28.toNat

/-- The frame of `fi` at `SP = sp` as the runtime finds it when a panic or `Goexit` reaches it:
it runs open-coded defers iff the function has `FUNCDATA_OpenCodedDeferInfo` and its `deferBits`
byte is non-zero (`initOpenCodedDefers`). -/
def frameOf (fi : FuncInfo) (sp : Nat) (m : Memory) : Frame :=
  { sp := sp, bound := fi.bound sp, resume := fi.resume,
    openAt := match fi.openDefer with
      | none => none
      | some _ => if m.readLE (fi.bitsAt sp) 1 = 0 then none else some (fi.bitsAt sp, fi.slotsAt sp) }

/-- The precondition of `runtime.gopanic(v)` (arm64) at its entry `s`, called from a frame of `fi`:
the shared frame (`PanicPre`, two argument registers), `v` (`X0`, `X1`) not nil, room for its
`_panic`, the frame's `deferBits` byte readable and outside `P.priv` (the runtime reads it to find the
frame's open-coded defers), and the frame's memory as the loop needs it. -/
def GopanicPre (P : PanicRuntime) (fi : FuncInfo) (s : State) : Prop :=
  PanicPre P 2 s ∧ (s.regs 0).toNat ≠ 0 ∧ 0 < P.room s.mem (gOf s) ∧
    (fi.openDefer.isSome → s.mem.accessible (fi.bitsAt s.sp.toNat) 1 false = true ∧
      Outside (fi.bitsAt s.sp.toNat) 1 P.priv) ∧
    FrameOK P s.mem (frameOf fi s.sp.toNat s.mem)
      (frameItems s.mem (frameOf fi s.sp.toNat s.mem) (P.defers s.mem (gOf s)))

/-- **`runtime.gopanic(v)`** (Go 1.26 `panic.go`; `X0`/`X1` = the `any`). Called from a frame `F`
of an extracted function (`fi`: the function of `T`, the binary's `Extracted.funcs`, containing the
return address `X30`; `F`'s `SP` is `SP` at entry), it pushes a `_panic` for `v` started at `F`
and runs `F`'s deferred calls (`Engine`, mode `panic`): a call that recovers makes the runtime
resume `F` at its `deferreturn` call; a nested panic that leaves a call replaces `v` for the rest;
if no call recovers, the panic leaves `F` (`LeftFrame`: the state `U d g (F's entry SP)` the
runtime unwinds into `F`'s callers from). -/
def GopanicContract (p : Program) (addr : Nat) (P : PanicRuntime) (U : State → Nat → Nat → Prop)
    (T : List FuncInfo) : Prop :=
  ∀ s fi, s.pc = BitVec.ofNat 64 addr → FuncInfo.find T (s.regs 30).toNat = some fi →
    GopanicPre P fi s →
    Engine p P U (s.regs 28) (s.regs 18) (frameOf fi s.sp.toNat s.mem)
      (frameKeep s.mem (frameOf fi s.sp.toNat s.mem)
        (frameItems s.mem (frameOf fi s.sp.toNat s.mem) (P.defers s.mem (gOf s))))
      .panic (LeftFrame P U (s.regs 28) (frameOf fi s.sp.toNat s.mem) (P.defers s.mem (gOf s)))
      ({ arg := ⟨(s.regs 0).toNat, (s.regs 1).toNat⟩, start := s.sp.toNat } :: P.panics s.mem (gOf s))
      (P.room s.mem (gOf s) - 1)
      (frameItems s.mem (frameOf fi s.sp.toNat s.mem) (P.defers s.mem (gOf s))) s

/-- The precondition of `runtime.Goexit()` (arm64) called from a frame of `fi`. -/
def GoexitPre (P : PanicRuntime) (fi : FuncInfo) (s : State) : Prop :=
  PanicPre P 0 s ∧ 0 < P.room s.mem (gOf s) ∧
    (fi.openDefer.isSome → s.mem.accessible (fi.bitsAt s.sp.toNat) 1 false = true ∧
      Outside (fi.bitsAt s.sp.toNat) 1 P.priv) ∧
    FrameOK P s.mem (frameOf fi s.sp.toNat s.mem)
      (frameItems s.mem (frameOf fi s.sp.toNat s.mem) (P.defers s.mem (gOf s)))

/-- **`runtime.Goexit()`** (Go 1.26 `panic.go`): pushes a `_panic` with `goexit` set (so `recover`
returns `nil` in the deferred calls: a `Goexit` cannot be recovered), runs the deferred calls of
the calling frame `F` (`Engine`, mode `goexit`) and leaves `F` (`LeftFrame`), going on to
terminate the goroutine; it never returns. A deferred call that panics is not covered. -/
def GoexitContract (p : Program) (addr : Nat) (P : PanicRuntime) (U : State → Nat → Nat → Prop)
    (T : List FuncInfo) : Prop :=
  ∀ s fi, s.pc = BitVec.ofNat 64 addr → FuncInfo.find T (s.regs 30).toNat = some fi →
    GoexitPre P fi s →
    Engine p P U (s.regs 28) (s.regs 18) (frameOf fi s.sp.toNat s.mem)
      (frameKeep s.mem (frameOf fi s.sp.toNat s.mem)
        (frameItems s.mem (frameOf fi s.sp.toNat s.mem) (P.defers s.mem (gOf s))))
      .goexit (LeftFrame P U (s.regs 28) (frameOf fi s.sp.toNat s.mem) (P.defers s.mem (gOf s)))
      ({ arg := ⟨0, 0⟩, goexit := true, start := s.sp.toNat } :: P.panics s.mem (gOf s))
      (P.room s.mem (gOf s) - 1)
      (frameItems s.mem (frameOf fi s.sp.toNat s.mem) (P.defers s.mem (gOf s))) s

/-- The frame `deferreturn` runs (its caller, `SP` at entry): the open-coded defers a recovery
left pending (`P.saved`), then the frame's records. -/
def retFrame (P : PanicRuntime) (s : State) : Frame :=
  { sp := s.sp.toNat, bound := s.sp.toNat, resume := 0, openAt := P.saved s.mem (gOf s) }

/-- The end of `deferreturn`'s loop: it returns to `X30` with `SP`, `X28`, `X18`, `X29` as at entry
`s`, memory changed only in `P.priv`, its window and the `deferBits` byte, the frame's records
popped, `saved` cleared. -/
def RetFin (P : PanicRuntime) (s : State) (ds : List DeferRec) (ch : List PanicRec) (rm : Nat)
    (c d : State) : Prop :=
  d.pc = s.regs 30 ∧ d.sp = s.sp ∧ d.regs 28 = s.regs 28 ∧ d.regs 18 = s.regs 18 ∧
    d.regs 29 = s.regs 29 ∧ MemFrame c.mem d.mem (P.priv ++ rtWin P (retFrame P s) ++ bitsWin (retFrame P s)) ∧
    P.Env d.mem ∧ P.panics d.mem (gOf s) = ch ∧ P.defers d.mem (gOf s) = frameRest s.sp.toNat ds ∧
    P.saved d.mem (gOf s) = none ∧ P.rp d.mem (gOf s) = P.rp s.mem (gOf s) ∧ rm ≤ P.room d.mem (gOf s)

/-- The precondition of `runtime.deferreturn()` (arm64). -/
def DeferreturnPre (P : PanicRuntime) (s : State) : Prop :=
  PanicPre P 0 s ∧
    FrameOK P s.mem (retFrame P s) (frameItems s.mem (retFrame P s) (P.defers s.mem (gOf s)))

/-- **`runtime.deferreturn()`** (Go 1.26): runs the deferred calls of its caller's frame — the
open-coded defers a recovery left pending, then the frame's records, most recent first
(`Engine`, mode `ret`) — and returns (`RetFin`). The deferred calls are the program's own code,
run by the theorem; a call that panics is not covered. -/
def DeferreturnContract (p : Program) (addr : Nat) (P : PanicRuntime) (U : State → Nat → Nat → Prop) :
    Prop :=
  ∀ s, s.pc = BitVec.ofNat 64 addr → DeferreturnPre P s →
    Engine p P U (s.regs 28) (s.regs 18) (retFrame P s)
      (frameKeep s.mem (retFrame P s) (frameItems s.mem (retFrame P s) (P.defers s.mem (gOf s))))
      .ret (RetFin P s (P.defers s.mem (gOf s))) (P.panics s.mem (gOf s)) (P.room s.mem (gOf s))
      (frameItems s.mem (retFrame P s) (P.defers s.mem (gOf s))) s

/-- The Go-level classification with the panic runtime's unwinding states (arm64): as `goClass`,
and a state the runtime unwinds past the call's frame from (`U s g s₀.sp`, `s₀` the call state)
is a panic with the active panic's value (`atLeave`) or, for a `Goexit`, the `Goexit` outcome
(`atExit`). -/
def goClassU (P : PanicRuntime) (U : State → Nat → Nat → Prop) (s₀ : State) : GoClass :=
  { atStub := (goClass P).atStub, atFault := (goClass P).atFault,
    atLeave := fun s v => U s (gOf s₀) s₀.sp.toNat ∧
      ∃ r rs, P.panics s.mem (gOf s₀) = r :: rs ∧ r.arg = v ∧ r.goexit = false,
    atExit := fun s => U s (gOf s₀) s₀.sp.toNat ∧
      ∃ r rs, P.panics s.mem (gOf s₀) = r :: rs ∧ r.goexit = true }

/-- Use the `gopanic` contract at a call `S` inside a proof of a `GoReturns` goal at `S`. -/
theorem GopanicContract.apply {p p' : Program} {addr : Nat} {P : PanicRuntime}
    {U : State → Nat → Nat → Prop} {T : List FuncInfo} {S : State} {fi : FuncInfo} {C : GoClass}
    {Q : GoOutcome → Prop} (h : GopanicContract p addr P U T) (hpc : S.pc = BitVec.ofNat 64 addr)
    (hfi : FuncInfo.find T (S.regs 30).toNat = some fi) (hpre : GopanicPre P fi S)
    (k : Engine p P U (S.regs 28) (S.regs 18) (frameOf fi S.sp.toNat S.mem)
      (frameKeep S.mem (frameOf fi S.sp.toNat S.mem)
        (frameItems S.mem (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S))))
      .panic (LeftFrame P U (S.regs 28) (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S)))
      ({ arg := ⟨(S.regs 0).toNat, (S.regs 1).toNat⟩, start := S.sp.toNat } :: P.panics S.mem (gOf S))
      (P.room S.mem (gOf S) - 1)
      (frameItems S.mem (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S))) S →
      GoReturns p' C S Q) : GoReturns p' C S Q :=
  k (h S fi hpc hfi hpre)

/-- Use the `Goexit` contract at a call `S`. -/
theorem GoexitContract.apply {p p' : Program} {addr : Nat} {P : PanicRuntime}
    {U : State → Nat → Nat → Prop} {T : List FuncInfo} {S : State} {fi : FuncInfo} {C : GoClass}
    {Q : GoOutcome → Prop} (h : GoexitContract p addr P U T) (hpc : S.pc = BitVec.ofNat 64 addr)
    (hfi : FuncInfo.find T (S.regs 30).toNat = some fi) (hpre : GoexitPre P fi S)
    (k : Engine p P U (S.regs 28) (S.regs 18) (frameOf fi S.sp.toNat S.mem)
      (frameKeep S.mem (frameOf fi S.sp.toNat S.mem)
        (frameItems S.mem (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S))))
      .goexit (LeftFrame P U (S.regs 28) (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S)))
      ({ arg := ⟨0, 0⟩, goexit := true, start := S.sp.toNat } :: P.panics S.mem (gOf S))
      (P.room S.mem (gOf S) - 1)
      (frameItems S.mem (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S))) S →
      GoReturns p' C S Q) : GoReturns p' C S Q :=
  k (h S fi hpc hfi hpre)

/-- Name the state of a `GoReturns` goal (to replace a large symbolic state by its facts). -/
theorem _root_.Janus.GoABI.GoReturns.name {p : Program} {C : GoClass} {S : State} {Q : GoOutcome → Prop}
    (h : ∀ S', S' = S → GoReturns p C S' Q) : GoReturns p C S Q := h S rfl

/-- A deferred call that returned at its return point with `SP`, `X28`, `X18` restored and wrote only
the window `[lo, hi)`, outside `P.priv`, the runtime's stack between its `SP` and the frame's, and
the memory the loop reads again, returned as `DeferReturned` says, with the panic chain unchanged. -/
theorem DeferReturned.of_window {P : PanicRuntime} (hl : P.Laws) {x28 x18 : W64} {fsp : Nat}
    {keep : List (Nat × Nat)} {e e' : State} {lo hi : Nat}
    (hpc : e'.pc = e.regs 30) (hsp : e'.sp = e.sp) (h28 : e'.regs 28 = x28) (h18 : e'.regs 18 = x18)
    (henv : P.Env e.mem) (hf : MemFrame e.mem e'.mem [(lo, hi)])
    (ho : Outside lo (hi - lo) (P.priv ++ (e.sp.toNat, fsp) :: keep)) :
    DeferReturned P x28 x18 fsp keep e e' ∧ P.panics e'.mem x28.toNat = P.panics e.mem x28.toNat := by
  rw [outside_append] at ho
  have hp : Map.Agrees e.mem e'.mem P.priv := Map.Agrees.of_window hf ho.1
  exact ⟨⟨hpc, hsp, h28, h18, Map.Agrees.of_window hf ho.2, hl.env_frame _ _ henv hp,
    hl.defers_frame _ _ _ hp, hl.saved_frame _ _ _ hp, (hl.room_frame _ _ _ hp).symm ▸ Nat.le_refl _⟩,
    hl.panics_frame _ _ _ hp⟩

/-! ### Reading the loop on concrete frames -/

/-- A frame none of whose records is on top of the chain (every record belongs to a frame above
it) runs no record calls, and its rest of the chain is the whole chain. -/
theorem frameRecs_above {sp : Nat} {ds : List DeferRec} (h : ∀ d ∈ ds, sp < d.sp) :
    recFns sp ds = [] ∧ frameRest sp ds = ds := by
  cases ds with
  | nil => exact ⟨rfl, rfl⟩
  | cons d ds =>
    have hd : (d.sp == sp) = false := by
      have := h d (List.mem_cons_self ..); simp only [beq_eq_false_iff_ne, ne_eq]; omega
    simp [recFns, frameRecs, frameRest, List.takeWhile, List.dropWhile, hd]

@[simp] theorem recItems_nil (sp : Nat) : recItems sp [] = [] := rfl

/-- A frame none of whose records is on top of the chain makes no record calls. -/
theorem recItems_above {sp : Nat} {ds : List DeferRec} (h : ∀ d ∈ ds, sp < d.sp) : recItems sp ds = [] := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    have : d.sp ≠ sp := by have := h d (List.mem_cons_self ..); omega
    simp [recItems, this]

theorem Engine_nil {p : Program} {P : PanicRuntime} {U : State → Nat → Nat → Prop} {x28 x18 : W64}
    {F : Frame} {keep : List (Nat × Nat)} {mode : DeferMode}
    {Fin : List PanicRec → Nat → State → State → Prop} {ch : List PanicRec} {rm : Nat} {c : State} :
    Engine p P U x28 x18 F keep mode Fin ch rm [] c = ∃ k d, Program.Steps p c k d ∧ Fin ch rm c d := by
  simp only [Engine]

theorem Engine_cons {p : Program} {P : PanicRuntime} {U : State → Nat → Nat → Prop} {x28 x18 : W64}
    {F : Frame} {keep : List (Nat × Nat)} {mode : DeferMode}
    {Fin : List PanicRec → Nat → State → State → Prop} {ch : List PanicRec} {rm : Nat} {c : State}
    {it : Item} {rest : List Item} :
    Engine p P U x28 x18 F keep mode Fin ch rm (it :: rest) c =
      ∃ k e, Program.Steps p c k e ∧ DeferCall P x28 x18 F.sp it.fn e ∧
      MemFrame c.mem e.mem (P.priv ++ rtWin P F ++ bitsWin F) ∧
      (∀ b ba sa, it.bits = some b → F.openAt = some (ba, sa) → e.mem.readLE ba 1 = b) ∧
      P.defers e.mem x28.toNat = it.chain ∧ P.panics e.mem x28.toNat = ch ∧
      rm ≤ P.room e.mem x28.toNat ∧
      (if mode = .ret then P.rp e.mem x28.toNat = P.rp c.mem x28.toNat ∧ P.saved e.mem x28.toNat = none
       else P.rp e.mem x28.toNat = (e.regs 30).toNat ∧ P.saved e.mem x28.toNat = P.saved c.mem x28.toNat) ∧
      (∀ e', DeferReturned P x28 x18 F.sp keep e e' →
        (P.panics e'.mem x28.toNat = ch → Engine p P U x28 x18 F keep mode Fin ch rm rest e') ∧
        (mode = .panic → ∀ r rs, ch = r :: rs →
          P.panics e'.mem x28.toNat = { r with recovered := true } :: rs →
          (∀ q ∈ (P.panics e'.mem x28.toNat).takeWhile (·.start ≤ F.sp), q.goexit = false) →
          Recovers p P x28 x18 F it e')) ∧
      (mode = .panic → ∀ u r2, U u x28.toNat e.sp.toNat →
        Map.Agrees e.mem u.mem ((e.sp.toNat, F.sp) :: keep) → P.Env u.mem →
        P.defers u.mem x28.toNat = P.defers e.mem x28.toNat →
        P.saved u.mem x28.toNat = P.saved e.mem x28.toNat →
        P.panics u.mem x28.toNat = r2 :: ch → r2.goexit = false → r2.recovered = false →
        r2.start ≤ e.sp.toNat → rm ≤ P.room u.mem x28.toNat + 1 →
        Engine p P U x28 x18 F keep mode Fin (r2 :: ch) (rm - 1) rest u) := by
  simp only [Engine]

/-- The loop over a frame's calls is closed under a runtime prefix that writes only the loop's own
memory and keeps `saved` and `rp` (the model runtime's silent steps between calls). -/
theorem Engine.of_prefix {p : Program} {P : PanicRuntime} {U : State → Nat → Nat → Prop} {x28 x18 : W64}
    {F : Frame} {keep : List (Nat × Nat)} {mode : DeferMode}
    {Fin : List PanicRec → Nat → State → State → Prop} {c c' : State} {j : Nat}
    (hFin : ∀ ch rm d, Fin ch rm c' d → Fin ch rm c d) (hst : Program.Steps p c j c')
    (hm : MemFrame c.mem c'.mem (P.priv ++ rtWin P F ++ bitsWin F))
    (hsaved : P.saved c'.mem x28.toNat = P.saved c.mem x28.toNat)
    (hrp : P.rp c'.mem x28.toNat = P.rp c.mem x28.toNat) :
    ∀ {ch : List PanicRec} {rm : Nat} {L : List Item},
      Engine p P U x28 x18 F keep mode Fin ch rm L c' → Engine p P U x28 x18 F keep mode Fin ch rm L c
  | _, _, [], h => by
    rw [Engine_nil] at h ⊢
    obtain ⟨k, d, hs, hf⟩ := h
    exact ⟨j + k, d, hst.trans hs, hFin _ _ _ hf⟩
  | _, _, it :: rest, h => by
    rw [Engine_cons] at h ⊢
    obtain ⟨k, e, hs, hcall, hmf, hb, hd, hpn, hrm, hrs, hcont, hnest⟩ := h
    refine ⟨j + k, e, hst.trans hs, hcall, hm.trans hmf fun a n h => ⟨h, h⟩, hb, hd, hpn, hrm, ?_,
      hcont, hnest⟩
    split
    · rename_i hmode; rw [if_pos hmode] at hrs; exact ⟨hrs.1.trans hrp, hrs.2⟩
    · rename_i hmode; rw [if_neg hmode] at hrs; exact ⟨hrs.1, hrs.2.trans hsaved⟩

theorem LeftFrame.prefix {P : PanicRuntime} {U : State → Nat → Nat → Prop} {x28 : W64} {F : Frame}
    {ds : List DeferRec} {c c' : State} (hm : MemFrame c.mem c'.mem (P.priv ++ rtWin P F ++ bitsWin F))
    (hsv : P.saved c'.mem x28.toNat = P.saved c.mem x28.toNat)
    {ch : List PanicRec} {rm : Nat} {d : State} (h : LeftFrame P U x28 F ds ch rm c' d) :
    LeftFrame P U x28 F ds ch rm c d := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, hm.trans h4 fun a n h => ⟨h, h⟩, h5, h6, h7.trans hsv⟩

theorem RetFin.prefix {P : PanicRuntime} {s : State} {ds : List DeferRec} {c c' : State}
    (hm : MemFrame c.mem c'.mem (P.priv ++ rtWin P (retFrame P s) ++ bitsWin (retFrame P s)))
    {ch : List PanicRec} {rm : Nat} {d : State} (h : RetFin P s ds ch rm c' d) : RetFin P s ds ch rm c d := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, hm.trans h6 fun a n h => ⟨h, h⟩, h7⟩

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
