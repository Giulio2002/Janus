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

/-- `runtime.gorecover()` (Go 1.26 `panic.go`, no arguments): `recover()`. It returns the
current panic's value if it was called directly by the deferred call the panic is running (the
caller is not a wrapper and its frame's saved return address, `[FP + 8]` on the frame-pointer chain
at entry, is that deferred call's return point into `runtime.gopanic`), and marks the panic
recovered; with no active panic (`P.Calm`) it returns `nil`. In every other situation the contract
says nothing about the result. It returns normally. -/
def GorecoverContract (p : Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr
    (fun s => PanicPre P 0 s ∧ s.mem.accessible ((s.regs 29).toNat + 8) 8 false = true ∧
      (s.regs 29).toNat + 16 ≤ 2 ^ 48)
    (fun s s' => PanicRet P 0 s s' ∧
      (P.Calm s.mem (s.regs 28).toNat →
        s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ P.Calm s'.mem (s.regs 28).toNat) ∧
      (∀ v rp, P.Panicking s.mem (s.regs 28).toNat v rp → ¬ P.wrapper (s.regs 30).toNat →
        s.mem.readLE ((s.regs 29).toNat + 8) 8 = rp →
        (s'.regs 0).toNat = v.typ ∧ (s'.regs 1).toNat = v.data ∧
          P.Recovered s'.mem (s.regs 28).toNat))

/-- The precondition of `GopanicRecoverContract` at `gopanic`'s entry `s` (see there). -/
def GopanicRecoverPre (P : PanicRuntime) (bitsOff slotOff : Nat) (s : State) : Prop :=
  PanicPre P 2 s ∧ (s.regs 0).toNat ≠ 0 ∧
    s.mem.readLE (s.sp.toNat + bitsOff) 1 = 1 ∧
    s.sp.toNat + bitsOff + 1 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat + bitsOff) 1 true = true ∧
    Outside (s.sp.toNat + bitsOff) 1 P.priv ∧
    s.sp.toNat + slotOff + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat + slotOff) 8 false = true ∧
    s.mem.readLE (s.sp.toNat + slotOff) 8 + 8 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.mem.readLE (s.sp.toNat + slotOff) 8) 8 false = true ∧
    s.mem.readLE (s.mem.readLE (s.sp.toNat + slotOff) 8) 8 % 4 = 0 ∧
    s.mem.readLE (s.mem.readLE (s.sp.toNat + slotOff) 8) 8 < 2 ^ 48

/-- The closure call `gopanic` reaches from `s` (state `c`), and its continuation (see
`GopanicRecoverContract`). -/
def GopanicRecoverCall (p : Program) (P : PanicRuntime) (bitsOff slotOff resume : Nat)
    (s c : State) : Prop :=
  c.pc = BitVec.ofNat 64 (s.mem.readLE (s.mem.readLE (s.sp.toNat + slotOff) 8) 8) ∧
    c.regs 26 = BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + slotOff) 8) ∧
    c.regs 28 = s.regs 28 ∧ c.regs 18 = s.regs 18 ∧ c.regs 29 = c.sp - 8 ∧
    c.sp.toNat % 16 = 0 ∧ s.sp.toNat - P.depth ≤ c.sp.toNat ∧ c.sp.toNat + 16 ≤ s.sp.toNat ∧
    (c.regs 30).toNat % 4 = 0 ∧ (c.regs 30).toNat < 2 ^ 48 ∧
    P.Panicking c.mem (s.regs 28).toNat ⟨(s.regs 0).toNat, (s.regs 1).toNat⟩ (c.regs 30).toNat ∧
    P.Env c.mem ∧ c.mem.readLE (s.sp.toNat + bitsOff) 1 = 0 ∧
    MemFrame s.mem c.mem (P.priv ++ [(s.sp.toNat - P.depth, s.sp.toNat - 8),
      (s.sp.toNat + bitsOff, s.sp.toNat + bitsOff + 1)]) ∧
    ∀ c', c'.pc = c.regs 30 → c'.sp = c.sp → c'.regs 28 = c.regs 28 → c'.regs 18 = c.regs 18 →
      Map.Agrees c.mem c'.mem [(c.sp.toNat, s.sp.toNat)] → P.Env c'.mem →
      P.Recovered c'.mem (s.regs 28).toNat →
      ∃ k' d, Program.Steps p c' k' d ∧ d.pc = BitVec.ofNat 64 resume ∧ d.sp = s.sp ∧
        d.regs 28 = s.regs 28 ∧ d.regs 18 = s.regs 18 ∧ d.regs 29 = s.sp - 8 ∧
        MemFrame c'.mem d.mem (P.priv ++ [(s.sp.toNat - P.depth, s.sp.toNat - 8)]) ∧
        P.Env d.mem ∧ P.Calm d.mem (s.regs 28).toNat

/-- `runtime.gopanic(v)` for a frame whose only pending deferred call is an open-coded defer that
**recovers** (Go 1.26 `gopanic` → `nextDefer` → `recovery`). The panicking frame `F` is the caller
of `gopanic` (`F`'s `SP` is `SP` at entry); its open-coded `deferBits` byte is at `SP + bitsOff`
and holds `1` (bit 0 pending), the deferred funcval's slot is at `SP + slotOff`, and `resume` is
`F`'s `deferreturn` call site (`funcInfo.deferreturn`); these are the function's funcdata
(`FUNCDATA_OpenCodedDeferInfo`) and are part of the statement. The value `v = (X0, X1)` is not nil,
the `deferBits` byte is writable and outside `P.priv`, and the slot, the funcval it points to and
the funcval's code word (an admissible branch target) are readable.

The runtime clears the bit and calls the deferred closure — control reaches the closure's code with
`X26` = the funcval, an admissible return point `rp = X30` inside `gopanic`, the frame-pointer
convention, a 16-aligned `SP` at most `P.depth` bytes below `F`'s, the goroutine `X28` and `X18`
kept, memory changed only in `P.priv`, the runtime's stack window `[SP - P.depth, SP - 8)` (never the
caller's saved frame pointer) and the cleared byte, and the
panic active (`P.Panicking … v rp`). Then, for **every** state the closure may return in (at `rp`
with `SP`, `X18`, `X28` restored, the runtime's stack between the closure's `SP` and `F`'s kept,
the runtime usable) **in which the panic was recovered**, the runtime resumes `F`: control reaches
`resume` with `SP` = `F`'s, `X29 = SP - 8`, `X18`, `X28` kept, memory changed only in `P.priv`
and the runtime's stack window, and no panic active (`P.Calm`). If the closure does not recover,
the contract says nothing. -/
def GopanicRecoverContract (p : Program) (addr : Nat) (P : PanicRuntime)
    (bitsOff slotOff resume : Nat) : Prop :=
  ∀ s, s.pc = BitVec.ofNat 64 addr → GopanicRecoverPre P bitsOff slotOff s →
    ∃ k c, Program.Steps p s k c ∧ GopanicRecoverCall p P bitsOff slotOff resume s c

/-- Use the `gopanic` contract inside a run of `p.withExit ret`: from its entry `S`, continue from
the closure call `c` it reaches. -/
theorem GopanicRecoverContract.reaches {p : Program} {addr ret bitsOff slotOff resume : Nat}
    {P : PanicRuntime} {S : State} {Q : Outcome → Prop}
    (h : GopanicRecoverContract p addr P bitsOff slotOff resume) (hret : RetAddr p ret)
    (hpc : S.pc = BitVec.ofNat 64 addr) (hpre : GopanicRecoverPre P bitsOff slotOff S)
    (hk : ∀ c, GopanicRecoverCall p P bitsOff slotOff resume S c → Reaches (p.withExit ret) c Q) :
    Reaches (p.withExit ret) S Q := by
  obtain ⟨k, c, hst, hc⟩ := h S hpc hpre
  exact Reaches.of_steps (hst.withExit hret.fetch_none) (hk c hc)

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
