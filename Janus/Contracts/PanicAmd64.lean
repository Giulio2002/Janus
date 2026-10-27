import Janus.Spec.Panic
import Janus.Contracts.Panic
import Janus.Contracts.IfaceAmd64
import Janus.Amd64.Tactic

/-!
# Contracts of the Go panic/defer/recover runtime (amd64)

The amd64 counterpart of `Janus.Contracts.Panic` (see there and docs/RUNTIME-CONTRACTS.md). Same
panic-runtime model `P : Janus.Spec.PanicRuntime`, the same general defer/panic engine (the loop
over a frame's deferred calls shared by `runtime.gopanic`, `runtime.Goexit` and
`runtime.deferreturn`) with the amd64 conventions: the panic value in `RAX`/`RBX`, the goroutine in
`R14`, the closure context in `RDX`, the return address pushed by `CALL` (so the SP of the frame
that called a runtime function is `RSP + 8` at its entry), `RBP`, `R14` and `X15` preserved by
every call. The Go-level classification adds the hardware divide-by-zero fault (`#DE`), which Go
turns into `runtime.panicdivide` via `sigpanic`.
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


/-! ## Control-flow contracts (amd64)

The amd64 counterparts of `Janus.Contracts.Panic`'s contracts, with the amd64 ABIInternal frame of
the other runtime contracts (`Janus.Contracts.IfaceAmd64`): arguments in `RAX`, `RBX`, …; `CALL`
pushes the return address; `RBP`, `R14` (`g`) and `X15` (zero) preserved, `RSP + 8` on return. -/

open Janus.Contracts

/-- The precondition every returning panic-runtime call shares (amd64). -/
def PanicPre (P : PanicRuntime) (nargs : Nat) (s : State) : Prop :=
  P.Env s.mem ∧ StackGuardOK s P.depth ∧ (s.regs 4).toNat % 8 = 0 ∧
    P.depth ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 8 + 8 * nargs ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - P.depth) (P.depth + 8 + 8 * nargs) true = true ∧
    s.xmm 15 = 0 ∧ s.df = false ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    Outside ((s.regs 4).toNat - P.depth) (P.depth + 8 + 8 * nargs) P.priv

/-- A panic-runtime call returns to its caller (amd64): `RSP + 8`, `RBP`, `R14`, `X15` kept,
everything else arbitrary, memory changed only in `P.priv` and the callee stack window, the
runtime usable. -/
def PanicRet (P : PanicRuntime) (nargs : Nat) (s s' : State) : Prop :=
  ∃ r x y fl m, s' = { s with regs := MapAmd64.keepABI s.regs r, xmm := MapAmd64.keepX15 s.xmm x,
                              ymmHi := y, flags := fl, mem := m, rip := retAddrOf s } ∧
    MemFrame s.mem m (P.priv ++ MapAmd64.calleeStack s P.depth nargs) ∧ P.Env m

/-- What a caller needs to call the panic runtime (amd64), as `IfaceAmd64.CallerOK` for `P`. -/
def PanicCallerOK (P : PanicRuntime) (s : State) (frame above : Nat) : Prop :=
  P.Env s.mem ∧ StackGuardOK s (P.depth + frame) ∧ (s.regs 4).toNat % 8 = 0 ∧
    P.depth + frame ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - (P.depth + frame)) (P.depth + frame + above) true = true ∧
    Outside ((s.regs 4).toNat - (P.depth + frame)) (P.depth + frame + above) P.priv ∧
    Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - (P.depth + frame))
      (P.depth + frame + above) ∧
    Outside ((s.regs 14).toNat + 16) 8 P.priv

theorem PanicPre.of_parts {P : PanicRuntime} {s S : State} {frame above nargs : Nat}
    (hc : PanicCallerOK P s frame above) (henv : P.Env S.mem)
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (hguard : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame + above) : PanicPre P nargs S := by
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, -, -⟩ := hc
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  refine ⟨henv, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hx, hdf, hra, ?_⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hacc]; exact hg2
  · simp only [stackguard0, regG, regSP, stackguard0Offset, hg, hguard, hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hacc]; exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
  · rw [hsp]; exact Outside.of_sub hout (by omega) (by omega)

theorem PanicPre.of_caller {P : PanicRuntime} (hl : P.Laws) {s S : State}
    {frame above nargs : Nat} (hc : PanicCallerOK P s frame above)
    (hf : MemFrame s.mem S.mem [((s.regs 4).toNat - (P.depth + frame), (s.regs 4).toNat + above)])
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame + above) : PanicPre P nargs S := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, -, -⟩, -, -, -, -, hout, hgd, -⟩ := hc'
  simp only [regG, stackguard0Offset, Spec.Disjoint] at hg1 hgd
  refine PanicPre.of_parts hc (hl.env_frame _ _ henv
    (Map.Agrees.of_window hf (Outside.of_sub hout (by omega) (by omega)))) hf.accessible
    (hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)) hsp hg hx hdf hra hfr hn

theorem PanicPre.of_frame {P : PanicRuntime} {s S : State} {frame above nargs : Nat}
    (hc : PanicCallerOK P s frame above)
    (hf : MemFrame s.mem S.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + frame), (s.regs 4).toNat + above)]))
    (henv : P.Env S.mem)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame + above) : PanicPre P nargs S := by
  have hc' := hc
  obtain ⟨-, ⟨hg1, -, -⟩, -, -, -, -, -, hgd, hgo⟩ := hc'
  simp only [regG, stackguard0Offset, Spec.Disjoint] at hg1 hgd
  refine PanicPre.of_parts hc henv hf.accessible (hf.readLE _ _ ?_) hsp hg hx hdf hra hfr hn
  rw [outside_append]; exact ⟨hgo, by simp only [outside_cons, outside_nil, and_true]; omega⟩

/-- `PanicPre` at any call site inside the caller's window (amd64; see the arm64 version). -/
theorem PanicPre.of_within {P : PanicRuntime} {s S : State} {frame above nargs : Nat}
    (hc : PanicCallerOK P s frame above)
    (hf : MemFrame s.mem S.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + frame), (s.regs 4).toNat + above)]))
    (henv : P.Env S.mem) (hlo : (s.regs 4).toNat - frame ≤ (S.regs 4).toNat)
    (hhi : (S.regs 4).toNat + 8 + 8 * nargs ≤ (s.regs 4).toNat + above)
    (hal : (S.regs 4).toNat % 8 = 0) (hg : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47) :
    PanicPre P nargs S := by
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, -, hd, hb, hst, hout, hgd, hgo⟩ := hc
  simp only [regG, regSP, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd
  have hguard : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hf.readLE _ _ (by rw [outside_append]; exact ⟨hgo, by simp only [outside_cons, outside_nil, and_true]; omega⟩)
  refine ⟨henv, ⟨?_, ?_, ?_⟩, hal, ?_, ?_, ?_, hx, hdf, hra, ?_⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hf.accessible]; exact hg2
  · simp only [stackguard0, regG, regSP, stackguard0Offset, hg, hguard]; omega
  · omega
  · omega
  · rw [hf.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
  · exact Outside.of_sub hout (by omega) (by omega)


open Janus.Contracts.Panic (Frame Item DeferMode fnItems recItems openItems frameItems frameKeep bitsWin
  KeepsBut frameRecs_above recItems_above)
open Janus.Spec (frameRest frameRecs recFns)

/-- The frame's memory as the loop needs it (see `Janus.Contracts.Panic.FrameOK`), and every deferred
call's code word a canonical user address (`< 2^47`), which the indirect call needs. -/
def FrameOK (P : PanicRuntime) (m : Memory) (F : Frame) (items : List Item) : Prop :=
  Janus.Contracts.Panic.FrameOK P m F items ∧ ∀ it ∈ items, m.readLE it.fn 8 < 2 ^ 47

/-- The goroutine of an amd64 Go state: `R14`. -/
abbrev gOf (s : State) : Nat := (s.regs 14).toNat

/-- The `SP` of the frame that called the runtime function `s` is entering (`CALL` pushed the return
address): `RSP + 8`. -/
abbrev fspOf (s : State) : Nat := (s.regs 4).toNat + 8

/-- A panic-runtime call returns (amd64) and may also write the ranges `extra` (a `_defer` record
on the caller's stack). -/
def PanicRetW (P : PanicRuntime) (nargs : Nat) (extra : List (Nat × Nat)) (s s' : State) : Prop :=
  ∃ r x y fl m, s' = { s with regs := MapAmd64.keepABI s.regs r, xmm := MapAmd64.keepX15 s.xmm x,
                              ymmHi := y, flags := fl, mem := m, rip := retAddrOf s } ∧
    MemFrame s.mem m (P.priv ++ MapAmd64.calleeStack s P.depth nargs ++ extra) ∧ P.Env m

/-- `runtime.deferproc(fn)` (amd64, `RAX` = the funcval): records a heap `_defer` for the caller's
frame (`d.sp` = `RSP + 8`) on top of the goroutine's chain. -/
def DeferprocContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (fun s => PanicPre P 1 s ∧ 0 < P.room s.mem (gOf s))
    (fun s s' => PanicRet P 1 s s' ∧
      P.defers s'.mem (gOf s) = { sp := fspOf s, fns := [(s.regs 0).toNat] } :: P.defers s.mem (gOf s) ∧
      KeepsBut P (gOf s) 1 s.mem s'.mem)

/-- `runtime.deferprocStack(d)` (amd64, `RAX` = a 48-byte `_defer` on the caller's stack whose `fn`,
at `d + 24`, the compiler has set). -/
def DeferprocStackContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (fun s => PanicPre P 1 s ∧ 0 < P.room s.mem (gOf s) ∧
      (s.regs 0).toNat + 48 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 48 true = true ∧
      Outside (s.regs 0).toNat 48 P.priv)
    (fun s s' => PanicRetW P 1 [((s.regs 0).toNat, (s.regs 0).toNat + 48)] s s' ∧
      P.defers s'.mem (gOf s) =
        { sp := fspOf s, fns := [s.mem.readLE ((s.regs 0).toNat + 24) 8] } :: P.defers s.mem (gOf s) ∧
      KeepsBut P (gOf s) 1 s.mem s'.mem)

/-- `runtime.deferrangefunc()` (amd64): starts the range-over-func defer list of the caller's frame
and returns its token, a non-nil `any` (`RAX` its type word, `RBX` the token). -/
def DeferrangefuncContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (fun s => PanicPre P 0 s ∧ 0 < P.room s.mem (gOf s))
    (fun s s' => PanicRet P 0 s s' ∧ (s'.regs 0).toNat ≠ 0 ∧
      P.defers s'.mem (gOf s) =
        { sp := fspOf s, fns := [], token := some (s'.regs 3).toNat } :: P.defers s.mem (gOf s) ∧
      KeepsBut P (gOf s) 1 s.mem s'.mem)

/-- `runtime.deferprocat(fn, frame)` (amd64, `RAX` = the funcval, `RBX`/`RCX` = the token `any`). -/
def DeferprocatContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (fun s => PanicPre P 2 s ∧ 0 < P.room s.mem (gOf s) ∧
      ∃ r rest, P.defers s.mem (gOf s) = r :: rest ∧ r.token = some (s.regs 1).toNat)
    (fun s s' => PanicRet P 2 s s' ∧
      (∀ r rest, P.defers s.mem (gOf s) = r :: rest →
        P.defers s'.mem (gOf s) = { r with fns := (s.regs 0).toNat :: r.fns } :: rest) ∧
      KeepsBut P (gOf s) 1 s.mem s'.mem)

/-- `runtime.gorecover()` (amd64): `nil` (`RAX = RBX = 0`) with no active panic or with a `Goexit` or
an already recovered panic on top of the chain (changing nothing); otherwise, when called directly
by the deferred call the active panic is running — its caller is not a wrapper and the caller's
return address, `[RBP + 8]` on the frame-pointer chain at entry, is that call's return point
`P.rp` — it marks the panic recovered and returns its value (`RAX` type, `RBX` data). It keeps the
defer chain, the saved state and `room`. -/
def GorecoverContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr
    (fun s => PanicPre P 0 s ∧ s.mem.accessible ((s.regs 5).toNat + 8) 8 false = true ∧
      (s.regs 5).toNat + 16 ≤ 2 ^ 48)
    (fun s s' => PanicRet P 0 s s' ∧ P.defers s'.mem (gOf s) = P.defers s.mem (gOf s) ∧
      P.saved s'.mem (gOf s) = P.saved s.mem (gOf s) ∧ P.rp s'.mem (gOf s) = P.rp s.mem (gOf s) ∧
      P.room s.mem (gOf s) ≤ P.room s'.mem (gOf s) ∧
      ((P.panics s.mem (gOf s) = [] ∨ ∃ r rs, P.panics s.mem (gOf s) = r :: rs ∧
          (r.goexit = true ∨ r.recovered = true)) →
        s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ P.panics s'.mem (gOf s) = P.panics s.mem (gOf s)) ∧
      (∀ r rs, P.panics s.mem (gOf s) = r :: rs → r.goexit = false → r.recovered = false →
        ¬ P.wrapper (s.mem.readLE (s.regs 4).toNat 8) →
        s.mem.readLE ((s.regs 5).toNat + 8) 8 = P.rp s.mem (gOf s) →
        (s'.regs 0).toNat = r.arg.typ ∧ (s'.regs 3).toNat = r.arg.data ∧
          P.panics s'.mem (gOf s) = { r with recovered := true } :: rs))

/-! ### Running a frame's deferred calls (amd64)

The loop of `Janus.Contracts.Panic.Engine`, with the amd64 conventions (see there for the account
of the loop). -/

/-- The runtime's stack window below the frame (amd64): `[F.sp - P.depth, F.sp - 8)`, below the
return-address slot of the call into the runtime. -/
def rtWin (P : PanicRuntime) (F : Frame) : List (Nat × Nat) := [(F.sp - P.depth, F.sp - 8)]

/-- A deferred call as the runtime makes it (amd64): control at the funcval's code word, the closure
context `RDX` = the funcval, `R14` the goroutine, `X15 = 0`, the direction flag clear, an 8-aligned
`RSP` pointing at the return address, at most `P.depth` bytes below the frame's `SP`
and below it, with an admissible return point there, the runtime usable. -/
def DeferCall (P : PanicRuntime) (g : W64) (fsp fn : Nat) (e : State) : Prop :=
  e.rip = BitVec.ofNat 64 (e.mem.readLE fn 8) ∧ e.regs 2 = BitVec.ofNat 64 fn ∧ e.regs 14 = g ∧
    e.xmm 15 = 0 ∧ e.df = false ∧ (e.regs 4).toNat % 8 = 0 ∧
    fsp - P.depth ≤ (e.regs 4).toNat ∧ (e.regs 4).toNat + 16 ≤ fsp ∧
    e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 47 ∧ P.Env e.mem

/-- A deferred call `e` returned normally in `e'` (amd64): at its return point with `RSP` popped,
`R14`, `RBP`, `X15` and the direction flag restored, the runtime's stack above the call's return
address, and the memory `keep`, unchanged, the runtime usable, the defer chain and saved state as
at the call, no room consumed. -/
def DeferReturned (P : PanicRuntime) (g : W64) (fsp : Nat) (keep : List (Nat × Nat)) (e e' : State) :
    Prop :=
  e'.rip.toNat = e.mem.readLE (e.regs 4).toNat 8 ∧ e'.regs 4 = e.regs 4 + 8 ∧ e'.regs 14 = g ∧
    e'.regs 5 = e.regs 5 ∧ e'.xmm 15 = 0 ∧ e'.df = false ∧
    Map.Agrees e.mem e'.mem (((e.regs 4).toNat + 8, fsp) :: keep) ∧ P.Env e'.mem ∧
    P.defers e'.mem g.toNat = P.defers e.mem g.toNat ∧
    P.saved e'.mem g.toNat = P.saved e.mem g.toNat ∧ P.room e.mem g.toNat ≤ P.room e'.mem g.toNat

/-- What `runtime.recovery` does after the deferred call (whose item is `it`) returned in `e'` with
the panic recovered (amd64): it resumes the frame at its `deferreturn` call with `RSP` the frame's
and `RBP` its frame pointer (`bound - 8`), `R14` kept, `X15 = 0`, the direction flag clear, memory
changed only in `P.priv` and the runtime's window; it drops every panic started at or below the
frame; if the frame still has open-coded defers pending, it leaves them for `deferreturn`
(`saved`). -/
def Recovers (p : Janus.Amd64.Program) (P : PanicRuntime) (g : W64) (F : Frame) (it : Item)
    (e' : State) : Prop :=
  ∃ k d, Janus.Amd64.Program.Steps p e' k d ∧ d.rip = BitVec.ofNat 64 F.resume ∧ d.regs 4 = BitVec.ofNat 64 F.sp ∧
    d.regs 5 = BitVec.ofNat 64 (F.bound - 8) ∧ d.regs 14 = g ∧ d.xmm 15 = 0 ∧ d.df = false ∧
    MemFrame e'.mem d.mem (P.priv ++ rtWin P F) ∧ P.Env d.mem ∧
    P.panics d.mem g.toNat = (P.panics e'.mem g.toNat).dropWhile (·.start ≤ F.sp) ∧
    P.defers d.mem g.toNat = P.defers e'.mem g.toNat ∧
    P.saved d.mem g.toNat = (if it.bits.getD 0 = 0 then none else F.openAt) ∧
    P.room e'.mem g.toNat ≤ P.room d.mem g.toNat

/-- The loop over a frame's deferred calls (amd64; see `Janus.Contracts.Panic.Engine`). -/
def Engine (p : Janus.Amd64.Program) (P : PanicRuntime) (U : State → Nat → Nat → Prop) (g : W64)
    (F : Frame) (keep : List (Nat × Nat)) (mode : DeferMode)
    (Fin : List PanicRec → Nat → State → State → Prop) :
    List PanicRec → Nat → List Item → State → Prop
  | ch, rm, [], c => ∃ k d, Janus.Amd64.Program.Steps p c k d ∧ Fin ch rm c d
  | ch, rm, it :: rest, c => ∃ k e, Janus.Amd64.Program.Steps p c k e ∧ DeferCall P g F.sp it.fn e ∧
      MemFrame c.mem e.mem (P.priv ++ rtWin P F ++ bitsWin F) ∧
      (∀ b ba sa, it.bits = some b → F.openAt = some (ba, sa) → e.mem.readLE ba 1 = b) ∧
      P.defers e.mem g.toNat = it.chain ∧ P.panics e.mem g.toNat = ch ∧
      rm ≤ P.room e.mem g.toNat ∧
      (if mode = .ret then P.rp e.mem g.toNat = P.rp c.mem g.toNat ∧ P.saved e.mem g.toNat = none
       else P.rp e.mem g.toNat = e.mem.readLE (e.regs 4).toNat 8 ∧ P.saved e.mem g.toNat = P.saved c.mem g.toNat) ∧
      (∀ e', DeferReturned P g F.sp keep e e' →
        (P.panics e'.mem g.toNat = ch → Engine p P U g F keep mode Fin ch rm rest e') ∧
        (mode = .panic → ∀ r rs, ch = r :: rs →
          P.panics e'.mem g.toNat = { r with recovered := true } :: rs →
          (∀ q ∈ (P.panics e'.mem g.toNat).takeWhile (·.start ≤ F.sp), q.goexit = false) →
          Recovers p P g F it e')) ∧
      (mode = .panic → ∀ u r2, U u g.toNat (e.regs 4).toNat →
        Map.Agrees e.mem u.mem (((e.regs 4).toNat, F.sp) :: keep) → P.Env u.mem →
        P.defers u.mem g.toNat = P.defers e.mem g.toNat →
        P.saved u.mem g.toNat = P.saved e.mem g.toNat →
        P.panics u.mem g.toNat = r2 :: ch → r2.goexit = false → r2.recovered = false →
        r2.start ≤ (e.regs 4).toNat → rm ≤ P.room u.mem g.toNat + 1 →
        Engine p P U g F keep mode Fin (r2 :: ch) (rm - 1) rest u)

/-- The end of a panic's or `Goexit`'s loop over frame `F` (entered with defer chain `ds`): the
runtime unwinds past the frame (`U d g F.bound`) with the panic chain `ch`, the frame's records
popped, memory changed only in `P.priv`, its window and the `deferBits` byte, the saved
open-coded state kept. -/
def LeftFrame (P : PanicRuntime) (U : State → Nat → Nat → Prop) (g : W64) (F : Frame)
    (ds : List DeferRec) (ch : List PanicRec) (rm : Nat) (c d : State) : Prop :=
  U d g.toNat F.bound ∧ P.panics d.mem g.toNat = ch ∧ P.defers d.mem g.toNat = frameRest F.sp ds ∧
    MemFrame c.mem d.mem (P.priv ++ rtWin P F ++ bitsWin F) ∧ P.Env d.mem ∧ rm ≤ P.room d.mem g.toNat ∧
    P.saved d.mem g.toNat = P.saved c.mem g.toNat

/-- The frame of `fi` whose `SP` is `sp` as the runtime finds it when a panic or `Goexit` reaches it
(see `Janus.Contracts.Panic.frameOf`). -/
def frameOf (fi : FuncInfo) (sp : Nat) (m : Memory) : Frame :=
  Janus.Contracts.Panic.frameOf fi sp m

/-- The precondition of `runtime.gopanic(v)` (amd64) at its entry `s`, called from a frame of `fi`
(`F.sp = RSP + 8`): the shared frame (`PanicPre`, two argument registers), `v` (`RAX`, `RBX`) not nil,
room for its `_panic`, the frame's `deferBits` byte readable and outside `P.priv`, and the frame's
memory as the loop needs it. -/
def GopanicPre (P : PanicRuntime) (fi : FuncInfo) (s : State) : Prop :=
  PanicPre P 2 s ∧ (s.regs 0).toNat ≠ 0 ∧ 0 < P.room s.mem (gOf s) ∧
    (fi.openDefer.isSome → s.mem.accessible (fi.bitsAt (fspOf s)) 1 false = true ∧
      Outside (fi.bitsAt (fspOf s)) 1 P.priv) ∧
    FrameOK P s.mem (frameOf fi (fspOf s) s.mem)
      (frameItems s.mem (frameOf fi (fspOf s) s.mem) (P.defers s.mem (gOf s)))

/-- **`runtime.gopanic(v)`** (amd64; see `Janus.Contracts.Panic.GopanicContract`). The function of
`T` containing the return address `[RSP]` is the caller's. -/
def GopanicContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime)
    (U : State → Nat → Nat → Prop) (T : List FuncInfo) : Prop :=
  ∀ s fi, s.rip = BitVec.ofNat 64 addr → FuncInfo.find T (s.mem.readLE (s.regs 4).toNat 8) = some fi →
    GopanicPre P fi s →
    Engine p P U (s.regs 14) (frameOf fi (fspOf s) s.mem)
      (frameKeep s.mem (frameOf fi (fspOf s) s.mem)
        (frameItems s.mem (frameOf fi (fspOf s) s.mem) (P.defers s.mem (gOf s))))
      .panic (LeftFrame P U (s.regs 14) (frameOf fi (fspOf s) s.mem) (P.defers s.mem (gOf s)))
      ({ arg := ⟨(s.regs 0).toNat, (s.regs 3).toNat⟩, start := fspOf s } :: P.panics s.mem (gOf s))
      (P.room s.mem (gOf s) - 1)
      (frameItems s.mem (frameOf fi (fspOf s) s.mem) (P.defers s.mem (gOf s))) s

/-- The precondition of `runtime.Goexit()` (amd64) called from a frame of `fi`. -/
def GoexitPre (P : PanicRuntime) (fi : FuncInfo) (s : State) : Prop :=
  PanicPre P 0 s ∧ 0 < P.room s.mem (gOf s) ∧
    (fi.openDefer.isSome → s.mem.accessible (fi.bitsAt (fspOf s)) 1 false = true ∧
      Outside (fi.bitsAt (fspOf s)) 1 P.priv) ∧
    FrameOK P s.mem (frameOf fi (fspOf s) s.mem)
      (frameItems s.mem (frameOf fi (fspOf s) s.mem) (P.defers s.mem (gOf s)))

/-- **`runtime.Goexit()`** (amd64; see `Janus.Contracts.Panic.GoexitContract`). -/
def GoexitContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime)
    (U : State → Nat → Nat → Prop) (T : List FuncInfo) : Prop :=
  ∀ s fi, s.rip = BitVec.ofNat 64 addr → FuncInfo.find T (s.mem.readLE (s.regs 4).toNat 8) = some fi →
    GoexitPre P fi s →
    Engine p P U (s.regs 14) (frameOf fi (fspOf s) s.mem)
      (frameKeep s.mem (frameOf fi (fspOf s) s.mem)
        (frameItems s.mem (frameOf fi (fspOf s) s.mem) (P.defers s.mem (gOf s))))
      .goexit (LeftFrame P U (s.regs 14) (frameOf fi (fspOf s) s.mem) (P.defers s.mem (gOf s)))
      ({ arg := ⟨0, 0⟩, goexit := true, start := fspOf s } :: P.panics s.mem (gOf s))
      (P.room s.mem (gOf s) - 1)
      (frameItems s.mem (frameOf fi (fspOf s) s.mem) (P.defers s.mem (gOf s))) s

/-- The frame `deferreturn` runs (its caller: `SP = RSP + 8` at entry): the open-coded defers a
recovery left pending (`P.saved`), then the frame's records. -/
def retFrame (P : PanicRuntime) (s : State) : Frame :=
  { sp := fspOf s, bound := fspOf s, resume := 0, openAt := P.saved s.mem (gOf s) }

/-- The end of `deferreturn`'s loop: it returns to its caller (`RSP` popped past the return
address, `RBP`, `R14`, `X15`, `DF` as at entry), memory changed only in `P.priv`, its window and the
`deferBits` byte, the frame's records popped, `saved` cleared. -/
def RetFin (P : PanicRuntime) (s : State) (ds : List DeferRec) (ch : List PanicRec) (rm : Nat)
    (c d : State) : Prop :=
  d.rip.toNat = s.mem.readLE (s.regs 4).toNat 8 ∧ d.regs 4 = s.regs 4 + 8 ∧ d.regs 14 = s.regs 14 ∧
    d.regs 5 = s.regs 5 ∧ d.xmm 15 = 0 ∧ d.df = false ∧
    MemFrame c.mem d.mem (P.priv ++ rtWin P (retFrame P s) ++ bitsWin (retFrame P s)) ∧
    P.Env d.mem ∧ P.panics d.mem (gOf s) = ch ∧ P.defers d.mem (gOf s) = frameRest (fspOf s) ds ∧
    P.saved d.mem (gOf s) = none ∧ P.rp d.mem (gOf s) = P.rp s.mem (gOf s) ∧ rm ≤ P.room d.mem (gOf s)

/-- The precondition of `runtime.deferreturn()` (amd64). -/
def DeferreturnPre (P : PanicRuntime) (s : State) : Prop :=
  PanicPre P 0 s ∧
    FrameOK P s.mem (retFrame P s) (frameItems s.mem (retFrame P s) (P.defers s.mem (gOf s)))

/-- **`runtime.deferreturn()`** (amd64; see `Janus.Contracts.Panic.DeferreturnContract`). -/
def DeferreturnContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime)
    (U : State → Nat → Nat → Prop) : Prop :=
  ∀ s, s.rip = BitVec.ofNat 64 addr → DeferreturnPre P s →
    Engine p P U (s.regs 14) (retFrame P s)
      (frameKeep s.mem (retFrame P s) (frameItems s.mem (retFrame P s) (P.defers s.mem (gOf s))))
      .ret (RetFin P s (P.defers s.mem (gOf s))) (P.panics s.mem (gOf s)) (P.room s.mem (gOf s))
      (frameItems s.mem (retFrame P s) (P.defers s.mem (gOf s))) s

/-- The Go-level classification with the panic runtime's unwinding states (amd64): as `goClass`, and
a state the runtime unwinds past the call's frame from (`U s g s₀.RSP`, `s₀` the call state, whose
`RSP` is the call's entry `SP`) is a panic with the active panic's value (`atLeave`) or, for a
`Goexit`, the `Goexit` outcome (`atExit`). -/
def goClassU (P : PanicRuntime) (U : State → Nat → Nat → Prop) (s₀ : State) : GoClass :=
  { atStub := (goClass P).atStub, atFault := (goClass P).atFault,
    atLeave := fun s v => U s (gOf s₀) (s₀.regs 4).toNat ∧
      ∃ r rs, P.panics s.mem (gOf s₀) = r :: rs ∧ r.arg = v ∧ r.goexit = false,
    atExit := fun s => U s (gOf s₀) (s₀.regs 4).toNat ∧
      ∃ r rs, P.panics s.mem (gOf s₀) = r :: rs ∧ r.goexit = true }

/-- Use the `gopanic` contract at a call `S` inside a proof of a `GoReturns` goal at `S`. -/
theorem GopanicContract.apply {p p' : Janus.Amd64.Program} {addr : Nat} {P : PanicRuntime}
    {U : State → Nat → Nat → Prop} {T : List FuncInfo} {S : State} {fi : FuncInfo} {C : GoClass}
    {Q : GoOutcome → Prop} (h : GopanicContract p addr P U T) (hpc : S.rip = BitVec.ofNat 64 addr)
    (hfi : FuncInfo.find T (S.mem.readLE (S.regs 4).toNat 8) = some fi) (hpre : GopanicPre P fi S)
    (k : Engine p P U (S.regs 14) (frameOf fi (fspOf S) S.mem)
      (frameKeep S.mem (frameOf fi (fspOf S) S.mem)
        (frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S))))
      .panic (LeftFrame P U (S.regs 14) (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S)))
      ({ arg := ⟨(S.regs 0).toNat, (S.regs 3).toNat⟩, start := fspOf S } :: P.panics S.mem (gOf S))
      (P.room S.mem (gOf S) - 1)
      (frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S))) S →
      GoReturns p' C S Q) : GoReturns p' C S Q :=
  k (h S fi hpc hfi hpre)

/-- Use the `Goexit` contract at a call `S`. -/
theorem GoexitContract.apply {p p' : Janus.Amd64.Program} {addr : Nat} {P : PanicRuntime}
    {U : State → Nat → Nat → Prop} {T : List FuncInfo} {S : State} {fi : FuncInfo} {C : GoClass}
    {Q : GoOutcome → Prop} (h : GoexitContract p addr P U T) (hpc : S.rip = BitVec.ofNat 64 addr)
    (hfi : FuncInfo.find T (S.mem.readLE (S.regs 4).toNat 8) = some fi) (hpre : GoexitPre P fi S)
    (k : Engine p P U (S.regs 14) (frameOf fi (fspOf S) S.mem)
      (frameKeep S.mem (frameOf fi (fspOf S) S.mem)
        (frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S))))
      .goexit (LeftFrame P U (S.regs 14) (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S)))
      ({ arg := ⟨0, 0⟩, goexit := true, start := fspOf S } :: P.panics S.mem (gOf S))
      (P.room S.mem (gOf S) - 1)
      (frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S))) S →
      GoReturns p' C S Q) : GoReturns p' C S Q :=
  k (h S fi hpc hfi hpre)

/-- Use the `deferreturn` contract at a call `S` inside a proof of a `GoReturns` goal at `S`. -/
theorem DeferreturnContract.apply {p p' : Janus.Amd64.Program} {addr : Nat} {P : PanicRuntime}
    {U : State → Nat → Nat → Prop} {S : State} {C : GoClass} {Q : GoOutcome → Prop}
    (h : DeferreturnContract p addr P U) (hpc : S.rip = BitVec.ofNat 64 addr)
    (hpre : DeferreturnPre P S)
    (k : Engine p P U (S.regs 14) (retFrame P S)
      (frameKeep S.mem (retFrame P S) (frameItems S.mem (retFrame P S) (P.defers S.mem (gOf S))))
      .ret (RetFin P S (P.defers S.mem (gOf S))) (P.panics S.mem (gOf S)) (P.room S.mem (gOf S))
      (frameItems S.mem (retFrame P S) (P.defers S.mem (gOf S))) S → GoReturns p' C S Q) :
    GoReturns p' C S Q :=
  k (h S hpc hpre)

/-- Name the state of a `GoReturns` goal (to replace a large symbolic state by its facts). -/
theorem _root_.Janus.Amd64.GoABI.GoReturns.name {p : Janus.Amd64.Program} {C : GoClass} {S : State}
    {Q : GoOutcome → Prop} (h : ∀ S', S' = S → GoReturns p C S' Q) : GoReturns p C S Q := h S rfl

/-- Name the state of a `ReachesRet` goal. -/
theorem _root_.Janus.Amd64.Tactic.ReachesRet.name {p : Janus.Amd64.Program} {tgt : W64} {S : State}
    {Q : State → Prop} (h : ∀ S', S' = S → ReachesRet p tgt S' Q) : ReachesRet p tgt S Q := h S rfl

/-- A deferred call that returned at its return point with `RSP`, `RBP`, `R14`, `X15`, `DF`
restored and wrote only the window `[lo, hi)`, outside `P.priv`, the runtime's stack above the
call's return address and the memory the loop reads again, returned as `DeferReturned` says, with
the panic chain unchanged. -/
theorem DeferReturned.of_window {P : PanicRuntime} (hl : P.Laws) {g : W64} {fsp : Nat}
    {keep : List (Nat × Nat)} {e e' : State} {lo hi : Nat}
    (hpc : e'.rip.toNat = e.mem.readLE (e.regs 4).toNat 8) (hsp : e'.regs 4 = e.regs 4 + 8)
    (hg : e'.regs 14 = g) (hbp : e'.regs 5 = e.regs 5) (hx : e'.xmm 15 = 0) (hdf : e'.df = false)
    (henv : P.Env e.mem) (hf : MemFrame e.mem e'.mem [(lo, hi)])
    (ho : Outside lo (hi - lo) (P.priv ++ ((e.regs 4).toNat + 8, fsp) :: keep)) :
    DeferReturned P g fsp keep e e' ∧ P.panics e'.mem g.toNat = P.panics e.mem g.toNat := by
  rw [outside_append] at ho
  have hp : Map.Agrees e.mem e'.mem P.priv := Map.Agrees.of_window hf ho.1
  exact ⟨⟨hpc, hsp, hg, hbp, hx, hdf, Map.Agrees.of_window hf ho.2, hl.env_frame _ _ henv hp,
    hl.defers_frame _ _ _ hp, hl.saved_frame _ _ _ hp, (hl.room_frame _ _ _ hp).symm ▸ Nat.le_refl _⟩,
    hl.panics_frame _ _ _ hp⟩

/-- The empty range at `0` is outside every list of ranges. -/
theorem outside_zero : ∀ rs : List (Nat × Nat), Outside 0 0 rs
  | [] => trivial
  | (lo, hi) :: rs => ⟨Or.inl (by omega), outside_zero rs⟩

/-- A deferred call that changed nothing in memory and returned (`RET`) as `DeferReturned` says (the
chain of panics and the record chain are those at the call). -/
theorem DeferReturned.of_same {P : PanicRuntime} (hl : P.Laws) {g : W64} {fsp : Nat}
    {keep : List (Nat × Nat)} {e e' : State} (hpc : e'.rip.toNat = e.mem.readLE (e.regs 4).toNat 8)
    (hsp : e'.regs 4 = e.regs 4 + 8) (hg : e'.regs 14 = g) (hbp : e'.regs 5 = e.regs 5)
    (hx : e'.xmm 15 = 0) (hdf : e'.df = false) (hm : e'.mem = e.mem) (henv : P.Env e.mem) :
    DeferReturned P g fsp keep e e' ∧ P.panics e'.mem g.toNat = P.panics e.mem g.toNat :=
  DeferReturned.of_window hl hpc hsp hg hbp hx hdf henv (lo := 0) (hi := 0)
    (by rw [hm]; exact MemFrame.refl _ _) (outside_zero _)

/-- Run to a call of a contract (`ReachesRet` with the contract's address as the target), then
continue at the call with a `GoReturns`. -/
theorem _root_.Janus.Amd64.GoABI.GoReturns.of_reachesRet_exit {p : Janus.Amd64.Program}
    {C : GoClass} {s : State} {tgt : W64} {ret : Nat} {Q : GoOutcome → Prop} (hret : p.fetch ret = none)
    (h : ReachesRet p tgt s (fun s' => GoReturns (p.withExit ret) C s' Q)) :
    GoReturns (p.withExit ret) C s Q := by
  obtain ⟨k, s', hk, -, hq⟩ := h
  exact GoReturns.of_steps (hk.withExit hret) hq

theorem Engine_nil {p : Janus.Amd64.Program} {P : PanicRuntime} {U : State → Nat → Nat → Prop} {g : W64}
    {F : Frame} {keep : List (Nat × Nat)} {mode : DeferMode}
    {Fin : List PanicRec → Nat → State → State → Prop} {ch : List PanicRec} {rm : Nat} {c : State} :
    Engine p P U g F keep mode Fin ch rm [] c = ∃ k d, Janus.Amd64.Program.Steps p c k d ∧ Fin ch rm c d := by
  simp only [Engine]

theorem Engine_cons {p : Janus.Amd64.Program} {P : PanicRuntime} {U : State → Nat → Nat → Prop} {g : W64}
    {F : Frame} {keep : List (Nat × Nat)} {mode : DeferMode}
    {Fin : List PanicRec → Nat → State → State → Prop} {ch : List PanicRec} {rm : Nat} {c : State}
    {it : Item} {rest : List Item} :
    Engine p P U g F keep mode Fin ch rm (it :: rest) c =
      ∃ k e, Janus.Amd64.Program.Steps p c k e ∧ DeferCall P g F.sp it.fn e ∧
      MemFrame c.mem e.mem (P.priv ++ rtWin P F ++ bitsWin F) ∧
      (∀ b ba sa, it.bits = some b → F.openAt = some (ba, sa) → e.mem.readLE ba 1 = b) ∧
      P.defers e.mem g.toNat = it.chain ∧ P.panics e.mem g.toNat = ch ∧
      rm ≤ P.room e.mem g.toNat ∧
      (if mode = .ret then P.rp e.mem g.toNat = P.rp c.mem g.toNat ∧ P.saved e.mem g.toNat = none
       else P.rp e.mem g.toNat = e.mem.readLE (e.regs 4).toNat 8 ∧ P.saved e.mem g.toNat = P.saved c.mem g.toNat) ∧
      (∀ e', DeferReturned P g F.sp keep e e' →
        (P.panics e'.mem g.toNat = ch → Engine p P U g F keep mode Fin ch rm rest e') ∧
        (mode = .panic → ∀ r rs, ch = r :: rs →
          P.panics e'.mem g.toNat = { r with recovered := true } :: rs →
          (∀ q ∈ (P.panics e'.mem g.toNat).takeWhile (·.start ≤ F.sp), q.goexit = false) →
          Recovers p P g F it e')) ∧
      (mode = .panic → ∀ u r2, U u g.toNat (e.regs 4).toNat →
        Map.Agrees e.mem u.mem (((e.regs 4).toNat, F.sp) :: keep) → P.Env u.mem →
        P.defers u.mem g.toNat = P.defers e.mem g.toNat →
        P.saved u.mem g.toNat = P.saved e.mem g.toNat →
        P.panics u.mem g.toNat = r2 :: ch → r2.goexit = false → r2.recovered = false →
        r2.start ≤ (e.regs 4).toNat → rm ≤ P.room u.mem g.toNat + 1 →
        Engine p P U g F keep mode Fin (r2 :: ch) (rm - 1) rest u) := by
  simp only [Engine]

/-- The loop over a frame's calls is closed under a runtime prefix that writes only the loop's own
memory and keeps `saved` and `rp`. -/
theorem Engine.of_prefix {p : Janus.Amd64.Program} {P : PanicRuntime} {U : State → Nat → Nat → Prop}
    {g : W64} {F : Frame} {keep : List (Nat × Nat)} {mode : DeferMode}
    {Fin : List PanicRec → Nat → State → State → Prop} {c c' : State} {j : Nat}
    (hFin : ∀ ch rm d, Fin ch rm c' d → Fin ch rm c d) (hst : Janus.Amd64.Program.Steps p c j c')
    (hm : MemFrame c.mem c'.mem (P.priv ++ rtWin P F ++ bitsWin F))
    (hsaved : P.saved c'.mem g.toNat = P.saved c.mem g.toNat)
    (hrp : P.rp c'.mem g.toNat = P.rp c.mem g.toNat) :
    ∀ {ch : List PanicRec} {rm : Nat} {L : List Item},
      Engine p P U g F keep mode Fin ch rm L c' → Engine p P U g F keep mode Fin ch rm L c
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

theorem LeftFrame.prefix {P : PanicRuntime} {U : State → Nat → Nat → Prop} {g : W64} {F : Frame}
    {ds : List DeferRec} {c c' : State} (hm : MemFrame c.mem c'.mem (P.priv ++ rtWin P F ++ bitsWin F))
    (hsv : P.saved c'.mem g.toNat = P.saved c.mem g.toNat)
    {ch : List PanicRec} {rm : Nat} {d : State} (h : LeftFrame P U g F ds ch rm c' d) :
    LeftFrame P U g F ds ch rm c d := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, hm.trans h4 fun a n h => ⟨h, h⟩, h5, h6, h7.trans hsv⟩

theorem RetFin.prefix {P : PanicRuntime} {s : State} {ds : List DeferRec} {c c' : State}
    (hm : MemFrame c.mem c'.mem (P.priv ++ rtWin P (retFrame P s) ++ bitsWin (retFrame P s)))
    {ch : List PanicRec} {rm : Nat} {d : State} (h : RetFin P s ds ch rm c' d) : RetFin P s ds ch rm c d := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, hm.trans h7 fun a n h => ⟨h, h⟩, h8, h9, h10, h11, h12, h13⟩

theorem panicrangestate_panics (P : PanicRuntime) (s : State) :
    (goClass P).atStub "runtime.panicrangestate" s (P.err ErrKind.rangeState) :=
  goClass_panicStub P s (by rfl) (by decide)

end Janus.Contracts.PanicAmd64
