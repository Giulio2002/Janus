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

def DeferprocContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (PanicPre P 1) (PanicRet P 1)
def DeferprocStackContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (PanicPre P 1) (PanicRet P 1)
def DeferprocatContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (PanicPre P 2) (PanicRet P 2)
def DeferrangefuncContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (PanicPre P 0) (PanicRet P 0)
def DeferreturnContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr (PanicPre P 0) (PanicRet P 0)

/-- `runtime.gorecover()` (amd64): `nil` when calm; the panic value when called directly by the
running deferred call (the caller is not a wrapper and its frame's return address, `[RBP + 8]` on
the frame-pointer chain at entry, is that call's return point). -/
def GorecoverContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime) : Prop :=
  Summary p addr
    (fun s => PanicPre P 0 s ∧ s.mem.accessible ((s.regs 5).toNat + 8) 8 false = true ∧
      (s.regs 5).toNat + 16 ≤ 2 ^ 48)
    (fun s s' => PanicRet P 0 s s' ∧
      (P.Calm s.mem (s.regs 14).toNat →
        s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ P.Calm s'.mem (s.regs 14).toNat) ∧
      (∀ v rp, P.Panicking s.mem (s.regs 14).toNat v rp →
        ¬ P.wrapper (s.mem.readLE (s.regs 4).toNat 8) →
        s.mem.readLE ((s.regs 5).toNat + 8) 8 = rp →
        (s'.regs 0).toNat = v.typ ∧ (s'.regs 3).toNat = v.data ∧
          P.Recovered s'.mem (s.regs 14).toNat))

/-- `runtime.gopanic(v)` for a frame with one pending open-coded defer that recovers (amd64; see
`Janus.Contracts.Panic.GopanicRecoverContract`). `F`'s body `RSP` is `RSP + 8` at entry (the
return address is pushed); `deferBits` at `F.RSP + bitsOff`, the slot at `F.RSP + slotOff`. The
closure is entered with `RDX` = the funcval, the return point `rp` at `[RSP]`, `RBP` as at entry,
and returns obeying the ABI (`RSP + 8`, `RBP`, `R14`, `X15 = 0`, `DF` clear); `F` is resumed at
`resume` with `RSP` = `F`'s, `RBP` as at entry (`F`'s frame pointer), `R14` kept, `X15 = 0`, the
direction flag clear. -/
def GopanicRecoverContract (p : Janus.Amd64.Program) (addr : Nat) (P : PanicRuntime)
    (bitsOff slotOff resume : Nat) : Prop :=
  ∀ s, s.rip = BitVec.ofNat 64 addr → PanicPre P 2 s → (s.regs 0).toNat ≠ 0 →
    s.mem.readLE ((s.regs 4).toNat + 8 + bitsOff) 1 = 1 →
    (s.regs 4).toNat + 8 + bitsOff + 1 ≤ 2 ^ 48 →
    s.mem.accessible ((s.regs 4).toNat + 8 + bitsOff) 1 true = true →
    Outside ((s.regs 4).toNat + 8 + bitsOff) 1 P.priv →
    (s.regs 4).toNat + 8 + slotOff + 8 ≤ 2 ^ 48 →
    s.mem.accessible ((s.regs 4).toNat + 8 + slotOff) 8 false = true →
    s.mem.readLE ((s.regs 4).toNat + 8 + slotOff) 8 + 8 ≤ 2 ^ 48 →
    s.mem.accessible (s.mem.readLE ((s.regs 4).toNat + 8 + slotOff) 8) 8 false = true →
    s.mem.readLE (s.mem.readLE ((s.regs 4).toNat + 8 + slotOff) 8) 8 < 2 ^ 47 →
    ∃ k c, Janus.Amd64.Program.Steps p s k c ∧
      c.rip = BitVec.ofNat 64 (s.mem.readLE (s.mem.readLE ((s.regs 4).toNat + 8 + slotOff) 8) 8) ∧
      c.regs 2 = BitVec.ofNat 64 (s.mem.readLE ((s.regs 4).toNat + 8 + slotOff) 8) ∧
      c.regs 14 = s.regs 14 ∧ c.xmm 15 = 0 ∧ c.df = false ∧
      (c.regs 4).toNat % 8 = 0 ∧ (s.regs 4).toNat - P.depth ≤ (c.regs 4).toNat ∧
      (c.regs 4).toNat + 16 ≤ (s.regs 4).toNat ∧
      c.mem.readLE (c.regs 4).toNat 8 < 2 ^ 47 ∧
      P.Panicking c.mem (s.regs 14).toNat ⟨(s.regs 0).toNat, (s.regs 3).toNat⟩
        (c.mem.readLE (c.regs 4).toNat 8) ∧
      P.Env c.mem ∧ c.mem.readLE ((s.regs 4).toNat + 8 + bitsOff) 1 = 0 ∧
      MemFrame s.mem c.mem (P.priv ++ [((s.regs 4).toNat - P.depth, (s.regs 4).toNat + 8),
        ((s.regs 4).toNat + 8 + bitsOff, (s.regs 4).toNat + 8 + bitsOff + 1)]) ∧
      c.regs 5 = s.regs 5 ∧
      ∀ c', c'.rip.toNat = c.mem.readLE (c.regs 4).toNat 8 → c'.regs 4 = c.regs 4 + 8 →
        c'.regs 14 = c.regs 14 → c'.regs 5 = c.regs 5 → c'.xmm 15 = 0 → c'.df = false →
        Map.Agrees c.mem c'.mem [((c.regs 4).toNat, (s.regs 4).toNat + 8)] → P.Env c'.mem →
        P.Recovered c'.mem (s.regs 14).toNat →
        ∃ k' d, Janus.Amd64.Program.Steps p c' k' d ∧ d.rip = BitVec.ofNat 64 resume ∧
          d.regs 4 = s.regs 4 + 8 ∧ d.regs 5 = s.regs 5 ∧ d.regs 14 = s.regs 14 ∧
          d.xmm 15 = 0 ∧ d.df = false ∧
          MemFrame c'.mem d.mem (P.priv ++ [((s.regs 4).toNat - P.depth, (s.regs 4).toNat + 8)]) ∧
          P.Env d.mem ∧ P.Calm d.mem (s.regs 14).toNat

theorem panicrangestate_panics (P : PanicRuntime) (s : State) :
    (goClass P).atStub "runtime.panicrangestate" s (P.err ErrKind.rangeState) :=
  goClass_panicStub P s (by rfl) (by decide)

end Janus.Contracts.PanicAmd64
