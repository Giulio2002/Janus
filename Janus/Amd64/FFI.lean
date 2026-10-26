import Janus.Amd64.Tactic
import Janus.Amd64.CABI
import Janus.FFI

/-!
# FFI on amd64: contracts for external functions, and the cgo boundary

The amd64 counterpart of `Janus.FFI` (read that module first): the same `Contract`,
`ReturnsC`, `RunsTo` and refinement machinery over the x86-64 model, the Go-side assumption
`CgoSpec`, the trusted `CgoCall` and the composition theorem `CgoCall.refines`.

The amd64 specifics: `runtime.cgocall(fn, arg)` takes `fn` in `RAX` and `arg` in `RBX`
(ABIInternal); `asmcgocall` calls the C wrapper with `arg` in `RDI`, `RSP + 8` 16-byte aligned
and the return address at `[RSP]` (System V); the Go caller resumes at the return address at
its `[RSP]` with `RSP + 8`, `RBP` and `R14` (`g`) restored, `X15 = 0`, the direction flag clear,
and the `g` slot of the (possibly different) thread's TLS holding `g` (`GoABI.TlsG`).
-/

namespace Janus.Amd64.FFI

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Amd64.CABI

/-- A contract for the external stubs of a program, by stub name (as in `Janus.FFI`). -/
structure Contract where
  safe : String → State → Prop
  next : String → State → State → Prop

def Contract.Refines (C₁ C₂ : Contract) : Prop :=
  ∀ f s, C₂.safe f s → C₁.safe f s ∧ ∀ s', C₁.next f s s' → C₂.next f s s'

theorem Contract.Refines.refl (C : Contract) : C.Refines C := fun _ _ h => ⟨h, fun _ h => h⟩

theorem Contract.Refines.trans {C₁ C₂ C₃ : Contract} (h₁ : C₁.Refines C₂) (h₂ : C₂.Refines C₃) :
    C₁.Refines C₃ := fun f s h =>
  let ⟨a, b⟩ := h₂ f s h
  let ⟨c, d⟩ := h₁ f s a
  ⟨c, fun s' h' => b s' (d s' h')⟩

/-- Every run from `s` returns satisfying `post`, under the contract `C` for external stubs
(see `Janus.FFI.ReturnsC`). -/
inductive ReturnsC (p : Program) (C : Contract) (post : State → Prop) : State → Prop where
  | exit {s : State} (hx : s.rip.toNat = p.exitAddr) (hp : post s) : ReturnsC p C post s
  | step {s s' : State} {w : List Nat} (hx : s.rip.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.rip.toNat = none) (hf : p.fetch s.rip.toNat = some w)
      (hst : Amd64.step w s = .ok s') (h : ReturnsC p C post s') : ReturnsC p C post s
  | ext {s : State} {st : Janus.Stub} (hx : s.rip.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.rip.toNat = some st) (hk : st.kind = .external)
      (hsafe : C.safe st.name s) (h : ∀ s', C.next st.name s s' → ReturnsC p C post s') :
      ReturnsC p C post s

/-- `s'` is a final state of some run from `s` under `C`. -/
inductive RunsTo (p : Program) (C : Contract) : State → State → Prop where
  | exit {s : State} (hx : s.rip.toNat = p.exitAddr) : RunsTo p C s s
  | step {s s₁ s' : State} {w : List Nat} (hx : s.rip.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.rip.toNat = none) (hf : p.fetch s.rip.toNat = some w)
      (hst : Amd64.step w s = .ok s₁) (h : RunsTo p C s₁ s') : RunsTo p C s s'
  | ext {s s₁ s' : State} {st : Janus.Stub} (hx : s.rip.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.rip.toNat = some st) (hk : st.kind = .external)
      (hn : C.next st.name s s₁) (h : RunsTo p C s₁ s') : RunsTo p C s s'

namespace ReturnsC

variable {p : Program} {C : Contract} {P Q : State → Prop} {s : State}

theorem mono (h : ReturnsC p C P s) (hPQ : ∀ s, P s → Q s) : ReturnsC p C Q s := by
  induction h with
  | exit hx hp => exact .exit hx (hPQ _ hp)
  | step hx hs hf hst _ ih => exact .step hx hs hf hst ih
  | ext hx hs hk hsafe _ ih => exact .ext hx hs hk hsafe ih

theorem refine {C₁ : Contract} (hR : C₁.Refines C) (h : ReturnsC p C P s) : ReturnsC p C₁ P s := by
  induction h with
  | exit hx hp => exact .exit hx hp
  | step hx hs hf hst _ ih => exact .step hx hs hf hst ih
  | @ext s st hx hs hk hsafe _ ih =>
    obtain ⟨hs₁, hn⟩ := hR st.name s hsafe
    exact .ext hx hs hk hs₁ fun s' h' => ih s' (hn s' h')

theorem runsTo {s' : State} (h : ReturnsC p C P s) (hr : RunsTo p C s s') : P s' := by
  induction hr with
  | exit hx =>
    cases h with
    | exit _ hp => exact hp
    | step hx' => exact absurd hx hx'
    | ext hx' => exact absurd hx hx'
  | step hx hs hf hst _ ih =>
    cases h with
    | exit hx' => exact absurd hx' hx
    | step _ _ hf' hst' h' =>
      rw [hf] at hf'; cases hf'; rw [hst] at hst'; cases hst'; exact ih h'
    | ext _ hs' => rw [hs] at hs'; cases hs'
  | ext hx hs hk hn _ ih =>
    cases h with
    | exit hx' => exact absurd hx' hx
    | step _ hs' => rw [hs] at hs'; cases hs'
    | ext _ hs' _ _ h' => rw [hs] at hs'; cases hs'; exact ih (h' _ hn)

theorem of_steps {k : Nat} {s' : State} (hs : Program.Steps p s k s') (h : ReturnsC p C P s') :
    ReturnsC p C P s := by
  induction hs with
  | refl => exact h
  | step hx hst hf he _ ih => exact .step hx hst hf he (ih h)

theorem of_run {n : Nat} {s' : State} (hr : p.run n s = .ok (.returned s')) (hp : P s') :
    ReturnsC p C P s := by
  induction n generalizing s with
  | zero => simp at hr
  | succ n ih =>
    rw [Program.run_succ] at hr
    by_cases hx : s.rip.toNat = p.exitAddr
    · rw [ite_eq_left hx] at hr; cases hr; exact .exit hx hp
    · rw [ite_eq_right hx] at hr
      cases hst : p.stubAt s.rip.toNat with
      | some st => simp only [hst] at hr; cases hr
      | none =>
        cases hf : p.fetch s.rip.toNat with
        | none => simp only [hst, hf] at hr; cases hr
        | some w =>
          cases he : Amd64.step w s with
          | error e => simp only [hst, hf, he] at hr; cases hr
          | ok s₁ => simp only [hst, hf, he] at hr; exact .step hx hst hf he (ih hr)

theorem of_returns (h : Returns p s P) : ReturnsC p C P s := by
  obtain ⟨n, s', hr, hp⟩ := h
  exact of_run hr hp

end ReturnsC

/-- The outcome predicate of `ReturnsC`, for `janus64_run` (see `Janus.FFI.IsReturnC`). -/
def IsReturnC (p : Program) (C : Contract) (post : State → Prop) : Outcome → Prop
  | .returned s => post s
  | .stub f .external s => C.safe f s ∧ ∀ s', C.next f s s' → ReturnsC p C post s'
  | .stub _ _ _ => False

@[simp, janus64_post] theorem isReturnC_returned (p : Program) (C : Contract)
    (post : State → Prop) (s : State) : IsReturnC p C post (.returned s) = post s := rfl
@[simp, janus64_post] theorem isReturnC_external (p : Program) (C : Contract)
    (post : State → Prop) (f : String) (s : State) : IsReturnC p C post (.stub f .external s) =
      (C.safe f s ∧ ∀ s', C.next f s s' → ReturnsC p C post s') := rfl
@[simp, janus64_post] theorem isReturnC_panic (p : Program) (C : Contract) (post : State → Prop)
    (f : String) (s : State) : IsReturnC p C post (.stub f .panic s) = False := rfl
@[simp, janus64_post] theorem isReturnC_morestack (p : Program) (C : Contract)
    (post : State → Prop) (f : String) (s : State) :
    IsReturnC p C post (.stub f .morestack s) = False := rfl
@[simp, janus64_post] theorem isReturnC_syscall (p : Program) (C : Contract)
    (post : State → Prop) (f : String) (s : State) :
    IsReturnC p C post (.stub f .syscall s) = False := rfl
@[simp, janus64_post] theorem isReturnC_trap (p : Program) (C : Contract)
    (post : State → Prop) (f : String) (s : State) :
    IsReturnC p C post (.stub f .trap s) = False := rfl

theorem ReturnsC.of_reaches {p : Program} {C : Contract} {post : State → Prop} {s : State}
    (h : Reaches p s (IsReturnC p C post)) : ReturnsC p C post s := by
  obtain ⟨n, o, hr, hq⟩ := h
  induction n generalizing s with
  | zero => simp at hr
  | succ n ih =>
    rw [Program.run_succ] at hr
    by_cases hx : s.rip.toNat = p.exitAddr
    · rw [ite_eq_left hx] at hr; cases hr; exact .exit hx hq
    · rw [ite_eq_right hx] at hr
      cases hst : p.stubAt s.rip.toNat with
      | some st =>
        simp only [hst] at hr; cases hr
        cases hk : st.kind with
        | external => rw [hk] at hq; exact .ext hx hst hk hq.1 hq.2
        | panic => rw [hk] at hq; exact hq.elim
        | morestack => rw [hk] at hq; exact hq.elim
        | syscall => rw [hk] at hq; exact hq.elim
        | trap => rw [hk] at hq; exact hq.elim
      | none =>
        cases hf : p.fetch s.rip.toNat with
        | none => simp only [hst, hf] at hr; cases hr
        | some w =>
          cases he : Amd64.step w s with
          | error e => simp only [hst, hf, he] at hr; cases hr
          | ok s₁ => simp only [hst, hf, he] at hr; exact .step hx hst hf he (ih hr)

/-! ## Specifications under a contract -/

attribute [janus64_post] CABI.cReturn_iff

/-- The Go function contract under a contract `C` for its external calls (`GoABI.Ensures` with
`ReturnsC`; on amd64 `cgocall` restores everything `GoABI.ABIReturn` asks for). -/
def EnsuresC (p : Program) (C : Contract) (entry : Nat) (args : List W64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ ret, RetAddr p ret → ∀ s, CallSetup (p.withExit ret) entry args s → pre s →
    ReturnsC (p.withExit ret) C (fun s' => ABIReturn s s' ∧ post s s') s

/-- The C function contract under a contract `C` for its external calls. -/
def CEnsuresC (p : Program) (C : Contract) (entry : Nat) (args : List W64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ ret, RetAddr p ret → ∀ s, CCall (p.withExit ret) entry args s → pre s →
    ReturnsC (p.withExit ret) C (fun s' => CReturn s s' ∧ post s s') s

theorem EnsuresC.refine {p : Program} {C₁ C₂ : Contract} {entry : Nat} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (hR : C₁.Refines C₂)
    (h : EnsuresC p C₂ entry args pre post) : EnsuresC p C₁ entry args pre post :=
  fun ret hret s hs hp => (h ret hret s hs hp).refine hR

theorem CEnsuresC.refine {p : Program} {C₁ C₂ : Contract} {entry : Nat} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (hR : C₁.Refines C₂)
    (h : CEnsuresC p C₂ entry args pre post) : CEnsuresC p C₁ entry args pre post :=
  fun ret hret s hs hp => (h ret hret s hs hp).refine hR

theorem EnsuresC.of_ensures {p : Program} {C : Contract} {entry : Nat} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (h : Ensures p entry args pre post) :
    EnsuresC p C entry args pre post :=
  fun ret hret s hs hp => .of_returns (h ret hret s hs hp)

theorem CEnsuresC.of_cEnsures {p : Program} {C : Contract} {entry : Nat} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (h : CEnsures p entry args pre post) :
    CEnsuresC p C entry args pre post :=
  fun ret hret s hs hp => .of_returns (h ret hret s hs hp)

/-- A callee `Summary` of a C function (precondition `spre`, implied by every C call state
satisfying `pre`) is a `CEnsures` when its postcondition implies `CReturn`. -/
theorem CEnsures.of_summary {p : Program} {entry : Nat} {args : List W64}
    {pre spre : State → Prop} {post post' : State → State → Prop}
    (hsum : Summary p entry spre post')
    (hpre : ∀ ret s, RetAddr p ret → CCall (p.withExit ret) entry args s → pre s → spre s)
    (hpost : ∀ s s', pre s → post' s s' → CReturn s s' ∧ post s s') :
    CEnsures p entry args pre post := by
  intro ret hret s hs hp
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hs.rip (hpre ret s hret hs hp)
  have hst' := hst.withExit hret.fetch_none
  refine returns_of_steps hst' ?_ (hpost s s' hp hq)
  rw [hr, retAddrOf, hs.ret]
  simp only [Program.withExit, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hret.lt64

/-! ## The cgo boundary -/

/-- Bytes of the goroutine stack below `RSP` that `cgocall` and the nosplit functions it calls
may write (see `Janus.FFI.cgoStackScratch`). -/
def cgoStackScratch : Nat := 1024

/-- `unsafe.Sizeof(runtime.g{})` in Go 1.26.0. -/
def gStructSize : Nat := 456

/-- Bytes free on the system stack below `RSP` for the C code. -/
def cgoCStack : Nat := 4096

/-- The byte ranges a `cgocall` from state `s` may change besides the C code's writes: the
goroutine stack below `RSP`, the spill slots of `cgocall`'s register arguments above the return
address (`[RSP+8, RSP+24)`), the `g` struct (`R14`), and the `g` slot of the thread's TLS
(`FS:-8`, which `asmcgocall` points at `g0` during the call). -/
def cgoClobber (s : State) : List (Nat × Nat) :=
  [((s.regs GoABI.regSP).toNat - cgoStackScratch, (s.regs GoABI.regSP).toNat),
   ((s.regs GoABI.regSP).toNat + 8, (s.regs GoABI.regSP).toNat + 24),
   ((s.regs regG).toNat, (s.regs regG).toNat + gStructSize),
   (s.fsBase.toNat - 8, s.fsBase.toNat)]

/-- How the Go caller resumes after `cgocall` returns: at the return address at `[RSP]`, with
`RSP + 8`, `RBP` and `R14` (`g`) restored, `X15 = 0`, the direction flag clear and memory `m`;
the goroutine may resume on another thread, so `FS` is arbitrary except that its `g` slot holds
`g` (`TlsG`); every other register, the flags, the vector registers (`ZMM` bits 511:256
included) and the opmask registers are arbitrary. `MXCSR`
keeps its control bits (the C code restores them, `CReturn.mxcsr`), its sticky status flags are
arbitrary: a caller in the Go floating-point environment (`GoABI.GoMXCSR`) is still in it
(`GoResume.goMXCSR`). The x87 FPU state is arbitrary (the C code may have raised its sticky
flags; Go code never uses it). -/
def GoResume (s s' : State) (m : Memory) : Prop :=
  ∃ regs flags xmm ymmHi fs mx x87 zh kr,
    s' = { s with regs := regs, rip := retAddrOf s, flags := flags, xmm := xmm, ymmHi := ymmHi,
                  mem := m, fsBase := fs, df := false, mxcsr := mx, x87 := x87, zmmHi := zh,
                  kreg := kr } ∧
    regs GoABI.regSP = s.regs GoABI.regSP + 8 ∧ regs GoABI.regFP = s.regs GoABI.regFP ∧ regs regG = s.regs regG ∧
    xmm xmmZero = 0 ∧ TlsG s' ∧ mx.toNat / 64 = s.mxcsr.toNat / 64

theorem GoResume.goMXCSR {s s' : State} {m : Memory} (h : GoResume s s' m)
    (hm : GoABI.GoMXCSR s) : GoABI.GoMXCSR s' := by
  obtain ⟨_, _, _, _, _, mx, _, _, _, rfl, -, -, -, -, -, hmx⟩ := h
  unfold GoABI.GoMXCSR at hm ⊢
  exact hmx.trans hm

/-- The cgo contract a Go-side theorem assumes: `runtime.cgocall` called with `RAX = fn` in a
state satisfying `G` returns (`GoResume`) with memory that agrees with `E s` outside
`cgoClobber s`. -/
def CgoSpec (fn : Nat) (G : State → Prop) (E : State → Memory) : Contract where
  safe f s := f = "runtime.cgocall" ∧ s.regs 0 = BitVec.ofNat 64 fn ∧ G s
  next f s s' := f = "runtime.cgocall" ∧ ∃ m, GoResume s s' m ∧ MemFrame (E s) m (cgoClobber s)

/-- The trusted contract of `_cgo_topofstack` (`runtime/asm_amd64.s`) during one cgo call: it
returns `T` (the calling goroutine's `stack.hi`, the same on every call while no callback moves
the stack) in `RAX`, pops the return address, preserves every other register and the memory. -/
def TopOfStack (T : W64) : Contract where
  safe f s := f = "_cgo_topofstack" ∧ (s.regs GoABI.regSP).toNat + 8 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs GoABI.regSP).toNat 8 false = true
  next f s s' := f = "_cgo_topofstack" ∧ ∃ flags,
    s' = { s with regs := setRegF (setRegF s.regs 0 T) 4 (s.regs 4 + 8), rip := retAddrOf s,
                  flags := flags }

def GoKept (s : State) (a n : Nat) (w : Bool) : Prop :=
  s.mem.accessible a n w = true ∧ Outside a n (cgoClobber s)

/-- The C call state `t` that `asmcgocall` makes for `cgocall(fn = RAX, arg = RBX)` from the Go
state `s`, returning to `ret` (trusted, see `Janus.FFI.CgoEntry`): `RIP = fn`, `RDI = arg`,
`[RSP] = ret`; the system stack (`RSP + 8` 16-byte aligned, `cgoCStack` bytes below `RSP` and
the return address writable) is not Go memory; Go memory the runtime leaves alone keeps its
bytes and accessibility; the direction flag is clear; the same thread (`FS`), and so the same
floating-point control state: the `MXCSR` control bits and the x87 control word of the Go caller
(`asmcgocall` switches only the stack and `g` and executes no `LDMXCSR`/`FLDCW`,
`runtime/asm_amd64.s`). -/
structure CgoEntry (p : Program) (s t : State) (ret : Nat) : Prop where
  rip : t.rip = s.regs 0
  arg : t.regs 7 = s.regs 3
  retSlot : t.mem.readLE (t.regs GoABI.regSP).toNat 8 = ret
  retAddr : RetAddr p ret
  stack : CStack t cgoCStack 8
  stackSep : ∀ a n w, s.mem.accessible a n w = true →
    Outside a n [((t.regs GoABI.regSP).toNat - cgoCStack, (t.regs GoABI.regSP).toNat + 8)]
  kept : ∀ a n, GoKept s a n false → t.mem.readLE a n = s.mem.readLE a n
  keptAcc : ∀ a n w, GoKept s a n w → t.mem.accessible a n w = true
  df : t.df = false
  fs : t.fsBase = s.fsBase
  /-- The x87 FPU is the caller's: nothing between the Go call and the C entry (`cgocall`,
  `entersyscall`, `asmcgocall`, all Go and Go assembly) executes an x87 instruction. -/
  x87 : t.x87 = s.x87
  mxcsr : t.mxcsr.toNat / 64 = s.mxcsr.toNat / 64
  fpucw : t.fpucw = s.fpucw

/-- The Go caller resumes from the final C state `t'` (see `Janus.FFI.CgoResumed`). -/
def CgoResumed (s t' s' : State) : Prop :=
  ∃ m, GoResume s s' m ∧ m.regions = s.mem.regions ∧
    ∀ a, Outside a 1 (cgoClobber s) →
      m.bytes a = if s.mem.accessible a 1 false then t'.mem.bytes a else s.mem.bytes a

/-- The **trusted** contract of `runtime.cgocall` on amd64 (see `Janus.FFI.CgoCall`). -/
def CgoCall (p : Program) : Contract where
  safe f s := f = "runtime.cgocall" ∧ ∀ t ret T, CgoEntry p s t ret →
    ReturnsC (p.withExit ret) (TopOfStack T) (CReturn t) t
  next f s s' := f = "runtime.cgocall" ∧ ∃ t ret T t', CgoEntry p s t ret ∧
    RunsTo (p.withExit ret) (TopOfStack T) t t' ∧ CReturn t t' ∧ CgoResumed s t' s'

/-! ### Composition -/

theorem CgoResumed.memFrame {s t' s' : State} {E : Memory} (h : CgoResumed s t' s')
    (hE : E.regions = s.mem.regions)
    (hacc : ∀ a, Outside a 1 (cgoClobber s) → s.mem.accessible a 1 false = true →
      t'.mem.bytes a = E.bytes a)
    (hna : ∀ a, Outside a 1 (cgoClobber s) → s.mem.accessible a 1 false = false →
      s.mem.bytes a = E.bytes a) :
    ∃ m, GoResume s s' m ∧ MemFrame E m (cgoClobber s) := by
  obtain ⟨m, hres, hreg, hb⟩ := h
  refine ⟨m, hres, ⟨fun a n ho => Janus.FFI.readLE_congr fun i hi => ?_, fun a n w => ?_⟩⟩
  · have ho1 := Janus.FFI.outside_one ho hi
    rw [hb _ ho1]
    cases hc : s.mem.accessible (a + i) 1 false
    · simp only [Bool.false_eq_true, ite_false]; exact hna _ ho1 hc
    · simp only [ite_true]; exact hacc _ ho1 hc
  · simp only [Janus.Arm64.Memory.accessible, hreg, hE]

/-- **Composition** (amd64): a proved `CEnsuresC` of the C wrapper at `fn` turns the Go-side
assumption `CgoSpec fn G E` into the trusted `CgoCall p`. -/
theorem CgoCall.refines {p : Program} {fn : Nat} {G : State → Prop} {E : State → Memory}
    {pre : W64 → State → Prop} {post : W64 → State → State → Prop}
    (hC : ∀ T a, CEnsuresC p (TopOfStack T) fn [a] (pre a) (post a))
    (hpre : ∀ s t ret, G s → CgoEntry p s t ret → pre (s.regs 3) t)
    (hE : ∀ s, G s → (E s).regions = s.mem.regions)
    (hacc : ∀ s t ret t', G s → CgoEntry p s t ret → CReturn t t' → post (s.regs 3) t t' →
      ∀ a, Outside a 1 (cgoClobber s) → s.mem.accessible a 1 false = true →
        t'.mem.bytes a = (E s).bytes a)
    (hna : ∀ s, G s → ∀ a, Outside a 1 (cgoClobber s) → s.mem.accessible a 1 false = false →
      s.mem.bytes a = (E s).bytes a) :
    (CgoCall p).Refines (CgoSpec fn G E) := by
  intro f s ⟨hf, hx0, hG⟩
  have hcall : ∀ t ret, CgoEntry p s t ret → CCall (p.withExit ret) fn [s.regs 3] t :=
    fun t ret he => {
      rip := by rw [he.rip, hx0]
      ret := by rw [he.retSlot]; rfl
      len := by simp [numArgRegs]
      args := fun i hi => by
        have : i = 0 := by simp at hi; omega
        subst this; simpa [CABI.argReg, CABI.intArgRegs] using he.arg
      spAligned := he.stack.1
      df := he.df }
  refine ⟨⟨hf, fun t ret T he => ?_⟩, ?_⟩
  · exact (hC T (s.regs 3) ret he.retAddr t (hcall t ret he) (hpre s t ret hG he)).mono
      fun _ h => h.1
  · rintro s' ⟨hf', t, ret, T, t', he, hrun, hcr, hres⟩
    refine ⟨hf', ?_⟩
    have hq := (hC T (s.regs 3) ret he.retAddr t (hcall t ret he) (hpre s t ret hG he)).runsTo hrun
    exact hres.memFrame (hE s hG) (hacc s t ret t' hG he hcr hq.2) (hna s hG)

end Janus.Amd64.FFI
