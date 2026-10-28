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


/-! ## Combining contracts, totality (as in `Janus.FFI`) -/

def Contract.plus (C₁ C₂ : Contract) : Contract where
  safe f s := C₁.safe f s ∨ C₂.safe f s
  next f s s' := (C₁.safe f s ∧ C₁.next f s s') ∨ (C₂.safe f s ∧ C₂.next f s s')

def Contract.Disjoint (C D : Contract) : Prop := ∀ f s s', C.safe f s → D.safe f s' → False

theorem Contract.Refines.plus_left {C₁ C₂ : Contract} (hd : C₂.Disjoint C₁) :
    (C₁.plus C₂).Refines C₁ := fun f s h =>
  ⟨.inl h, fun _ hn => hn.elim (fun h' => h'.2) (fun h' => (hd f s s h'.1 h).elim)⟩

theorem Contract.Refines.plus_right {C₁ C₂ : Contract} (hd : C₁.Disjoint C₂) :
    (C₁.plus C₂).Refines C₂ := fun f s h =>
  ⟨.inr h, fun _ hn => hn.elim (fun h' => (hd f s s h'.1 h).elim) (fun h' => h'.2)⟩

theorem Contract.Refines.plus {A₁ A₂ B₁ B₂ : Contract} (h₁ : A₁.Refines B₁) (h₂ : A₂.Refines B₂)
    (d₁ : A₁.Disjoint B₂) (d₂ : A₂.Disjoint B₁) : (A₁.plus A₂).Refines (B₁.plus B₂) := by
  intro f s hs
  refine ⟨hs.elim (fun h => .inl (h₁ f s h).1) (fun h => .inr (h₂ f s h).1), fun s' hn => ?_⟩
  rcases hn with ⟨ha, hn⟩ | ⟨ha, hn⟩
  · rcases hs with hb | hb
    · exact .inl ⟨hb, (h₁ f s hb).2 s' hn⟩
    · exact (d₁ f s s ha hb).elim
  · rcases hs with hb | hb
    · exact (d₂ f s s ha hb).elim
    · exact .inr ⟨hb, (h₂ f s hb).2 s' hn⟩

/-- Every call the contract allows has a result. -/
def Contract.Total (C : Contract) : Prop := ∀ f s, C.safe f s → ∃ s', C.next f s s'

theorem Contract.Total.plus {C₁ C₂ : Contract} (h₁ : C₁.Total) (h₂ : C₂.Total) :
    (C₁.plus C₂).Total := fun f s hs => hs.elim
  (fun h => let ⟨s', h'⟩ := h₁ f s h; ⟨s', .inl ⟨h, h'⟩⟩)
  (fun h => let ⟨s', h'⟩ := h₂ f s h; ⟨s', .inr ⟨h, h'⟩⟩)

def Contract.none : Contract := ⟨fun _ _ => False, fun _ _ _ => False⟩

theorem none_total : Contract.none.Total := fun _ _ h => h.elim

theorem ReturnsC.exists_runsTo {p : Program} {C : Contract} {P : State → Prop} {s : State}
    (hC : C.Total) (h : ReturnsC p C P s) : ∃ s', RunsTo p C s s' ∧ P s' := by
  induction h with
  | exit hx hp => exact ⟨_, .exit hx, hp⟩
  | step hx hs hf hst _ ih =>
    obtain ⟨s', hr, hp⟩ := ih; exact ⟨s', .step hx hs hf hst hr, hp⟩
  | @ext s st hx hs hk hsafe _ ih =>
    obtain ⟨s₁, hn⟩ := hC st.name s hsafe
    obtain ⟨s', hr, hp⟩ := ih s₁ hn
    exact ⟨s', .ext hx hs hk hn hr, hp⟩

/-! ## C function pointers (amd64; see `Janus.FFI.CFuncIs`) -/

/-- The code at `f` (a canonical user address) is a C function: from every state at `f`
satisfying `pre`, it returns to `[RSP]` restoring `CReturn` and satisfying `post`. -/
def CFuncIs (p : Program) (f : W64) (pre : State → Prop) (post : State → State → Prop) : Prop :=
  f.toNat < 2 ^ 47 ∧ Summary p f.toNat pre (fun s s' => CReturn s s' ∧ post s s')

/-- The callee's entry state of `CALL r` (length `len`) at `s`. -/
def callState (s : State) (r len : Nat) : State :=
  ({ s with mem := s.mem.writeLE (s.regs 4 - 8).toNat 8 ((s.rip.toNat + len) % 2 ^ 64) }.setReg 4
    (s.regs 4 - 8)).setRip (s.regs r)

@[simp] theorem callState_rip (s : State) (r len : Nat) : (callState s r len).rip = s.regs r := rfl

theorem exec_callInd_reg {s : State} {r len : Nat} (ht : (s.regs r).toNat < 2 ^ 47)
    (hacc : s.mem.accessible (s.regs 4 - 8).toNat 8 true = true) :
    exec (.callInd (.reg r)) len s = .ok (callState s r len) := by
  have hr : s.mem.accessible (s.regs 4 - 8).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_read_of_write _ hacc
  simp only [exec, readLoc, State.getReg, BitVec.setWidth_eq, ht, if_true, push64, store, hr, hacc,
    BitVec.toNat_ofNat, callState, Nat.mod_mod]

/-- An indirect `CALL r` through a function pointer satisfying `CFuncIs`. -/
theorem Reaches.callInd_call {p : Program} {s : State} {Q : Outcome → Prop} {c len r : Nat}
    {bs : List Nat} {pre : State → Prop} {post : State → State → Prop}
    (hpc : s.rip = BitVec.ofNat 64 c) (hok : stepOK p c bs (.callInd (.reg r)) len = true)
    (hf : CFuncIs p (s.regs r) pre post)
    (hacc : s.mem.accessible (s.regs 4 - 8).toNat 8 true = true) (hpre : pre (callState s r len))
    (h : ∀ s', s'.rip = retAddrOf (callState s r len) → CReturn (callState s r len) s' →
      post (callState s r len) s' → Reaches p s' Q) : Reaches p s Q := by
  obtain ⟨hlt, hsum⟩ := hf
  refine Reaches.step hpc hok (exec_callInd_reg hlt hacc) ?_
  exact Reaches.call (entry := (s.regs r).toNat) hsum (by simp) hpre fun s' hr hq => h s' hr hq.1 hq.2

theorem ReachesRet.callInd_call {p : Program} {s : State} {ret : W64} {Q : State → Prop}
    {c len r : Nat} {bs : List Nat} {pre : State → Prop} {post : State → State → Prop}
    (hpc : s.rip = BitVec.ofNat 64 c) (hok : stepOK p c bs (.callInd (.reg r)) len = true)
    (hf : CFuncIs p (s.regs r) pre post)
    (hacc : s.mem.accessible (s.regs 4 - 8).toNat 8 true = true) (hpre : pre (callState s r len))
    (h : ∀ s', s'.rip = retAddrOf (callState s r len) → CReturn (callState s r len) s' →
      post (callState s r len) s' → ReachesRet p ret s' Q) : ReachesRet p ret s Q := by
  obtain ⟨hlt, hsum⟩ := hf
  refine ReachesRet.step hpc hok (exec_callInd_reg hlt hacc) ?_
  exact ReachesRet.call (entry := (s.regs r).toNat) hsum (by simp) hpre fun s' hr hq => h s' hr hq.1 hq.2

/-! ## Callbacks: C calls an exported Go function (amd64; see `Janus.FFI.CgoCallback`)

`crosscall2` (`runtime/cgo/asm_amd64.s`) saves `RBX RBP R12–R15`, stores `fn`, `frame` and
`ctxt` at `[RSP]`, `[RSP+8]`, `[RSP+16]` and calls `runtime.cgocallback` (ABI0), so at the stub
`[RSP]` is the return address and the arguments are at `[RSP+8]`, `[RSP+16]`, `[RSP+24]`. Go's TLS
`g` slot is at `FS + d` with `d` the linker's offset of `runtime.tlsg` (`-8` in a binary whose C
code has no `__thread` variables; in general `TLSImage.x64Addr` of `runtime.tlsg`, which is why
the contract takes the extraction's `TLSImage`). -/

/-- The entry of the Go function behind `//export F` (`_cgoexp_<hash>_F`; see
`Janus.FFI.exportAddr`). -/
def exportAddr (p : Program) (F : String) : Nat :=
  ((p.segments.find? fun sg => "_cgoexp_".toList.isPrefixOf sg.name.toList &&
      sg.name.toList.drop 21 == F.toList).map (·.base)).getD 0

def cbStackScratch : Nat := 16384
/-- The goroutine stack of the examples whose Go side needs little (`Janus.FFI.cbGoStack`). -/
def cbGoStack : Nat := 4096

/-- Go's TLS `g` slot of the thread whose `FS` base is `fs`: `runtime.tlsg` in the executable's
TLS image `t` (`FS − 8` without C `__thread` variables). -/
def tlsGSlot (t : TLSImage) (fs : W64) : Nat := t.x64Addr fs "runtime.tlsg"

/-- The bytes a `cgocallback` from `s` may change besides what the Go code writes: the C stack
below `RSP`, its ABI0 argument slots `[RSP+8, RSP+32)`, and Go's TLS `g` slot. -/
def cbClobber (t : TLSImage) (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - cbStackScratch, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 32),
   (tlsGSlot t s.fsBase, tlsGSlot t s.fsBase + 8)]

def CbKept (t : TLSImage) (s : State) (a n : Nat) (w : Bool) : Prop :=
  s.mem.accessible a n w = true ∧ Outside a n (cbClobber t s)

/-- The readiness of the goroutine stack `k` (`Janus.FFI.CbStack`) at the stub state `s`:
`k.ready [fn, k.size] g RSP (rtView k.rt s.mem)` with `g` the TLS `g` slot that `cgocallback`
reads. -/
def CbReady (k : Janus.FFI.CbStack) (t : TLSImage) (s : State) : Prop :=
  k.ready [s.mem.readLE ((s.regs 4).toNat + 8) 8, k.size] (s.mem.readLE (tlsGSlot t s.fsBase) 8)
    (s.regs 4).toNat (Janus.Contracts.rtView k.rt s.mem)

/-- The Go call state `u` that `cgocallback` makes from the C state `s` with `gs` bytes of
goroutine stack (trusted; see `Janus.FFI.CallbackEntry`): the ABIInternal call `fn(frame)`
(`RIP = [RSP+8]`, `RAX = [RSP+16]`, `[RSP_u] = ret`, `X15 = 0`, `DF` clear); `R14` the
goroutine's `g` (`m.curg`), its struct readable Go memory, the TLS `g` slot holding it; the
goroutine stack (`gs` writable bytes below `RSP`, the return-address slot and the argument's
spill slot) not C memory, its
low end at least `gs` bytes below `RSP` (`g.stackguard0 + gs ≤ RSP + stackGuard`); the C memory
left alone kept; the same thread, `MXCSR` and x87 control word. -/
structure CallbackEntry (t : TLSImage) (p : Program) (gs : Nat) (s u : State) (ret : Nat) : Prop where
  rip : u.rip = BitVec.ofNat 64 (s.mem.readLE ((s.regs 4).toNat + 8) 8)
  arg : u.regs 0 = BitVec.ofNat 64 (s.mem.readLE ((s.regs 4).toNat + 16) 8)
  retSlot : u.mem.readLE (u.regs 4).toNat 8 = ret
  retAddr : RetAddr p ret
  zero : u.xmm xmmZero = 0
  df : u.df = false
  gReg : (u.regs 14).toNat + gStructSize ≤ 2 ^ 48 ∧
    u.mem.accessible (u.regs 14).toNat gStructSize false = true
  gSep : ∀ a n w, s.mem.accessible a n w = true →
    Outside a n [((u.regs 14).toNat, (u.regs 14).toNat + gStructSize)]
  tlsG : u.mem.readLE (tlsGSlot t u.fsBase) 8 = (u.regs 14).toNat
  /-- The goroutine stack: `gs` writable bytes below `RSP`, the return-address slot and the
  spill slot of the frame argument above it (`[RSP+8, RSP+16)`, in `cgocallbackg1`'s frame). -/
  goStack : gs ≤ (u.regs 4).toNat ∧ (u.regs 4).toNat + 16 ≤ 2 ^ 48 ∧
    u.mem.accessible ((u.regs 4).toNat - gs) (gs + 16) true = true
  stackSep : ∀ a n w, s.mem.accessible a n w = true →
    Outside a n [((u.regs 4).toNat - gs, (u.regs 4).toNat + 16)]
  gOff : Outside (u.regs 14).toNat gStructSize [((u.regs 4).toNat - gs, (u.regs 4).toNat + 16)]
  guard : u.mem.readLE ((u.regs 14).toNat + 16) 8 + gs ≤ (u.regs 4).toNat + Janus.FFI.stackGuard
  kept : ∀ a n, CbKept t s a n false → u.mem.readLE a n = s.mem.readLE a n
  keptAcc : ∀ a n w, CbKept t s a n w → u.mem.accessible a n w = true
  fs : u.fsBase = s.fsBase
  mxcsr : u.mxcsr = s.mxcsr
  fpucw : u.fpucw = s.fpucw

/-- The Go code's stack check passes at the entry `u` for an adjustment `adj` when
`adj + stackGuard < gs`. -/
theorem CallbackEntry.guardOK {t : TLSImage} {p : Program} {gs : Nat} {s u : State} {ret : Nat}
    (he : CallbackEntry t p gs s u ret) {adj : Nat} (hadj : adj + Janus.FFI.stackGuard < gs) :
    StackGuardOK u adj := by
  obtain ⟨h1, h2⟩ := he.gReg
  have hg := he.guard
  refine ⟨by simp only [regG, stackguard0Offset]; unfold gStructSize at h1; omega,
    Janus.Arm64.Memory.accessible_sub _ h2 (by simp) (by simp only [regG, stackguard0Offset]; omega)
      (by simp only [regG, stackguard0Offset]; unfold gStructSize; omega), ?_⟩
  simp only [stackguard0, regG, stackguard0Offset, GoABI.regSP, Janus.FFI.stackGuard] at hg hadj ⊢; omega

/-- How the C caller resumes: at `[RSP]` with `RSP + 8`, `DF` clear, the same thread, the
`MXCSR` control bits and x87 control word kept; every other register, the flags and the vector
registers arbitrary (an ABI0 callee); memory `m`. -/
def CbResume (s s' : State) (m : Memory) : Prop :=
  ∃ regs flags xmm ymmHi mx zh kr,
    s' = { s with regs := regs, rip := retAddrOf s, flags := flags, xmm := xmm, ymmHi := ymmHi,
                  zmmHi := zh, kreg := kr,
                  mem := m, df := false, mxcsr := mx } ∧
    regs 4 = s.regs 4 + 8 ∧ mx.toNat / 64 = s.mxcsr.toNat / 64

def CbResumed (t : TLSImage) (s u' s' : State) : Prop :=
  ∃ m, CbResume s s' m ∧ m.regions = s.mem.regions ∧
    ∀ a, Outside a 1 (cbClobber t s) →
      m.bytes a = if s.mem.accessible a 1 false then u'.mem.bytes a else s.mem.bytes a

/-- The stack `cgocallback` may use below `RSP` and its argument slots above (no alignment:
at the stub `RSP ≡ 0 mod 16`, `crosscall2` being Go assembly that keeps the ABI0 frame layout,
not the System V alignment). -/
def CbStack (s : State) : Prop :=
  cbStackScratch ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 32 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - cbStackScratch) (cbStackScratch + 32) true = true

/-- The **trusted** contract of `runtime.cgocallback` (amd64; see `Janus.FFI.CgoCallback`): the
stub's stack window, the runtime's readiness for the goroutine stack `k` (`CbReady`), and for
every Go call state with `k.size` bytes of goroutine stack in which `R` holds, the Go function
returns. -/
def CgoCallback (t : TLSImage) (p : Program) (Cin : Contract) (R : State → Prop)
    (k : Janus.FFI.CbStack) : Contract where
  safe f s := f = "runtime.cgocallback.abi0" ∧ CbStack s ∧ CbReady k t s ∧
    ∀ u ret, CallbackEntry t p k.size s u ret → R u → ReturnsC (p.withExit ret) Cin (ABIReturn u) u
  next f s s' := f = "runtime.cgocallback.abi0" ∧ ∃ u ret u', CallbackEntry t p k.size s u ret ∧ R u ∧
    RunsTo (p.withExit ret) Cin u u' ∧ ABIReturn u u' ∧ CbResumed t s u' s'

/-- The C-side assumption (amd64). -/
def CallbackSpec (t : TLSImage) (fn : Nat) (G : State → Prop) (E : State → Memory) : Contract where
  safe f s := f = "runtime.cgocallback.abi0" ∧ s.mem.readLE ((s.regs 4).toNat + 8) 8 = fn ∧ G s
  next f s s' := f = "runtime.cgocallback.abi0" ∧ ∃ m, CbResume s s' m ∧ MemFrame (E s) m (cbClobber t s)

theorem CbResumed.memFrame {t : TLSImage} {s u' s' : State} {E : Memory} (h : CbResumed t s u' s')
    (hE : E.regions = s.mem.regions)
    (hacc : ∀ a, Outside a 1 (cbClobber t s) → s.mem.accessible a 1 false = true →
      u'.mem.bytes a = E.bytes a)
    (hna : ∀ a, Outside a 1 (cbClobber t s) → s.mem.accessible a 1 false = false →
      s.mem.bytes a = E.bytes a) :
    ∃ m, CbResume s s' m ∧ MemFrame E m (cbClobber t s) := by
  obtain ⟨m, hres, hreg, hb⟩ := h
  refine ⟨m, hres, ⟨fun a n ho => Janus.FFI.readLE_congr fun i hi => ?_, fun a n w => ?_⟩⟩
  · have ho1 := Janus.FFI.outside_one ho hi
    rw [hb _ ho1]
    cases hc : s.mem.accessible (a + i) 1 false
    · simp only [Bool.false_eq_true, ite_false]; exact hna _ ho1 hc
    · simp only [ite_true]; exact hacc _ ho1 hc
  · simp only [Janus.Arm64.Memory.accessible, hreg, hE]

/-- **Reverse composition** (amd64). -/
theorem CgoCallback.refines {t : TLSImage} {p : Program} {Cin : Contract} {R : State → Prop}
    {k : Janus.FFI.CbStack} {fn : Nat}
    {G : State → Prop} {E : State → Memory}
    {pre : W64 → State → Prop} {post : W64 → State → State → Prop}
    (hGo : ∀ a, EnsuresC p Cin fn [a] (pre a) (post a))
    (hstack : ∀ s, G s → CbStack s)
    (hready : ∀ s, G s → CbReady k t s)
    (hpre : ∀ s u ret, G s → CallbackEntry t p k.size s u ret → R u →
      pre (BitVec.ofNat 64 (s.mem.readLE ((s.regs 4).toNat + 16) 8)) u)
    (hE : ∀ s, G s → (E s).regions = s.mem.regions)
    (hacc : ∀ s u ret u', G s → CallbackEntry t p k.size s u ret → R u → ABIReturn u u' →
      post (BitVec.ofNat 64 (s.mem.readLE ((s.regs 4).toNat + 16) 8)) u u' →
      ∀ a, Outside a 1 (cbClobber t s) → s.mem.accessible a 1 false = true →
        u'.mem.bytes a = (E s).bytes a)
    (hna : ∀ s, G s → ∀ a, Outside a 1 (cbClobber t s) → s.mem.accessible a 1 false = false →
      s.mem.bytes a = (E s).bytes a) :
    (CgoCallback t p Cin R k).Refines (CallbackSpec t fn G E) := by
  intro f s ⟨hf, hfn, hG⟩
  have hfnv : BitVec.ofNat 64 (s.mem.readLE ((s.regs 4).toNat + 8) 8) = BitVec.ofNat 64 fn := by rw [hfn]
  have hcall : ∀ u ret, CallbackEntry t p k.size s u ret →
      CallSetup (p.withExit ret) fn [BitVec.ofNat 64 (s.mem.readLE ((s.regs 4).toNat + 16) 8)] u :=
    fun u ret he => {
      rip := by rw [he.rip, hfnv]
      ret := by rw [he.retSlot]; rfl
      zero := he.zero
      len := by simp [numIntRegs]
      args := fun i hi => by
        have : i = 0 := by simp at hi; omega
        subst this; simpa [GoABI.argReg, GoABI.intArgRegs] using he.arg
      df := he.df }
  refine ⟨⟨hf, hstack s hG, hready s hG, fun u ret he hR => ?_⟩, ?_⟩
  · exact (hGo _ ret he.retAddr u (hcall u ret he) (hpre s u ret hG he hR)).mono fun _ h => h.1
  · rintro s' ⟨hf', u, ret, u', he, hR, hrun, hab, hres⟩
    refine ⟨hf', ?_⟩
    have hq := (hGo _ ret he.retAddr u (hcall u ret he) (hpre s u ret hG he hR)).runsTo hrun
    exact hres.memFrame (hE s hG) (hacc s u ret u' hG he hR hab hq.2) (hna s hG)

/-! ## Stack windows -/

theorem CStack.frame {s t : State} {below above n : Nat} {rs : List (Nat × Nat)}
    (h : CStack s below above) (hn : n ≤ below) (h16 : n % 16 = 0)
    (hsp : (t.regs 4).toNat = (s.regs 4).toNat - n) (hf : MemFrame s.mem t.mem rs) :
    CStack t (below - n) (n + above) := by
  unfold CStack at *
  try simp only [CABI.regSP] at *
  obtain ⟨ha, hb, hc, hd⟩ := h
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hsp, hf.accessible, show (s.regs 4).toNat - n - (below - n) = (s.regs 4).toNat - below by omega,
    show below - n + (n + above) = below + above by omega]
  exact hd

theorem CStack.mono {s : State} {below above below' above' : Nat} (h : CStack s below above)
    (h1 : below' ≤ below) (h2 : above' ≤ above) : CStack s below' above' := by
  unfold CStack at *
  obtain ⟨ha, hb, hc, hd⟩ := h
  exact ⟨ha, by omega, by omega, Janus.Arm64.Memory.accessible_mono _ hd (by omega) (by omega)⟩

/-- `obtain_cret64 h`: the equations of `h : CReturn s s'` (amd64) as hypotheses. -/
macro "obtain_cret64 " h:term : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := $h)

end Janus.Amd64.FFI
