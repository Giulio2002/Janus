import Janus.Tactic
import Janus.CABI

/-!
# FFI: contracts for external functions, and the cgo boundary (arm64)

Go calls C only through `runtime.cgocall(fn, arg)`: the cgo-generated Go function
`_Cfunc_f` stores its arguments in an argument frame on the goroutine stack and calls
`runtime.cgocall(_cgo_<hash>_Cfunc_f, &frame)`; `cgocall` enters a system call
(`entersyscall`), switches to the system stack (`asmcgocall`, the `g0` stack), calls the C
wrapper `_cgo_<hash>_Cfunc_f(&frame)` there with the C calling convention, switches back and
leaves the system call (`exitsyscall`, which may reschedule the goroutine). The C wrapper unpacks
the frame, calls the C function `f`, and stores its result in the frame.

The C code (the wrapper and `f`) is machine code in the same binary: Janus extracts it and runs
it in the same model (`janus extract` follows the cgo function-pointer variable from the Go side
to the wrapper, and direct calls from there). What is **not** extracted is `runtime.cgocall`
itself: the scheduler and the stack switch. The extractor makes it an `external` stub
(`StubKind.external`), and this module gives such stubs a meaning through an explicit
**contract** (`Contract`): `ReturnsC p C post s` is "every run from `s` returns satisfying
`post`, where reaching an external stub `f` is allowed when `C.safe f` holds there, and then
continues from every state `C.next f` allows".

Two cgo contracts are defined here:

* `CgoSpec fn G E` — the **assumption** a Go-side theorem states: "`cgocall` with `X0 = fn`
  (the C wrapper) in a state satisfying `G` returns to the caller with the Go state restored
  (`GoResume`: `SP`, `g`, `FP` and the return address; every other register arbitrary) and
  memory `E s` outside the bytes the runtime may use (`cgoClobber`)". It appears literally in the
  theorem statement (`EnsuresC p (CgoSpec …) …`), so the printed statement shows it.
* `CgoCall p` — the **trusted** description of what `cgocall` does on hardware: it runs the C
  function at `fn` *in the model*, from a C call state (`CgoEntry`: AAPCS64 call of `fn` with
  `X0 = arg` on a system stack that is not Go memory), and when the C code returns (with its
  callee-saved registers restored) it resumes the Go caller with the C code's memory writes
  (`CgoResumed`). Only the stack switch, the scheduler and `_cgo_topofstack` (`TopOfStack`) are
  taken on trust; every C instruction is executed by the model.

`CgoCall.refines` is the composition theorem: a proved `CEnsuresC` for the C wrapper turns a
Go-side theorem under `CgoSpec` into one under `CgoCall p` alone (`EnsuresC.refine`). See
`docs/FFI.md` and the "FFI" section of `docs/RUNTIME-CONTRACTS.md` for exactly what is trusted.

**Why not a `Summary` hypothesis.** A `Summary p cgocall pre post` is a statement about running
the *extracted* program from `cgocall`'s entry, where there is no code: it is false (or only true
vacuously), so a theorem assuming it would prove anything. A contract is instead a separate
semantics for the stub, and the only way to discharge one is a refinement proof.
-/

namespace Janus.FFI

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.CABI

/-! ## Contracts -/

/-- A contract for the external stubs of a program, by stub name. -/
structure Contract where
  /-- `safe f s`: calling the external function `f` in state `s` (at its entry, with the
  return address in `X30`) is allowed and returns to the caller. -/
  safe : String → State → Prop
  /-- `next f s s'`: `s'` is a possible state after the call has returned. -/
  next : String → State → State → Prop

/-- No external function may be called. `ReturnsC p Contract.none` is `Returns`. -/
def Contract.none : Contract := ⟨fun _ _ => False, fun _ _ _ => False⟩

/-- `C₁` refines `C₂`: wherever `C₂` allows a call, so does `C₁`, and every result of `C₁` is
one `C₂` allows. A theorem proved under `C₂` holds under `C₁` (`ReturnsC.refine`). -/
def Contract.Refines (C₁ C₂ : Contract) : Prop :=
  ∀ f s, C₂.safe f s → C₁.safe f s ∧ ∀ s', C₁.next f s s' → C₂.next f s s'

theorem Contract.Refines.refl (C : Contract) : C.Refines C := fun _ _ h => ⟨h, fun _ h => h⟩

theorem Contract.Refines.trans {C₁ C₂ C₃ : Contract} (h₁ : C₁.Refines C₂) (h₂ : C₂.Refines C₃) :
    C₁.Refines C₃ := fun f s h =>
  let ⟨a, b⟩ := h₂ f s h
  let ⟨c, d⟩ := h₁ f s a
  ⟨c, fun s' h' => b s' (d s' h')⟩

/-- Every run from `s` returns (reaches `p.exitAddr`) in a state satisfying `post`, after
finitely many steps, where an ordinary instruction is executed by the model and an external
stub `f` must be `C.safe f` and continues from **every** state `C.next f` allows. Faults,
panic and `morestack` stubs are excluded, as for `Returns`. -/
inductive ReturnsC (p : Program) (C : Contract) (post : State → Prop) : State → Prop where
  | exit {s : State} (hx : s.pc.toNat = p.exitAddr) (hp : post s) : ReturnsC p C post s
  | step {s s' : State} {w : Nat} (hx : s.pc.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.pc.toNat = none) (hf : p.fetch s.pc.toNat = some w)
      (hst : Arm64.step w s = .ok s') (h : ReturnsC p C post s') : ReturnsC p C post s
  | ext {s : State} {st : Stub} (hx : s.pc.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.pc.toNat = some st) (hk : st.kind = .external)
      (hsafe : C.safe st.name s) (h : ∀ s', C.next st.name s s' → ReturnsC p C post s') :
      ReturnsC p C post s

/-- `s'` is a final state (at `p.exitAddr`) of some run from `s` under the contract `C`. -/
inductive RunsTo (p : Program) (C : Contract) : State → State → Prop where
  | exit {s : State} (hx : s.pc.toNat = p.exitAddr) : RunsTo p C s s
  | step {s s₁ s' : State} {w : Nat} (hx : s.pc.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.pc.toNat = none) (hf : p.fetch s.pc.toNat = some w)
      (hst : Arm64.step w s = .ok s₁) (h : RunsTo p C s₁ s') : RunsTo p C s s'
  | ext {s s₁ s' : State} {st : Stub} (hx : s.pc.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.pc.toNat = some st) (hk : st.kind = .external)
      (hn : C.next st.name s s₁) (h : RunsTo p C s₁ s') : RunsTo p C s s'

namespace ReturnsC

variable {p : Program} {C : Contract} {P Q : State → Prop} {s : State}

theorem mono (h : ReturnsC p C P s) (hPQ : ∀ s, P s → Q s) : ReturnsC p C Q s := by
  induction h with
  | exit hx hp => exact .exit hx (hPQ _ hp)
  | step hx hs hf hst _ ih => exact .step hx hs hf hst ih
  | ext hx hs hk hsafe _ ih => exact .ext hx hs hk hsafe ih

/-- A theorem under a contract holds under every refinement of it. -/
theorem refine {C₁ : Contract} (hR : C₁.Refines C) (h : ReturnsC p C P s) : ReturnsC p C₁ P s := by
  induction h with
  | exit hx hp => exact .exit hx hp
  | step hx hs hf hst _ ih => exact .step hx hs hf hst ih
  | @ext s st hx hs hk hsafe _ ih =>
    obtain ⟨hs₁, hn⟩ := hR st.name s hsafe
    exact .ext hx hs hk hs₁ fun s' h' => ih s' (hn s' h')

/-- Every final state of a run satisfies `post`. -/
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

/-- A final state of a run is at the exit address. -/
theorem _root_.Janus.FFI.RunsTo.pc_exit {s s' : State} (h : RunsTo p C s s') :
    s'.pc.toNat = p.exitAddr := by
  induction h with
  | exit hx => exact hx
  | step _ _ _ _ _ ih => exact ih
  | ext _ _ _ _ _ ih => exact ih

/-- Ordinary steps first. -/
theorem of_steps {k : Nat} {s' : State} (hs : Program.Steps p s k s') (h : ReturnsC p C P s') :
    ReturnsC p C P s := by
  induction hs with
  | refl => exact h
  | step hx hst hf he _ ih => exact .step hx hst hf he (ih h)

/-- A run that returns without reaching an external stub. -/
theorem of_run {n : Nat} {s' : State} (hr : p.run n s = .ok (.returned s')) (hp : P s') :
    ReturnsC p C P s := by
  induction n generalizing s with
  | zero => simp at hr
  | succ n ih =>
    rw [Program.run_succ] at hr
    by_cases hx : s.pc.toNat = p.exitAddr
    · rw [ite_eq_left hx] at hr; cases hr; exact .exit hx hp
    · rw [ite_eq_right hx] at hr
      cases hst : p.stubAt s.pc.toNat with
      | some st => simp only [hst] at hr; cases hr
      | none =>
        cases hf : p.fetch s.pc.toNat with
        | none => simp only [hst, hf] at hr; cases hr
        | some w =>
          cases he : Arm64.step w s with
          | error e => simp only [hst, hf, he] at hr; cases hr
          | ok s₁ => simp only [hst, hf, he] at hr; exact .step hx hst hf he (ih hr)

/-- `Returns` (no external stub on the way) implies `ReturnsC` under any contract. -/
theorem of_returns (h : Returns p s P) : ReturnsC p C P s := by
  obtain ⟨n, s', hr, hp⟩ := h
  exact of_run hr hp

end ReturnsC

/-! ### Running under a contract with `janus_run`

`janus_run` works on `Reaches p s Q`. `ReturnsC.of_reaches` turns a `ReturnsC` goal into one with
`Q = IsReturnC p C post`: the run stops at the exit address (goal: `post`) or at an external stub
(goal: `C.safe f S ∧ ∀ s', C.next f S s' → ReturnsC p C post s'`, after `janus_post`); prove
`safe`, introduce `s'` and its `next` facts, and continue with `apply ReturnsC.of_reaches` and
`janus_run` again. -/

/-- The outcome predicate of `ReturnsC`. -/
def IsReturnC (p : Program) (C : Contract) (post : State → Prop) : Outcome → Prop
  | .returned s => post s
  | .stub f .external s => C.safe f s ∧ ∀ s', C.next f s s' → ReturnsC p C post s'
  | .stub _ _ _ => False

@[simp, janus_post] theorem isReturnC_returned (p : Program) (C : Contract) (post : State → Prop)
    (s : State) : IsReturnC p C post (.returned s) = post s := rfl
@[simp, janus_post] theorem isReturnC_external (p : Program) (C : Contract) (post : State → Prop)
    (f : String) (s : State) : IsReturnC p C post (.stub f .external s) =
      (C.safe f s ∧ ∀ s', C.next f s s' → ReturnsC p C post s') := rfl
@[simp, janus_post] theorem isReturnC_panic (p : Program) (C : Contract) (post : State → Prop)
    (f : String) (s : State) : IsReturnC p C post (.stub f .panic s) = False := rfl
@[simp, janus_post] theorem isReturnC_morestack (p : Program) (C : Contract)
    (post : State → Prop) (f : String) (s : State) :
    IsReturnC p C post (.stub f .morestack s) = False := rfl

theorem ReturnsC.of_reaches {p : Program} {C : Contract} {post : State → Prop} {s : State}
    (h : Reaches p s (IsReturnC p C post)) : ReturnsC p C post s := by
  obtain ⟨n, o, hr, hq⟩ := h
  induction n generalizing s with
  | zero => simp at hr
  | succ n ih =>
    rw [Program.run_succ] at hr
    by_cases hx : s.pc.toNat = p.exitAddr
    · rw [ite_eq_left hx] at hr; cases hr; exact .exit hx hq
    · rw [ite_eq_right hx] at hr
      cases hst : p.stubAt s.pc.toNat with
      | some st =>
        simp only [hst] at hr; cases hr
        cases hk : st.kind with
        | external => rw [hk] at hq; exact .ext hx hst hk hq.1 hq.2
        | panic => rw [hk] at hq; exact hq.elim
        | morestack => rw [hk] at hq; exact hq.elim
      | none =>
        cases hf : p.fetch s.pc.toNat with
        | none => simp only [hst, hf] at hr; cases hr
        | some w =>
          cases he : Arm64.step w s with
          | error e => simp only [hst, hf, he] at hr; cases hr
          | ok s₁ => simp only [hst, hf, he] at hr; exact .step hx hst hf he (ih hr)

/-! ## Specifications under a contract -/

/-- What a Go function that calls C restores on return: `SP`, `g` (`X28`) and the frame
pointer. Unlike `GoABI.ABIReturn` not `X18`: C code may use it (on Linux it is an ordinary
temporary in AAPCS64), and `cgocall` does not restore it (Go never uses it). -/
structure ABIReturnC (s₀ s₁ : State) : Prop where
  sp : s₁.sp = s₀.sp
  g : s₁.regs regG = s₀.regs regG
  fp : s₁.regs GoABI.regFP = s₀.regs GoABI.regFP

theorem abiReturnC_iff (s₀ s₁ : State) :
    ABIReturnC s₀ s₁ ↔ s₁.sp = s₀.sp ∧ s₁.regs 28 = s₀.regs 28 ∧ s₁.regs 29 = s₀.regs 29 :=
  ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

attribute [janus_post] abiReturnC_iff CABI.cReturn_iff

theorem ABIReturnC.of_abiReturn {s₀ s₁ : State} (h : ABIReturn s₀ s₁) : ABIReturnC s₀ s₁ :=
  ⟨h.sp, h.g, h.fp⟩

/-- The Go function contract under a contract `C` for its external calls: for **every**
admissible return address and **every** Go call state with these arguments satisfying `pre`,
every run returns to `ret` (`ReturnsC`), restores `SP`, `g` and `FP` (`ABIReturnC`) and
satisfies `post s₀ s₁`. -/
def EnsuresC (p : Program) (C : Contract) (entry : Nat) (args : List W64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ ret, RetAddr p ret → ∀ s, CallSetup (p.withExit ret) entry args s → pre s →
    ReturnsC (p.withExit ret) C (fun s' => ABIReturnC s s' ∧ post s s') s

/-- The C function contract under a contract `C` for its external calls (`CABI.CEnsures` with
`ReturnsC` in place of `Returns`). -/
def CEnsuresC (p : Program) (C : Contract) (entry : Nat) (args : List W64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ ret, RetAddr p ret → ∀ s, CCall (p.withExit ret) entry args s → pre s →
    ReturnsC (p.withExit ret) C (fun s' => CReturn s s' ∧ post s s') s

/-- A Go theorem under a contract holds under every refinement of the contract. -/
theorem EnsuresC.refine {p : Program} {C₁ C₂ : Contract} {entry : Nat} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (hR : C₁.Refines C₂)
    (h : EnsuresC p C₂ entry args pre post) : EnsuresC p C₁ entry args pre post :=
  fun ret hret s hs hp => (h ret hret s hs hp).refine hR

theorem CEnsuresC.refine {p : Program} {C₁ C₂ : Contract} {entry : Nat} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (hR : C₁.Refines C₂)
    (h : CEnsuresC p C₂ entry args pre post) : CEnsuresC p C₁ entry args pre post :=
  fun ret hret s hs hp => (h ret hret s hs hp).refine hR

/-- A Go `Ensures` theorem holds under any contract. -/
theorem EnsuresC.of_ensures {p : Program} {C : Contract} {entry : Nat} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (h : Ensures p entry args pre post) :
    EnsuresC p C entry args pre post :=
  fun ret hret s hs hp => .of_returns ((h ret hret s hs hp).mono fun _ ⟨ha, hq⟩ =>
    ⟨ABIReturnC.of_abiReturn ha, hq⟩)

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
  have hpc : s.pc = BitVec.ofNat 64 entry := hs.call.pc
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hpc (hpre ret s hret hs hp)
  have hst' := hst.withExit hret.fetch_none
  refine returns_of_steps hst' ?_ (hpost s s' hp hq)
  rw [hr, hs.call.lr]
  simp only [Program.withExit, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hret.lt64

/-! ## The cgo boundary -/

/-- Bytes of the goroutine stack below `SP` that `cgocall` and the nosplit functions it calls
(`entersyscall`, `exitsyscall`, ...) may write. The linker bounds every chain of nosplit frames
by `abi.StackNosplitBase` = 800 bytes (non-race builds); 1024 leaves a margin. -/
def cgoStackScratch : Nat := 1024

/-- `unsafe.Sizeof(runtime.g{})` in Go 1.26.0 (from the DWARF of the example binaries). -/
def gStructSize : Nat := 456

/-- Offset of the `g` slot in the thread's TLS block on linux/arm64 (`runtime.tls_g`, set by
the linker: `load_g` computes `TPIDR_EL0 + 16`). -/
def tlsGOffset : Nat := 16

/-- Bytes free on the system stack below `SP` for the C code (`CStack t cgoCStack 0`). The
system stack is the thread's own (8 MiB by default for threads created through cgo); the model
only needs it to hold the frames of the C function. -/
def cgoCStack : Nat := 4096

/-- The byte ranges a `cgocall` from state `s` may change besides what the C code writes: the
goroutine stack below `SP` (`cgocall`'s and the runtime's frames), the spill slots of
`cgocall`'s two register arguments above `SP` (`[SP+8, SP+24)`, `0(SP)` is the caller's saved
link register and is untouched), the `g` struct (`entersyscall`/`exitsyscall` update its status,
`stackguard0`, `syscallsp`, ...), and the `g` slot of the thread's TLS (`asmcgocall` points it
at `g0` during the call). -/
def cgoClobber (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - cgoStackScratch, s.sp.toNat), (s.sp.toNat + 8, s.sp.toNat + 24),
   ((s.regs regG).toNat, (s.regs regG).toNat + gStructSize),
   (s.tpidr.toNat + tlsGOffset, s.tpidr.toNat + tlsGOffset + 8)]

/-- How the Go caller resumes after `cgocall` returns: at the return address `X30`, with `SP`,
`g` (`X28`) and `FP` (`X29`) restored, the same `DCZID_EL0`, and memory `m` (every other
register, the flags, the SIMD&FP registers and `TPIDR_EL0` arbitrary: `cgocall` is an ordinary
Go call, and the goroutine may resume on another thread). `FPCR` is preserved (the C code
restores it, `CReturn.fpcr`); `FPSR` is arbitrary: its cumulative exception flags are sticky
and C floating point may set them. -/
def GoResume (s s' : State) (m : Memory) : Prop :=
  ∃ regs flags vregs tpidr fpsr,
    s' = { s with regs := regs, pc := s.regs GoABI.regLR, flags := flags, mem := m,
                  vregs := vregs, tpidr := tpidr, fpsr := fpsr } ∧
    regs regG = s.regs regG ∧ regs GoABI.regFP = s.regs GoABI.regFP

/-- The cgo contract a Go-side theorem assumes: `runtime.cgocall` called with `X0 = fn` in a
state satisfying `G` returns (`GoResume`) with memory that agrees with `E s` everywhere outside
`cgoClobber s` (and has the same regions). Nothing else may be called. -/
def CgoSpec (fn : Nat) (G : State → Prop) (E : State → Memory) : Contract where
  safe f s := f = "runtime.cgocall" ∧ s.regs 0 = BitVec.ofNat 64 fn ∧ G s
  next f s s' := f = "runtime.cgocall" ∧ ∃ m, GoResume s s' m ∧ MemFrame (E s) m (cgoClobber s)

/-- The trusted contract of `_cgo_topofstack` (`runtime/asm_arm64.s`) during one cgo call: it
returns `T`, the top of the calling goroutine's stack (`g0.m.curg.stack.hi`, the same on every
call while no callback into Go moves the goroutine stack), in `X0`; returns to `X30`; restores
every other register (it saves and reloads the `X27`/`X28` that `load_g` clobbers) and `SP`;
and writes only the 56 bytes below `SP` (its 48-byte frame, `STR X30, [SP, #-48]!`, and the
frame-pointer slot below it, `STUR X29, [SP, #-8]`), which must be writable. -/
def TopOfStack (T : W64) : Contract where
  safe f s := f = "_cgo_topofstack" ∧ CStack s 56 0
  next f s s' := f = "_cgo_topofstack" ∧ ∃ flags m,
    s' = { s with regs := setReg s.regs 0 T, pc := s.regs GoABI.regLR, flags := flags, mem := m } ∧
    MemFrame s.mem m [(s.sp.toNat - 56, s.sp.toNat)]

/-- Ranges `[a, a+n)` that are memory of the Go state `s` the runtime leaves alone: accessible
in `s` and outside `cgoClobber s`. -/
def GoKept (s : State) (a n : Nat) (w : Bool) : Prop :=
  s.mem.accessible a n w = true ∧ Outside a n (cgoClobber s)

/-- The C call state `t` that `asmcgocall` makes for `cgocall(fn = X0, arg = X1)` from the Go
state `s`, returning to `ret` (inside `asmcgocall`: outside the extracted code). Trusted
description (see `docs/RUNTIME-CONTRACTS.md`, "FFI"):

* the AAPCS64 call: `pc = fn`, `X0 = arg`, `X30 = ret`;
* the system stack: `SP` 16-byte aligned with `cgoCStack` bytes writable below it, and none of
  them memory of `s` (`stackSep`: the `g0` stack is not Go memory);
* the Go memory: every range the runtime leaves alone (`GoKept`) holds the same bytes and is
  accessible in the same way (`kept`, `keptAcc`);
* the same thread (`TPIDR_EL0`) and `DCZID_EL0`. Every other register, the flags and the
  SIMD&FP registers are arbitrary. -/
structure CgoEntry (p : Program) (s t : State) (ret : Nat) : Prop where
  pc : t.pc = s.regs 0
  arg : t.regs 0 = s.regs 1
  lr : t.regs GoABI.regLR = BitVec.ofNat 64 ret
  retAddr : RetAddr p ret
  stack : CStack t cgoCStack 0
  stackSep : ∀ a n w, s.mem.accessible a n w = true →
    Outside a n [(t.sp.toNat - cgoCStack, t.sp.toNat)]
  kept : ∀ a n, GoKept s a n false → t.mem.readLE a n = s.mem.readLE a n
  keptAcc : ∀ a n w, GoKept s a n w → t.mem.accessible a n w = true
  tpidr : t.tpidr = s.tpidr
  dczid : t.dczid = s.dczid

/-- The byte at `a` is memory of `s` that the runtime leaves alone (decidable form). -/
def keptByte (s : State) (a : Nat) : Bool :=
  s.mem.accessible a 1 false && (cgoClobber s).all fun r => a + 1 ≤ r.1 || r.2 ≤ a

/-- The Go caller resumes from the C state `t'` the C code returned in: `GoResume` with a
memory whose regions are those of `s`, whose bytes outside `cgoClobber s` are the C code's
result on Go memory (`t'`) and the old bytes elsewhere (unobservable: not accessible), and
whose clobbered bytes are arbitrary. -/
def CgoResumed (s t' s' : State) : Prop :=
  ∃ m, GoResume s s' m ∧ m.regions = s.mem.regions ∧
    ∀ a, Outside a 1 (cgoClobber s) →
      m.bytes a = if s.mem.accessible a 1 false then t'.mem.bytes a else s.mem.bytes a

/-- The **trusted** contract of `runtime.cgocall`: for every C call state `asmcgocall` may
make (`CgoEntry`, every return address, every value `T` of `_cgo_topofstack`), the C code at
`fn` returns, under `TopOfStack T`, with the AAPCS64 callee-saved registers restored (which
`asmcgocall` relies on); and the possible results are the Go states resumed from the final C
states of those runs (`CgoResumed`). The C code is run by the model on the extracted program
`p`. -/
def CgoCall (p : Program) : Contract where
  safe f s := f = "runtime.cgocall" ∧ ∀ t ret T, CgoEntry p s t ret →
    ReturnsC (p.withExit ret) (TopOfStack T) (CReturn t) t
  next f s s' := f = "runtime.cgocall" ∧ ∃ t ret T t', CgoEntry p s t ret ∧
    RunsTo (p.withExit ret) (TopOfStack T) t t' ∧ CReturn t t' ∧ CgoResumed s t' s'

/-! ### Composition -/

theorem readLE_congr {m m' : Memory} {a n : Nat} (h : ∀ i, i < n → m'.bytes (a + i) = m.bytes (a + i)) :
    m'.readLE a n = m.readLE a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [Memory.readLE]
    rw [show m'.bytes a = m.bytes a by simpa using h 0 (by omega),
      ih (a := a + 1) fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1 i] using h (i + 1) (by omega)]

theorem bytes_eq_readLE (m : Memory) (a : Nat) : m.bytes a = BitVec.ofNat 8 (m.readLE a 1) := by
  simp only [Memory.readLE, Nat.mul_zero, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem outside_one {a n i : Nat} {rs : List (Nat × Nat)} (h : Outside a n rs) (hi : i < n) :
    Outside (a + i) 1 rs := by
  induction rs with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨lo, hi'⟩ := r
    simp only [outside_cons] at h ⊢
    exact ⟨by omega, ih h.2⟩

/-- The same store on both sides keeps a frame. -/
theorem _root_.Janus.MemFrame.writeLE_both {m m' : Memory} {rs : List (Nat × Nat)}
    (h : MemFrame m m' rs) (a k v : Nat) :
    MemFrame (m.writeLE a k v) (m'.writeLE a k v) rs := by
  refine ⟨fun b n hb => readLE_congr fun i hi => ?_, fun b n w => ?_⟩
  · rw [Memory.bytes_writeLE, Memory.bytes_writeLE]
    split
    · rfl
    · have h1 := h.readLE (b + i) 1 (outside_one hb hi)
      simp only [Memory.readLE_one] at h1
      exact BitVec.eq_of_toNat_eq h1
  · rw [Memory.accessible_writeLE, Memory.accessible_writeLE]; exact h.accessible b n w

/-- The memory of a resumed state is a frame of `E` when the C code's result agrees with `E`
on Go memory and `E` agrees with `s` on the bytes that are not accessible. -/
theorem CgoResumed.memFrame {s t' s' : State} {E : Memory} (h : CgoResumed s t' s')
    (hE : E.regions = s.mem.regions)
    (hacc : ∀ a, Outside a 1 (cgoClobber s) → s.mem.accessible a 1 false = true →
      t'.mem.bytes a = E.bytes a)
    (hna : ∀ a, Outside a 1 (cgoClobber s) → s.mem.accessible a 1 false = false →
      s.mem.bytes a = E.bytes a) :
    ∃ m, GoResume s s' m ∧ MemFrame E m (cgoClobber s) := by
  obtain ⟨m, hres, hreg, hb⟩ := h
  refine ⟨m, hres, ⟨fun a n ho => readLE_congr fun i hi => ?_, fun a n w => ?_⟩⟩
  · have ho1 := outside_one ho hi
    rw [hb _ ho1]
    cases hc : s.mem.accessible (a + i) 1 false
    · simp only [Bool.false_eq_true, ite_false]; exact hna _ ho1 hc
    · simp only [ite_true]; exact hacc _ ho1 hc
  · simp only [Memory.accessible, hreg, hE]

/-- **Composition.** If the C wrapper at `fn` satisfies `CEnsuresC` under `TopOfStack T` for
every `T` and argument `a`, with a precondition that follows from `G` and the trusted entry
facts, and a postcondition from which the Go memory `E s` follows, then the trusted contract
`CgoCall p` refines the Go-side assumption `CgoSpec fn G E`. -/
theorem CgoCall.refines {p : Program} {fn : Nat} {G : State → Prop} {E : State → Memory}
    {pre : W64 → State → Prop} {post : W64 → State → State → Prop}
    (hC : ∀ T a, CEnsuresC p (TopOfStack T) fn [a] (pre a) (post a))
    (hpre : ∀ s t ret, G s → CgoEntry p s t ret → pre (s.regs 1) t)
    (hE : ∀ s, G s → (E s).regions = s.mem.regions)
    (hacc : ∀ s t ret t', G s → CgoEntry p s t ret → CReturn t t' → post (s.regs 1) t t' →
      ∀ a, Outside a 1 (cgoClobber s) → s.mem.accessible a 1 false = true →
        t'.mem.bytes a = (E s).bytes a)
    (hna : ∀ s, G s → ∀ a, Outside a 1 (cgoClobber s) → s.mem.accessible a 1 false = false →
      s.mem.bytes a = (E s).bytes a) :
    (CgoCall p).Refines (CgoSpec fn G E) := by
  intro f s ⟨hf, hx0, hG⟩
  have hcall : ∀ t ret, CgoEntry p s t ret → CCall (p.withExit ret) fn [s.regs 1] t :=
    fun t ret he => {
      call := {
        pc := by rw [he.pc, hx0]
        lr := by rw [he.lr]; rfl
        args := fun i hi => by
          have : i = 0 := by simp at hi; omega
          subst this; simpa using he.arg }
      nargs := by simp [numArgRegs]
      spAligned := he.stack.1 }
  refine ⟨⟨hf, fun t ret T he => ?_⟩, ?_⟩
  · exact (hC T (s.regs 1) ret he.retAddr t (hcall t ret he) (hpre s t ret hG he)).mono
      fun _ h => h.1
  · rintro s' ⟨hf', t, ret, T, t', he, hrun, hcr, hres⟩
    refine ⟨hf', ?_⟩
    have hq := (hC T (s.regs 1) ret he.retAddr t (hcall t ret he) (hpre s t ret hG he)).runsTo hrun
    exact hres.memFrame (hE s hG) (hacc s t ret t' hG he hcr hq.2) (hna s hG)

end Janus.FFI
