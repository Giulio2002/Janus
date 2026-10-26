import Janus.Tactic
import Janus.CABI
import Janus.Contracts.Alloc

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

namespace Janus

/-! ## The C environment of an extraction (both ISAs)

`janus extract` renders two more definitions for C code (docs/FFI.md, section 2): `Extracted.cdata`,
the writable C data objects (`.data`/`.bss`) the extracted C functions reference, directly or
through a statically resolved GOT slot, and `Extracted.tls`, the executable's TLS segment, when an
extracted function reads the thread pointer. They name addresses for theorems; they do not change
the run. -/

/-- A writable C data object: its symbol, address, size, and initial bytes (`.bss`: zero, `init`
empty). Its run-time content is not fixed by the binary, so it is not part of
`Program.DataLoaded`: a theorem states what it needs about it. -/
structure CData where
  name : String
  base : Nat
  size : Nat
  bss : Bool
  init : List Nat
deriving Repr, Inhabited

/-- The address of the object `name` (`0` if there is none). -/
def CData.addr (ds : List CData) (name : String) : Nat :=
  ((ds.find? (·.name == name)).map (·.base)).getD 0

/-- The executable's TLS segment (`PT_TLS`: `p_memsz`, `p_align`, the `.tdata` bytes) and its
`STT_TLS` symbols (name, offset in the segment, size). -/
structure TLSImage where
  size : Nat
  align : Nat
  init : List Nat
  vars : List (String × Nat × Nat)
deriving Repr, Inhabited

/-- `n` rounded up to a multiple of `a` (`a ≤ 1`: `n`). -/
def roundUp (n a : Nat) : Nat := if a ≤ 1 then n else (n + a - 1) / a * a

/-- The offset of the variable `name` in the TLS segment (`0` if there is none). -/
def TLSImage.varOff (t : TLSImage) (name : String) : Nat :=
  ((t.vars.find? (·.1 == name)).map (·.2.1)).getD 0

/-- The offset below the thread pointer (`FS`) of the executable's TLS block on x86-64 (ELF TLS
variant II: the block ends at the thread control block). -/
def TLSImage.x64Off (t : TLSImage) : Nat := roundUp t.size t.align

/-- The address of the `__thread` variable `name` on x86-64, for the thread whose `FS` base is
`fs`. -/
def TLSImage.x64Addr (t : TLSImage) (fs : BitVec 64) (name : String) : Nat :=
  fs.toNat - t.x64Off + t.varOff name

/-- The offset of the executable's TLS block from the thread pointer on AArch64 (ELF TLS variant
I: the 16-byte thread control block, rounded up to the segment's alignment). -/
def TLSImage.a64Off (t : TLSImage) : Nat := roundUp 16 t.align

/-- The address of the `__thread` variable `name` of the thread whose pointer is `tp` (AArch64). -/
def TLSImage.a64Addr (t : TLSImage) (tp : BitVec 64) (name : String) : Nat :=
  tp.toNat + t.a64Off + t.varOff name

end Janus

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
register, the flags, the SIMD&FP registers, `TPIDR_EL0` and the exclusive monitor arbitrary:
`cgocall` is an ordinary Go call, the C code and the runtime may leave the monitor marking bytes
of their own, and the goroutine may resume on another thread; the store-exclusive outcome stream
`exclPass` continues). `FPCR` is preserved (the C code
restores it, `CReturn.fpcr`); `FPSR` is arbitrary: its cumulative exception flags are sticky
and C floating point may set them. -/
def GoResume (s s' : State) (m : Memory) : Prop :=
  ∃ regs flags vregs tpidr fpsr excl,
    s' = { s with regs := regs, pc := s.regs GoABI.regLR, flags := flags, mem := m,
                  vregs := vregs, tpidr := tpidr, fpsr := fpsr, excl := excl } ∧
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
* the same thread (`TPIDR_EL0`) and `DCZID_EL0`, and the same `FPCR`: `asmcgocall` switches
  only the stack and `g` on the calling thread and executes no instruction that writes `FPCR`
  (`runtime/asm_arm64.s`), so the C function sees the Go caller's floating-point control state.
  Every other register, the flags and the SIMD&FP registers are arbitrary. -/
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
  fpcr : t.fpcr = s.fpcr

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


/-! ## Combining contracts

A C function may call several kinds of external functions (libc through the PLT, `setjmp`, a
callback into Go). `C₁.plus C₂` allows the calls of both; `Contract.Disjoint` (the contracts
name different functions) makes the parts refine separately. -/

/-- The calls of `C₁` and of `C₂`. A result is one of the contract that allowed the call. -/
def Contract.plus (C₁ C₂ : Contract) : Contract where
  safe f s := C₁.safe f s ∨ C₂.safe f s
  next f s s' := (C₁.safe f s ∧ C₁.next f s s') ∨ (C₂.safe f s ∧ C₂.next f s s')

/-- `C` and `D` never allow the same function. -/
def Contract.Disjoint (C D : Contract) : Prop := ∀ f s s', C.safe f s → D.safe f s' → False

theorem Contract.Disjoint.symm {C D : Contract} (h : C.Disjoint D) : D.Disjoint C :=
  fun f s s' h₁ h₂ => h f s' s h₂ h₁

/-- Two contracts that only allow the functions named in `n₁` and `n₂`, disjoint lists, are
disjoint. -/
theorem Contract.disjoint_of_names {C D : Contract} (n₁ n₂ : List String)
    (h₁ : ∀ f s, C.safe f s → f ∈ n₁) (h₂ : ∀ f s, D.safe f s → f ∈ n₂)
    (hd : ∀ f, f ∈ n₁ → f ∈ n₂ → False) : C.Disjoint D :=
  fun f s s' hc hd' => hd f (h₁ f s hc) (h₂ f s' hd')

/-- A theorem under `C₁` holds under `C₁.plus C₂`. -/
theorem Contract.Refines.plus_left {C₁ C₂ : Contract} (hd : C₂.Disjoint C₁) :
    (C₁.plus C₂).Refines C₁ := fun f s h =>
  ⟨.inl h, fun _ hn => hn.elim (fun h' => h'.2) (fun h' => (hd f s s h'.1 h).elim)⟩

/-- A theorem under `C₂` holds under `C₁.plus C₂`. -/
theorem Contract.Refines.plus_right {C₁ C₂ : Contract} (hd : C₁.Disjoint C₂) :
    (C₁.plus C₂).Refines C₂ := fun f s h =>
  ⟨.inr h, fun _ hn => hn.elim (fun h' => (hd f s s h'.1 h).elim) (fun h' => h'.2)⟩

/-- Refine both parts of a sum. -/
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

/-- A contract is **total** when every call it allows has a result: a run reaching it continues
(and a theorem under it is not vacuous there). Every contract of `Janus.FFI` and
`Janus.Contracts.Libc` has a `…_satisfiable` theorem of this form or stronger. -/
def Contract.Total (C : Contract) : Prop := ∀ f s, C.safe f s → ∃ s', C.next f s s'

theorem Contract.Total.plus {C₁ C₂ : Contract} (h₁ : C₁.Total) (h₂ : C₂.Total) :
    (C₁.plus C₂).Total := fun f s hs => hs.elim
  (fun h => let ⟨s', h'⟩ := h₁ f s h; ⟨s', .inl ⟨h, h'⟩⟩)
  (fun h => let ⟨s', h'⟩ := h₂ f s h; ⟨s', .inr ⟨h, h'⟩⟩)

/-- Under a total contract, a run that returns (`ReturnsC`) has a final state. -/
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

theorem none_total : Contract.none.Total := fun _ _ h => h.elim

/-! ## C function pointers

A C function that calls through a function pointer (a `qsort` comparator, a callback) is proved
for every pointer satisfying a **function-pointer hypothesis** `CFuncIs p f pre post`: the code at
`f` behaves as a C function with precondition `pre` and postcondition `post` (a callee
`Summary` that also restores what AAPCS64 requires). The theorem is stated over `p.link impl`
for every `impl` (the code behind the pointer is not extracted), as for runtime contracts
(docs/RUNTIME-CONTRACTS.md), so the hypothesis can hold: it is the C analogue of
`Janus.Spec.FuncvalIs`, which names an extracted closure. A concrete function satisfying it
(proved from its machine code) discharges it (`examples/proofs-cgo/*/EArgMin.lean`).

At the indirect call (`BLR Xn`), `Reaches.blr_call` (`ReachesRet.blr_call`) replaces the call by
the hypothesis: run `janus_run until [pc]` to the `BLR`, apply the lemma, and continue with
`janus_run` from every state the callee may return in. -/

/-- The code at `f` (a 4-aligned user address) is a C function: from every state at `f`
satisfying `pre`, it returns to `X30` restoring `CReturn` and satisfying `post`. -/
def CFuncIs (p : Program) (f : W64) (pre : State → Prop) (post : State → State → Prop) : Prop :=
  f.toNat % 4 = 0 ∧ f.toNat < 2 ^ 48 ∧ Summary p f.toNat pre (fun s s' => CReturn s s' ∧ post s s')

/-- The callee's entry state of `BLR Xrn` at `s`. -/
def blrState (s : State) (rn : Nat) : State := { s.writeZR 30 (s.pc + 4) with pc := s.regs rn }

@[simp] theorem blrState_pc (s : State) (rn : Nat) : (blrState s rn).pc = s.regs rn := rfl
@[simp] theorem blrState_lr (s : State) (rn : Nat) : (blrState s rn).regs 30 = s.pc + 4 := by
  simp [blrState, State.writeZR]

theorem exec_blr {s : State} {rn : Nat} (hrn : rn ≠ 31) (hal : (s.regs rn).toNat % 4 = 0)
    (hlt : (s.regs rn).toNat < 2 ^ 48) : exec (.blr rn) s = .ok (blrState s rn) := by
  have h56 : ¬ (s.regs rn).toNat ≥ 2 ^ 56 := by omega
  simp only [exec, State.readZR, if_neg hrn, branchReg, if_neg h56, if_pos hal]
  have : (s.writeZR 30 (s.pc + 4)).regs rn = s.regs rn ∨ rn = 30 := by
    by_cases h : rn = 30
    · exact .inr h
    · left; simp [State.writeZR, h]
  rfl

/-- An indirect call through a function pointer satisfying `CFuncIs`. -/
theorem Reaches.blr_call {p : Program} {s : State} {Q : Outcome → Prop} {c w rn : Nat}
    {pre : State → Prop} {post : State → State → Prop}
    (hpc : s.pc = BitVec.ofNat 64 c) (hok : stepOK p c w (.blr rn) = true) (hrn : rn ≠ 31)
    (hf : CFuncIs p (s.regs rn) pre post) (hpre : pre (blrState s rn))
    (h : ∀ s', s'.pc = s.pc + 4 → CReturn (blrState s rn) s' → post (blrState s rn) s' →
      Reaches p s' Q) : Reaches p s Q := by
  obtain ⟨hal, hlt, hsum⟩ := hf
  refine Reaches.step hpc hok (exec_blr hrn hal hlt) ?_
  refine Reaches.call (entry := (s.regs rn).toNat) hsum (by simp) hpre fun s' hr hq => ?_
  exact h s' (by rw [hr, blrState_lr]) hq.1 hq.2

/-- `Reaches.blr_call` inside a callee (`ReachesRet`). -/
theorem ReachesRet.blr_call {p : Program} {s : State} {ret : W64} {Q : State → Prop}
    {c w rn : Nat} {pre : State → Prop} {post : State → State → Prop}
    (hpc : s.pc = BitVec.ofNat 64 c) (hok : stepOK p c w (.blr rn) = true) (hrn : rn ≠ 31)
    (hf : CFuncIs p (s.regs rn) pre post) (hpre : pre (blrState s rn))
    (h : ∀ s', s'.pc = s.pc + 4 → CReturn (blrState s rn) s' → post (blrState s rn) s' →
      ReachesRet p ret s' Q) : ReachesRet p ret s Q := by
  obtain ⟨hal, hlt, hsum⟩ := hf
  refine ReachesRet.step hpc hok (exec_blr hrn hal hlt) ?_
  refine ReachesRet.call (entry := (s.regs rn).toNat) hsum (by simp) hpre fun s' hr hq => ?_
  exact h s' (by rw [hr, blrState_lr]) hq.1 hq.2

/-- A `CFuncIs` hypothesis about `p` holds in `p.withExit ret`. -/
theorem CFuncIs.withExit {p : Program} {f : W64} {pre : State → Prop}
    {post : State → State → Prop} {ret : Nat} (h : CFuncIs p f pre post) (hret : RetAddr p ret) :
    CFuncIs (p.withExit ret) f pre post := ⟨h.1, h.2.1, h.2.2.withExit hret⟩

/-! ## Callbacks: C calls an exported Go function (`//export`)

For `//export F`, cgo generates a C function `F` (in `_cgo_export.c`) that packs its arguments
into a frame and calls `crosscall2(_cgoexp_<hash>_F, &frame, size, ctxt)`; `crosscall2`
(`runtime/cgo/asm_arm64.s`, assembly) saves the AAPCS64 callee-saved registers, loads `g`
(`load_g`) and calls `runtime.cgocallback(fn, frame, ctxt)` (ABI0: the arguments at
`[SP+8]`, `[SP+16]`, `[SP+24]`). `cgocallback` re-enters Go: it gets `g` from TLS (borrowing an
`M` with `needm` on a thread Go did not create), switches from the system stack to the
goroutine's stack (`X28 = g`), and calls `fn(frame)` with the Go ABIInternal convention; the
Go function `_cgoexp_<hash>_F` unpacks the frame, calls `F` and stores the results in the frame;
then `cgocallback` switches back and returns to `crosscall2`, which restores the callee-saved
registers.

Everything but `cgocallback` is machine code in the binary and is executed by the model: the
C wrapper, `_cgo_wait_runtime_init_done`, `_cgo_release_context`, `crosscall2`, `load_g` and the
Go function behind the export (the extractor follows its address, `cmd/janus/cenv.go`). The
trusted contract `CgoCallback` describes `cgocallback`: it runs the Go function **in the
model** from a Go call state (`CallbackEntry`) and resumes the C caller with the Go code's memory
writes (`CbResumed`). `CallbackSpec` is the C-side assumption, and `CgoCallback.refines` the
reverse composition theorem (as `CgoCall.refines` is for Go → C). -/

/-- The entry of the Go function behind `//export F` in the extraction `p`: the segment
`_cgoexp_<hash>_F`, found by the shape of its name (cgo's 12-hex-digit `<hash>` is derived from
the package's files, so it changes when they do; `0` if there is none). -/
def exportAddr (p : Program) (F : String) : Nat :=
  ((p.segments.find? fun sg => "_cgoexp_".toList.isPrefixOf sg.name.toList &&
      sg.name.toList.drop 21 == F.toList).map (·.base)).getD 0

/-- Bytes of the C (system) stack below `SP` that `cgocallback` may use for its own frames
(`cgocallback` itself, `needm`, the `g0` frames on a thread Go did not create): the linker's
bound on a chain of nosplit frames (`abi.StackNosplitBase`, 800 bytes) plus a margin, as for
`cgoStackScratch`; `needm` and `dropm` are not nosplit but run on the system stack, which for a
C thread is the thread's own stack (the theorem's C stack window must cover them:
`cbStackScratch` bytes). -/
def cbStackScratch : Nat := 16384

/-- Go's TLS `g` slot of the thread whose `TPIDR_EL0` is `tp`, in the executable's TLS image `t`:
the variable `runtime.tls_g` (variant I: `TPIDR_EL0 + roundUp 16 align + off`). The Go linker
puts it at offset 0 of the executable's block, so it is `TPIDR_EL0 + 16` when the segment's
alignment is at most 16; it moves when the C code's `__thread` variables come first, which is why
the callback contract takes the extraction's `TLSImage`. `load_g` (executed by the model in
`crosscall2`) and `cgocallback` (trusted) read it. -/
def tlsGSlot (t : TLSImage) (tp : W64) : Nat := t.a64Addr tp "runtime.tls_g"

/-- The bytes a `cgocallback` from the C state `s` may change besides what the Go code writes:
the C stack below `SP` (`cbStackScratch` bytes), its ABI0 argument slots `[SP+8, SP+32)` (`[SP]`
is the caller's, untouched), and Go's TLS `g` slot (`tlsGSlot`, which `cgocallback` points at
the goroutine's `g`, `g0`, or nil around the call). -/
def cbClobber (t : TLSImage) (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - cbStackScratch, s.sp.toNat), (s.sp.toNat + 8, s.sp.toNat + 32),
   (tlsGSlot t s.tpidr, tlsGSlot t s.tpidr + 8)]

/-- Memory of the C state `s` that `cgocallback` leaves alone: accessible in `s` and outside
`cbClobber t s`. -/
def CbKept (t : TLSImage) (s : State) (a n : Nat) (w : Bool) : Prop :=
  s.mem.accessible a n w = true ∧ Outside a n (cbClobber t s)

/-- The goroutine stack of the examples whose Go side needs little: 4096 bytes. -/
def cbGoStack : Nat := 4096

/-- `runtime.stackGuard` of Go 1.26.0 on linux (non-race): `abi.StackNosplitBase` (800) +
`abi.StackSmall` (128). A goroutine's `stackguard0` is `stack.lo + stackGuard` while no
preemption is requested. -/
def stackGuard : Nat := 928

/-- The goroutine stack `cgocallback` enters the Go code with, and the runtime readiness under
which it does so (round 9 C1 style, as `Janus.Contracts.RtReady` for the allocator):

* `size`: bytes of goroutine stack below the Go call's `SP` (`CallbackEntry.goStack`, with the
  stack guard of `CallbackEntry.guard`). A Go function with a frame of `F` bytes passes its
  stack check when `F + stackGuard - StackSmall < size` (so `size > F + 800`), and its frame and
  the nosplit frames below it fit.
* `ready`: the readiness predicate, applied at the stub to `[fn, size]`, the `g` that
  `cgocallback`'s `load_g` reads (the TLS `g` slot), `SP`, and the memory as the runtime owns it
  (`rtView rt`). The real runtime meets the contract for `ready := "from this runtime state, the
  goroutine `cgocallback` switches to (`m.curg`, or the extra `M`'s on a C thread) has `size`
  bytes of stack below the entry, growing it if needed, and no preemption request pending"`: a
  goroutine stack is grown on demand (`morestack` copies it to a larger one and re-runs the
  function) up to `maxstacksize` (1 GB), so this holds whenever the runtime can allocate that
  stack. A theorem quantifies over `ready` and assumes it at its entry for the callback it
  makes; the C code's own stores (outside `rt`) do not change it (`rtView_writeLE`). -/
structure CbStack where
  size : Nat
  rt : List (Nat × Nat)
  ready : Janus.Contracts.RtReady

/-- The readiness of `k` at the stub state `s` (see `CbStack`). -/
def CbStack.Ready (k : CbStack) (t : TLSImage) (s : State) : Prop :=
  k.ready [s.mem.readLE (s.sp.toNat + 8) 8, k.size] (s.mem.readLE (tlsGSlot t s.tpidr) 8)
    s.sp.toNat (Janus.Contracts.rtView k.rt s.mem)

/-- The Go call state `u` that `cgocallback` makes from the C state `s` (at its entry: the ABI0
call from `crosscall2`), with `gs` bytes of goroutine stack, returning to `ret` (inside
`cgocallbackg1`, outside the extracted code). Trusted description (`runtime/asm_arm64.s`,
`cgocallback`; `runtime/cgocall.go`, `cgocallbackg`, `cgocallbackg1`), following the code:

* `cgocallback` loads `g` from the TLS slot (`load_g`; `needm` borrows an extra `M` when it is
  nil), takes `m.curg`, points the TLS slot at it (`save_g`) and moves `X28` to it, switches `SP`
  to the goroutine's saved stack pointer (`g.sched.sp`, minus its frame) and calls
  `cgocallbackg`, which leaves the system call (`exitsyscall`, restoring `stackguard0`) and calls
  `cgocallbackg1`, which calls `fn(frame)`:
  * the ABIInternal call `fn(frame)`: `pc = [SP+8]`, `X0 = [SP+16]`, `X30 = ret`;
  * `g` (`gReg`, `tlsG`): `X28` is the goroutine's `g`, its struct readable, Go memory (not C
    memory: `gSep`; not on the goroutine stack: `gOff`), and the TLS slot holds it;
  * the goroutine stack (`goStack`, `stackSep`): `SP` 16-aligned, `gs` writable bytes below it and
    the frame's spill slot above it (`[SP, SP+16)`), none of them C memory;
  * the stack guard (`guard`): `g.stackguard0 + gs ≤ SP + stackGuard`, i.e. the stack's low end
    (`stackguard0 - stackGuard`) is at least `gs` bytes below `SP` (no pending preemption,
    whose `stackPreempt` guard would send every check to `morestack`);
* C memory `cgocallback` leaves alone (`CbKept`) holds the same bytes and is accessible in the
  same way (`kept`, `keptAcc`);
* the same thread (`TPIDR_EL0`; a callback runs on the thread that called it), `DCZID_EL0` and
  `FPCR` (no instruction of the runtime path writes `FPCR`).

Every other register, the flags, the SIMD&FP registers and the exclusive monitor are arbitrary;
further facts the Go code needs (an allocator's readiness at its calls) are the readiness
predicate `R` of `CgoCallback`. -/
structure CallbackEntry (t : TLSImage) (p : Program) (gs : Nat) (s u : State) (ret : Nat) : Prop where
  pc : u.pc = BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 8) 8)
  arg : u.regs 0 = BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 16) 8)
  lr : u.regs GoABI.regLR = BitVec.ofNat 64 ret
  retAddr : RetAddr p ret
  gReg : (u.regs 28).toNat + gStructSize ≤ 2 ^ 48 ∧
    u.mem.accessible (u.regs 28).toNat gStructSize false = true
  gSep : ∀ a n w, s.mem.accessible a n w = true →
    Outside a n [((u.regs 28).toNat, (u.regs 28).toNat + gStructSize)]
  tlsG : u.mem.readLE (tlsGSlot t u.tpidr) 8 = (u.regs 28).toNat
  goStack : u.sp.toNat % 16 = 0 ∧ gs ≤ u.sp.toNat ∧ u.sp.toNat + 16 ≤ 2 ^ 48 ∧
    u.mem.accessible (u.sp.toNat - gs) (gs + 16) true = true
  stackSep : ∀ a n w, s.mem.accessible a n w = true →
    Outside a n [(u.sp.toNat - gs, u.sp.toNat + 16)]
  gOff : Outside (u.regs 28).toNat gStructSize [(u.sp.toNat - gs, u.sp.toNat + 16)]
  guard : u.mem.readLE ((u.regs 28).toNat + 16) 8 + gs ≤ u.sp.toNat + stackGuard
  kept : ∀ a n, CbKept t s a n false → u.mem.readLE a n = s.mem.readLE a n
  keptAcc : ∀ a n w, CbKept t s a n w → u.mem.accessible a n w = true
  tpidr : u.tpidr = s.tpidr
  dczid : u.dczid = s.dczid
  fpcr : u.fpcr = s.fpcr

/-- The Go code's stack check passes at the entry `u` for a frame adjustment `adj` (the
prologue compares `SP - adj` with `stackguard0`) when `adj + stackGuard < gs`: `GuardOK u adj`. -/
theorem CallbackEntry.guardOK {t : TLSImage} {p : Program} {gs : Nat} {s u : State} {ret : Nat}
    (he : CallbackEntry t p gs s u ret) {adj : Nat} (hadj : adj + stackGuard < gs) :
    Janus.Spec.GuardOK u adj := by
  obtain ⟨h1, h2⟩ := he.gReg
  have hg := he.guard
  refine ⟨by unfold gStructSize at h1; omega, Memory.accessible_sub _ h2 (by simp) (by omega)
    (by unfold gStructSize; omega), by omega⟩

/-- How the C caller resumes after `cgocallback` returns: at `X30` (in `crosscall2`), with `SP`,
`TPIDR_EL0`, `DCZID_EL0` and `FPCR` kept (an ABI0 callee: every general register, the flags,
the SIMD&FP registers, `FPSR` and the exclusive monitor arbitrary; `crosscall2` restores what
AAPCS64 needs), and memory `m`. The store-exclusive outcome stream (`exclPass`) continues: the
callback's own store-exclusives are the Go state's (`u`, arbitrary). -/
def CbResume (s s' : State) (m : Memory) : Prop :=
  ∃ regs flags vregs fpsr excl,
    s' = { s with regs := regs, pc := s.regs GoABI.regLR, flags := flags, mem := m,
                  vregs := vregs, fpsr := fpsr, excl := excl }

/-- The C caller resumes from the final Go state `u'`: memory with the regions of `s`, the Go
code's result on C memory outside `cbClobber t s`, the old bytes where `s` has no access, and
arbitrary clobbered bytes. -/
def CbResumed (t : TLSImage) (s u' s' : State) : Prop :=
  ∃ m, CbResume s s' m ∧ m.regions = s.mem.regions ∧
    ∀ a, Outside a 1 (cbClobber t s) →
      m.bytes a = if s.mem.accessible a 1 false then u'.mem.bytes a else s.mem.bytes a

/-- The **trusted** contract of `runtime.cgocallback` (arm64), for the executable's TLS image
`t`, Go code that may itself call external functions under `Cin` (`Contract.none` when it calls
none; `CgoCall p` when it calls C again), the readiness predicate `R` on the Go call state
(`fun _ => True` for Go code that needs nothing of the runtime beyond `CallbackEntry`; otherwise
e.g. an allocator's readiness at its calls) and the goroutine stack `k` (`CbStack`): the C stack
has `cbStackScratch` writable bytes below `SP` and the argument slots above, the runtime is ready
(`k.Ready t s`), and for every Go call state `cgocallback` may make with `k.size` bytes of
goroutine stack in which `R` holds, the Go function returns, restoring `SP`, `g` and `FP` (the
ABIInternal return `cgocallbackg1` relies on); the possible results are the C states resumed
from the final Go states (`CbResumed`). -/
def CgoCallback (t : TLSImage) (p : Program) (Cin : Contract) (R : State → Prop) (k : CbStack) :
    Contract where
  safe f s := f = "runtime.cgocallback.abi0" ∧ CStack s cbStackScratch 32 ∧ k.Ready t s ∧
    ∀ u ret, CallbackEntry t p k.size s u ret → R u →
      ReturnsC (p.withExit ret) Cin (ABIReturnC u) u
  next f s s' := f = "runtime.cgocallback.abi0" ∧ ∃ u ret u', CallbackEntry t p k.size s u ret ∧
    R u ∧ RunsTo (p.withExit ret) Cin u u' ∧ ABIReturnC u u' ∧ CbResumed t s u' s'

/-- The C-side assumption: `cgocallback` called (by `crosscall2`) with `fn = [SP+8]` the Go
function at `fn`, in a state satisfying `G`, returns (`CbResume`) with memory that agrees with
`E s` outside `cbClobber t s`. -/
def CallbackSpec (t : TLSImage) (fn : Nat) (G : State → Prop) (E : State → Memory) : Contract where
  safe f s := f = "runtime.cgocallback.abi0" ∧ s.mem.readLE (s.sp.toNat + 8) 8 = fn ∧ G s
  next f s s' := f = "runtime.cgocallback.abi0" ∧
    ∃ m, CbResume s s' m ∧ MemFrame (E s) m (cbClobber t s)

theorem CbResumed.memFrame {t : TLSImage} {s u' s' : State} {E : Memory} (h : CbResumed t s u' s')
    (hE : E.regions = s.mem.regions)
    (hacc : ∀ a, Outside a 1 (cbClobber t s) → s.mem.accessible a 1 false = true →
      u'.mem.bytes a = E.bytes a)
    (hna : ∀ a, Outside a 1 (cbClobber t s) → s.mem.accessible a 1 false = false →
      s.mem.bytes a = E.bytes a) :
    ∃ m, CbResume s s' m ∧ MemFrame E m (cbClobber t s) := by
  obtain ⟨m, hres, hreg, hb⟩ := h
  refine ⟨m, hres, ⟨fun a n ho => readLE_congr fun i hi => ?_, fun a n w => ?_⟩⟩
  · have ho1 := outside_one ho hi
    rw [hb _ ho1]
    cases hc : s.mem.accessible (a + i) 1 false
    · simp only [Bool.false_eq_true, ite_false]; exact hna _ ho1 hc
    · simp only [ite_true]; exact hacc _ ho1 hc
  · simp only [Memory.accessible, hreg, hE]

/-- **Reverse composition** (C → Go). If the Go function at `fn` satisfies `EnsuresC` under `Cin`
for every frame address `a`, with a precondition that follows from `G`, the trusted entry facts
and `R`, and a postcondition from which the C memory `E s` follows, and `G` gives the stub's
stack window and the runtime's readiness, then the trusted contract `CgoCallback t p Cin R k`
refines the C-side assumption `CallbackSpec t fn G E`: a C-side theorem under `CallbackSpec` plus
the Go-side `EnsuresC` give the C theorem under `CgoCallback` alone. -/
theorem CgoCallback.refines {t : TLSImage} {p : Program} {Cin : Contract} {R : State → Prop}
    {k : CbStack} {fn : Nat} {G : State → Prop} {E : State → Memory}
    {pre : W64 → State → Prop} {post : W64 → State → State → Prop}
    (hGo : ∀ a, EnsuresC p Cin fn [a] (pre a) (post a))
    (hstack : ∀ s, G s → CStack s cbStackScratch 32)
    (hready : ∀ s, G s → k.Ready t s)
    (hpre : ∀ s u ret, G s → CallbackEntry t p k.size s u ret → R u →
      pre (BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 16) 8)) u)
    (hE : ∀ s, G s → (E s).regions = s.mem.regions)
    (hacc : ∀ s u ret u', G s → CallbackEntry t p k.size s u ret → R u → ABIReturnC u u' →
      post (BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 16) 8)) u u' →
      ∀ a, Outside a 1 (cbClobber t s) → s.mem.accessible a 1 false = true →
        u'.mem.bytes a = (E s).bytes a)
    (hna : ∀ s, G s → ∀ a, Outside a 1 (cbClobber t s) → s.mem.accessible a 1 false = false →
      s.mem.bytes a = (E s).bytes a) :
    (CgoCallback t p Cin R k).Refines (CallbackSpec t fn G E) := by
  intro f s ⟨hf, hfn, hG⟩
  have hfnv : BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 8) 8) = BitVec.ofNat 64 fn := by rw [hfn]
  have hcall : ∀ u ret, CallbackEntry t p k.size s u ret →
      CallSetup (p.withExit ret) fn [BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 16) 8)] u :=
    fun u ret he => {
      pc := by rw [he.pc, hfnv]
      lr := by rw [he.lr]; rfl
      args := fun i hi => by
        have : i = 0 := by simp at hi; omega
        subst this; simpa using he.arg }
  refine ⟨⟨hf, hstack s hG, hready s hG, fun u ret he hR => ?_⟩, ?_⟩
  · exact (hGo _ ret he.retAddr u (hcall u ret he) (hpre s u ret hG he hR)).mono fun _ h => h.1
  · rintro s' ⟨hf', u, ret, u', he, hR, hrun, hab, hres⟩
    refine ⟨hf', ?_⟩
    have hq := (hGo _ ret he.retAddr u (hcall u ret he) (hpre s u ret hG he hR)).runsTo hrun
    exact hres.memFrame (hE s hG) (hacc s u ret u' hG he hR hab hq.2) (hna s hG)

/-! ## `alloca` and variable-length frames

gcc allocates `alloca(n)` (and a VLA) by moving `SP` down by `n` rounded up to 16, after
stack-clash probing: with `-fstack-clash-protection` (Ubuntu's default) it first moves `SP` down
page by page (64 KiB on arm64, 4 KiB on amd64), storing to each new page, then by the rest. The
rounding is done with masks; these lemmas turn them into arithmetic (`omega`), and `CStack.sub`
moves a stack window with `SP`. -/

theorem and_lowMask_eq_mod (x : BitVec 64) (k : Nat) (hk : k ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have h1 : (2 ^ k - 1) % 2 ^ 64 = 2 ^ k - 1 := by
    apply Nat.mod_eq_of_lt
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hk
    omega
  rw [h1, Nat.and_two_pow_sub_one_eq_mod]

theorem and_highMask_eq (x : BitVec 64) (k : Nat) (hk : k ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ 64 - 2 ^ k)).toNat = x.toNat / 2 ^ k * 2 ^ k := by
  have h1 := Nat.one_le_two_pow (n := k)
  have hle : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hk
  have hm : (2 ^ 64 - 2 ^ k) % 2 ^ 64 = 2 ^ 64 - 2 ^ k := Nat.mod_eq_of_lt (by omega)
  have hsplit : 2 ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, hm, hsplit]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : k ≤ i
  · have he : i - k + k = i := Nat.sub_add_cancel hi
    simp only [hi, decide_true, Bool.true_and, he]
    by_cases h64 : i - k < 64 - k
    · simp [h64]
    · have : x.toNat.testBit i = false := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [h64, this]
  · simp [hi]

/-- `x & (2^k − 2^j)`: bits `j … k−1` of `x` (the size masks of `alloca`, e.g. `0xfff0`). -/
theorem and_rangeMask_eq (x : BitVec 64) (j k : Nat) (hj : j ≤ k) (hk : k ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ k - 2 ^ j)).toNat = x.toNat % 2 ^ k / 2 ^ j * 2 ^ j := by
  have h1 := Nat.one_le_two_pow (n := j)
  have hjk : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hj
  have hle : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hk
  have hm : (2 ^ k - 2 ^ j) % 2 ^ 64 = 2 ^ k - 2 ^ j := Nat.mod_eq_of_lt (by omega)
  have hsplit : 2 ^ k - 2 ^ j = (2 ^ (k - j) - 1) * 2 ^ j := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hj]
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, hm, hsplit]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : j ≤ i
  · have he : i - j + j = i := Nat.sub_add_cancel hi
    simp only [hi, decide_true, Bool.true_and, he]
    by_cases h2 : i - j < k - j
    · have : i < k := by omega
      simp [h2, this]
    · have : ¬ i < k := by omega
      simp [h2, this]
  · simp [hi]

/-- `LSL #3` as gcc's `UBFM` decodes (`lsl x1, x0, #3`): a rotation and a mask. -/
theorem rot61 (n : BitVec 64) :
    (n.rotateRight 61 &&& 18446744073709551608#64 &&& 18446744073709551615#64) = n <<< 3 := by
  have m1 : ∀ i (h : i < 64), (18446744073709551608#64 : BitVec 64)[i] = decide (3 ≤ i) := by decide
  have m2 : ∀ i (h : i < 64), (18446744073709551615#64 : BitVec 64)[i] = true := by decide
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_shiftLeft, m1 i hi, m2 i hi]
  by_cases h : i < 3
  · simp [h]
  · simp [h]; omega

/-- A C stack window after `SP` moved down by `n` (a multiple of 16 inside the window). -/
theorem CStack.sub {s : State} {below above n : Nat} (h : CStack s below above) (hn : n ≤ below)
    (h16 : n % 16 = 0) {t : State} (hsp : t.sp.toNat = s.sp.toNat - n)
    (hm : ∀ a k w, t.mem.accessible a k w = s.mem.accessible a k w) :
    CStack t (below - n) (n + above) := by
  obtain ⟨ha, hb, hc, hd⟩ := h
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hsp, hm, show s.sp.toNat - n - (below - n) = s.sp.toNat - below by omega,
    show below - n + (n + above) = below + above by omega]
  exact hd

/-- `CStack.sub` through a memory frame. -/
theorem CStack.frame {s t : State} {below above n : Nat} {rs : List (Nat × Nat)}
    (h : CStack s below above) (hn : n ≤ below) (h16 : n % 16 = 0)
    (hsp : t.sp.toNat = s.sp.toNat - n) (hf : MemFrame s.mem t.mem rs) :
    CStack t (below - n) (n + above) :=
  CStack.sub h hn h16 hsp hf.accessible

/-- A smaller window of a C stack window. -/
theorem CStack.mono {s : State} {below above below' above' : Nat} (h : CStack s below above)
    (h1 : below' ≤ below) (h2 : above' ≤ above) : CStack s below' above' := by
  obtain ⟨ha, hb, hc, hd⟩ := h
  exact ⟨ha, by omega, by omega, Memory.accessible_mono _ hd (by omega) (by omega)⟩

/-- The low halves of `V8`–`V15` along two calls with no vector instruction in between (`b'` and
`b` have the same `vregs`), in the form of `CReturn`'s goals. -/
theorem _root_.Janus.CABI.CReturn.vlow_trans {a b b' c : State} (h₁ : CReturn a b) (h₂ : CReturn b' c)
    (hb : b'.vregs = b.vregs) :
    (c.vregs 8).toNat % 2 ^ 64 = (a.vregs 8).toNat % 2 ^ 64 ∧
    (c.vregs 9).toNat % 2 ^ 64 = (a.vregs 9).toNat % 2 ^ 64 ∧
    (c.vregs 10).toNat % 2 ^ 64 = (a.vregs 10).toNat % 2 ^ 64 ∧
    (c.vregs 11).toNat % 2 ^ 64 = (a.vregs 11).toNat % 2 ^ 64 ∧
    (c.vregs 12).toNat % 2 ^ 64 = (a.vregs 12).toNat % 2 ^ 64 ∧
    (c.vregs 13).toNat % 2 ^ 64 = (a.vregs 13).toNat % 2 ^ 64 ∧
    (c.vregs 14).toNat % 2 ^ 64 = (a.vregs 14).toNat % 2 ^ 64 ∧
    (c.vregs 15).toNat % 2 ^ 64 = (a.vregs 15).toNat % 2 ^ 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₂.v8, hb, h₁.v8]
  · rw [h₂.v9, hb, h₁.v9]
  · rw [h₂.v10, hb, h₁.v10]
  · rw [h₂.v11, hb, h₁.v11]
  · rw [h₂.v12, hb, h₁.v12]
  · rw [h₂.v13, hb, h₁.v13]
  · rw [h₂.v14, hb, h₁.v14]
  · rw [h₂.v15, hb, h₁.v15]

/-- `c` keeps the low halves of `V8`–`V15` of `a`. -/
def VLow (a c : State) : Prop := ∀ i, 8 ≤ i → i < 16 → (c.vregs i).toNat % 2 ^ 64 = (a.vregs i).toNat % 2 ^ 64

theorem _root_.Janus.CABI.CReturn.vlow {a b : State} (h : CReturn a b) : VLow a b := by
  intro i h1 h2
  have : i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.v8
  · exact h.v9
  · exact h.v10
  · exact h.v11
  · exact h.v12
  · exact h.v13
  · exact h.v14
  · exact h.v15

theorem VLow.trans {a b b' c : State} (h₁ : VLow a b) (h₂ : VLow b' c) (hb : b'.vregs = b.vregs) :
    VLow a c := fun i h1 h2 => by rw [h₂ i h1 h2, hb, h₁ i h1 h2]

theorem VLow.of_eq {a b : State} (h : b.vregs = a.vregs) : VLow a b := fun i _ _ => by rw [h]

/-- The eight equations `CReturn` asks for. -/
theorem VLow.goal {a c : State} (h : VLow a c) :
    (c.vregs 8).toNat % 2 ^ 64 = (a.vregs 8).toNat % 2 ^ 64 ∧
    (c.vregs 9).toNat % 2 ^ 64 = (a.vregs 9).toNat % 2 ^ 64 ∧
    (c.vregs 10).toNat % 2 ^ 64 = (a.vregs 10).toNat % 2 ^ 64 ∧
    (c.vregs 11).toNat % 2 ^ 64 = (a.vregs 11).toNat % 2 ^ 64 ∧
    (c.vregs 12).toNat % 2 ^ 64 = (a.vregs 12).toNat % 2 ^ 64 ∧
    (c.vregs 13).toNat % 2 ^ 64 = (a.vregs 13).toNat % 2 ^ 64 ∧
    (c.vregs 14).toNat % 2 ^ 64 = (a.vregs 14).toNat % 2 ^ 64 ∧
    (c.vregs 15).toNat % 2 ^ 64 = (a.vregs 15).toNat % 2 ^ 64 :=
  ⟨h 8 (by omega) (by omega), h 9 (by omega) (by omega), h 10 (by omega) (by omega),
   h 11 (by omega) (by omega), h 12 (by omega) (by omega), h 13 (by omega) (by omega),
   h 14 (by omega) (by omega), h 15 (by omega) (by omega)⟩

/-- `obtain_cret h`: the equations of `h : CReturn s s'` as hypotheses (for `janus_run`). -/
macro "obtain_cret " h:term : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)

end Janus.FFI
