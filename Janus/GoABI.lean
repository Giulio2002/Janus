import Janus.Run
import Janus.Eface
import Janus.Arm64.MemoryLemmas

/-!
# Go ABIInternal on arm64, and the specification vocabulary

Source of truth: `$GOROOT/src/cmd/compile/abi-internal.md`, section "arm64 architecture"
(checked against Go 1.26.0).

| Register | At call | At return | In body |
| --- | --- | --- | --- |
| `R0`–`R15` | integer arguments | integer results | scratch |
| `R16`, `R17`, `R19`–`R25` | scratch | scratch | scratch |
| `R18` | platform reserved, never used | same | same |
| `R26` | closure context pointer | scratch | scratch |
| `R27` | scratch (assembler temporary) | scratch | scratch |
| `R28` | current goroutine `g` | same | same |
| `R29` | frame pointer | same | same |
| `R30` | link register (return address) | same | scratch in non-leaf functions |
| `RSP` | stack pointer, 16-byte aligned | same | same |

There are **no callee-saved general registers** besides the fixed-meaning ones (`RSP`, `R18`,
`R28`, `R29`); flags (NZCV) are scratch. Arguments and results that do not fit in registers
are stack-assigned. On arm64 the caller's argument area starts at `8(RSP)` at entry
(`0(RSP)` is the caller's own saved-LR slot): first stack-assigned arguments, then
stack-assigned results, then (uninitialised) spill slots for the register arguments, each
group pointer-aligned. The callee may write anywhere in that area.

## Frame pointer

Go code keeps the invariant `R29 = RSP - 8` at every call (the caller set up its own frame
with `SUB $8, RSP, R29`). Leaf functions with a frame rely on it: Go 1.26 restores `R29`
arithmetically (`ADD $(frame-8), RSP, R29`) instead of reloading it, so "`R29` is preserved"
holds only for initial states satisfying `FPConvention`.

## Stack-growth prologue (Go 1.26)

Functions that are not `NOSPLIT` start with one of

```
MOVD 16(R28), R16                       // g.stackguard0
CMP  R16, RSP ; BLS morestack           // frame ≤ StackSmall (128)

MOVD 16(R28), R16
SUB  $k, RSP, R17 ; CMP R16, R17 ; BLS morestack           // medium frame

MOVD 16(R28), R16 ; MOVD $k, R27
SUBS R27, RSP, R17 ; BCC morestack ; CMP R16, R17 ; BLS morestack   // big frame
```

with `k = framesize - StackSmall`. `StackGuardOK s k` (`g` readable, `stackguard0 + k < SP`)
makes every form fall through: no borrow in `SP - k`, and `stackguard0 < SP - k` unsigned.
It also excludes a pending preemption request (`stackguard0 = stackPreempt`, a huge value).
-/

namespace Janus

open Arm64

namespace GoABI

/-! ## Register roles -/

/-- Integer argument / result registers are `R0 .. R(numIntRegs-1)`. -/
def numIntRegs : Nat := 16
/-- Platform register; Go never uses it. -/
abbrev regPlatform : Nat := 18
/-- Closure context pointer at calls. -/
abbrev regClosure : Nat := 26
/-- Assembler / linker temporary. -/
abbrev regTmp : Nat := 27
/-- The current goroutine `g`. -/
abbrev regG : Nat := 28
/-- Frame pointer. -/
abbrev regFP : Nat := 29
/-- Link register. -/
abbrev regLR : Nat := 30

/-- Offset of the first stack-assigned argument from `RSP` at entry (`FixedFrameSize`). -/
def stackArgOffset : Nat := 8
/-- `abi.StackSmall`: frames up to this size compare `SP` directly with the guard. -/
def stackSmall : Nat := 128
/-- `abi.StackBig`: larger frames use the `SUBS`/`BCC` underflow check. -/
def stackBig : Nat := 4096
/-- Offset of `stackguard0` in `runtime.g` (after `stack.lo`, `stack.hi`). -/
def stackguard0Offset : Nat := 16

/-- The immediate subtracted from `RSP` in the prologue (`0` for small frames). -/
def prologueAdj (frameSize : Nat) : Nat := frameSize - stackSmall

/-! ## Calls -/

/-- `ret` is an admissible return address for a call into `p` from outside the extracted code:
4-aligned, a user-space address (below `2^48`, untagged), not inside any extracted code segment
and not a stub address. A real caller's return address is the instruction after its `BL`, in
the caller's own code. Specifications quantify over **every** such `ret` and run
`p.withExit ret`, so the only way to "return" is to branch to the value the caller passed in
`X30`; a branch to any fixed address (such as `p.exitAddr`, or `0` loaded from memory) cannot
reach every admissible `ret`. -/
structure RetAddr (p : Program) (ret : Nat) : Prop where
  aligned : ret % 4 = 0
  user : ret < 2 ^ 48
  notCode : ∀ seg ∈ p.segments, ret < seg.base ∨ seg.base + 4 * seg.words.length ≤ ret
  notStub : ∀ st ∈ p.stubs, st.addr ≠ ret

/-- `s` is a state in which `entry` has just been called with integer register
arguments `args`, returning to `p.exitAddr`. Everything else (other registers, flags, SP,
memory) is arbitrary; specifications quantify over all such states. Specifications use it with
`p.withExit ret` for a universally quantified admissible `ret` (`RetAddr`), never with the
extracted placeholder `p.exitAddr`. -/
structure CallSetup (p : Program) (entry : Nat) (args : List W64) (s : State) : Prop where
  pc : s.pc = BitVec.ofNat 64 entry
  lr : s.regs regLR = BitVec.ofNat 64 p.exitAddr
  args : ∀ i (h : i < args.length), s.regs i = args[i]

/-- Alias: a Go call through ABIInternal. -/
abbrev GoCall := CallSetup

/-- Run the program from a (call) state. -/
def invoke (p : Program) (fuel : Nat) (s : State) : Except Fault Outcome := p.run fuel s

/-- The first `k` integer result registers. -/
def results (k : Nat) (s : State) : List W64 := (List.range k).map s.regs

/-- A 64-bit word at `off` bytes above the stack pointer. -/
def stackWord (s : State) (off : Nat) : W64 := BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + off) 8)

/-- Stack-assigned 64-bit arguments (or results) starting at `8(RSP)`, plus `skip` bytes. -/
def StackWords (s : State) (skip : Nat) (words : List W64) : Prop :=
  ∀ i (h : i < words.length),
    s.mem.readLE (s.sp.toNat + stackArgOffset + skip + 8 * i) 8 = words[i].toNat

/-- The closure context register holds `ctx` (calls to closures). -/
def ClosureCtx (s : State) (ctx : W64) : Prop := s.regs regClosure = ctx

/-- `RSP` is 16-byte aligned (required at every Go call). -/
def SPAligned (s : State) : Prop := s.sp.toNat % 16 = 0

/-- Go's frame-pointer invariant at calls: `R29 = RSP - 8`. -/
def FPConvention (s : State) : Prop := s.regs regFP = s.sp - 8

/-- The caller owns writable stack from `below` bytes under `SP` to `above` bytes over it
(the callee's frame below, the argument/result/spill area above). -/
def StackWritable (s : State) (below above : Nat) : Prop :=
  below ≤ s.sp.toNat ∧ s.mem.accessible (s.sp.toNat - below) (below + above) true = true

/-- `g.stackguard0` as read by `MOVD 16(R28), R16`. -/
def stackguard0 (s : State) : Nat := s.mem.readLE ((s.regs regG).toNat + stackguard0Offset) 8

/-- The stack-growth prologue with adjustment `adj` (see `prologueAdj`) falls through:
`g.stackguard0` is readable and below `SP - adj`. -/
structure StackGuardOK (s : State) (adj : Nat) : Prop where
  noWrap : (s.regs regG).toNat + stackguard0Offset + 8 ≤ 2 ^ 48
  readable : s.mem.accessible ((s.regs regG).toNat + stackguard0Offset) 8 false = true
  below : stackguard0 s + adj < s.sp.toNat

/-! ## Obligations on return -/

/-- What every Go function must restore on return, relative to its call state `s₀`:
`RSP`, `g` (`R28`), the frame pointer (`R29`) and the platform register (`R18`). -/
structure ABIReturn (s₀ s₁ : State) : Prop where
  sp : s₁.sp = s₀.sp
  g : s₁.regs regG = s₀.regs regG
  fp : s₁.regs regFP = s₀.regs regFP
  platform : s₁.regs regPlatform = s₀.regs regPlatform

/-! ## Specifications (total correctness with finite fuel)

The outcome predicates take a program and a state. For a call they are applied to
`p.withExit ret` with `ret` universally quantified (`RetAddr`); `Ensures` does this itself.
A fault (nil or out-of-bounds access, a read-only store, misaligned `SP`, a jump outside the
extracted code, an unsupported instruction) is a crash or a Go panic on real hardware (a
memory fault becomes `runtime.sigpanic`), so it is never "success": `Returns` excludes it, and
`NeverPanics` counts it as a panic. -/

/-- The call returns (reaches `p.exitAddr`) after finitely many steps, in a state
satisfying `post`. Excludes faults, panics, stack growth and non-termination. -/
def Returns (p : Program) (s : State) (post : State → Prop) : Prop :=
  ∃ fuel s', p.run fuel s = .ok (.returned s') ∧ post s'

/-- Execution reaches a Go panic stub (`runtime.panic*`: bounds checks, divide by zero,
explicit `panic`). A nil dereference is not a stub call but a hardware fault: see `Faults`. -/
def Panics (p : Program) (s : State) : Prop :=
  ∃ fuel name s', p.run fuel s = .ok (.stub name .panic s')

/-- Execution stops with a fault: a memory access outside the caller's regions (e.g. a nil
dereference) or to read-only memory, a misaligned `SP`, a jump outside the extracted code or
an unsupported instruction. Running out of fuel is not a fault. -/
def Faults (p : Program) (s : State) : Prop :=
  ∃ fuel e, p.run fuel s = .error e ∧ e ≠ .outOfFuel

/-- Execution never faults and never reaches a Go panic stub, for any fuel. It may return,
reach `morestack`, or run forever (only running out of fuel is allowed as an error). -/
def NeverPanics (p : Program) (s : State) : Prop :=
  ∀ fuel, (∀ name s', p.run fuel s ≠ .ok (.stub name .panic s')) ∧
    (∀ e, p.run fuel s = .error e → e = .outOfFuel)

/-- Execution reaches `runtime.morestack*`. -/
def GrowsStack (p : Program) (s : State) : Prop :=
  ∃ fuel name s', p.run fuel s = .ok (.stub name .morestack s')

/-- Go function contract: for **every** admissible return address `ret` (`RetAddr`) and
**every** call state with these arguments and `X30 = ret` satisfying `pre`, the call returns to
`ret` (never faults or panics), obeys the ABI return rules, and satisfies `post s₀ s₁`. -/
def Ensures (p : Program) (entry : Nat) (args : List W64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ ret, RetAddr p ret → ∀ s, CallSetup (p.withExit ret) entry args s → pre s →
    Returns (p.withExit ret) s (fun s' => ABIReturn s s' ∧ post s s')

/-- `Ensures` stated on the first `nres` integer result registers. -/
def EnsuresResults (p : Program) (entry : Nat) (args : List W64) (nres : Nat)
    (pre : State → Prop) (post : List W64 → Prop) : Prop :=
  Ensures p entry args pre (fun _ s' => post (results nres s'))

/-! ## Lemmas -/

section Lemmas

variable {p : Program} {s s' : State} {entry : Nat} {args : List W64}

theorem invoke_eq (fuel : Nat) : invoke p fuel s = p.run fuel s := rfl

theorem CallSetup.pc_toNat (h : CallSetup p entry args s) (he : entry < 2 ^ 64) :
    s.pc.toNat = entry := by
  rw [h.pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]

theorem CallSetup.lr_toNat (h : CallSetup p entry args s) (he : p.exitAddr < 2 ^ 64) :
    (s.regs regLR).toNat = p.exitAddr := by
  rw [h.lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]

theorem CallSetup.reg (h : CallSetup p entry args s) {i : Nat} (hi : i < args.length) :
    s.regs i = args[i] := h.args i hi

/-- A canonical call state built from any state `s` (used to show `CallSetup` is
satisfiable). -/
def setup (p : Program) (entry : Nat) (args : List W64) (s : State) : State :=
  { s with
    pc := BitVec.ofNat 64 entry
    regs := fun i => if i = regLR then BitVec.ofNat 64 p.exitAddr else args.getD i (s.regs i) }

theorem setup_callSetup (s : State) (h : args.length ≤ numIntRegs) :
    CallSetup p entry args (setup p entry args s) where
  pc := rfl
  lr := by simp [setup]
  args := fun i hi => by
    have : i ≠ regLR := by simp only [numIntRegs, regLR] at h ⊢; omega
    simp [setup, this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

@[simp] theorem results_length (k : Nat) : (results k s).length = k := by simp [results]

@[simp] theorem results_getElem (k i : Nat) (h : i < (results k s).length) :
    (results k s)[i] = s.regs i := by simp [results]

theorem results_zero : results 0 s = [] := rfl

theorem results_succ (k : Nat) : results (k + 1) s = results k s ++ [s.regs k] := by
  simp [results, List.range_succ]

theorem results_one : results 1 s = [s.regs 0] := rfl
theorem results_two : results 2 s = [s.regs 0, s.regs 1] := rfl

theorem StackGuardOK.adj_le {adj : Nat} (h : StackGuardOK s adj) : adj ≤ s.sp.toNat := by
  have := h.below; omega

theorem StackGuardOK.lt_sub {adj : Nat} (h : StackGuardOK s adj) :
    stackguard0 s < s.sp.toNat - adj := by
  have := h.below; omega

/-- `SP - adj` does not wrap. -/
theorem StackGuardOK.sub_toNat {adj : Nat} (h : StackGuardOK s adj) :
    (s.sp - BitVec.ofNat 64 adj).toNat = s.sp.toNat - adj := by
  have h1 := h.adj_le
  have h2 := s.sp.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show adj < 2 ^ 64 by omega),
    show 2 ^ 64 - adj + s.sp.toNat = (s.sp.toNat - adj) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- The guard word address `16(R28)` does not wrap. -/
theorem StackGuardOK.addr_toNat {adj : Nat} (h : StackGuardOK s adj) :
    (s.regs regG + BitVec.ofNat 64 stackguard0Offset).toNat =
      (s.regs regG).toNat + stackguard0Offset := by
  have := h.noWrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [stackguard0Offset] at *
  omega

/-- The prologue's load of the guard succeeds and yields `stackguard0`. -/
theorem StackGuardOK.load {adj : Nat} (h : StackGuardOK s adj) :
    load s.mem ((s.regs regG).toNat + stackguard0Offset) 8 = .ok (stackguard0 s) :=
  load_eq_ok _ h.readable

theorem stackguard0_lt : stackguard0 s < 2 ^ 64 := Memory.readLE_lt _ _ 8

theorem StackGuardOK.mono {adj adj' : Nat} (h : StackGuardOK s adj) (hle : adj' ≤ adj) :
    StackGuardOK s adj' :=
  ⟨h.noWrap, h.readable, by have := h.below; omega⟩

theorem ABIReturn.refl (s : State) : ABIReturn s s := ⟨rfl, rfl, rfl, rfl⟩

theorem ABIReturn.trans {s₀ s₁ s₂ : State} (h₁ : ABIReturn s₀ s₁) (h₂ : ABIReturn s₁ s₂) :
    ABIReturn s₀ s₂ :=
  ⟨h₂.sp.trans h₁.sp, h₂.g.trans h₁.g, h₂.fp.trans h₁.fp, h₂.platform.trans h₁.platform⟩

/-! ### `Returns` / `Panics` -/

theorem Returns.mono {P Q : State → Prop} (h : Returns p s P) (hPQ : ∀ s', P s' → Q s') :
    Returns p s Q := by
  obtain ⟨n, s', hr, hp⟩ := h; exact ⟨n, s', hr, hPQ _ hp⟩

/-- The returned state is unique, so postconditions can be proved separately. -/
theorem Returns.unique {P Q : State → Prop} (hP : Returns p s P) (hQ : Returns p s Q) :
    Returns p s (fun s' => P s' ∧ Q s') := by
  obtain ⟨n, s₁, h₁, hp⟩ := hP
  obtain ⟨m, s₂, h₂, hq⟩ := hQ
  have := Program.run_ok_unique h₁ h₂
  cases this
  exact ⟨n, s₁, h₁, hp, hq⟩

/-- If the call returns with some fuel, it returns with all larger fuel. -/
theorem Returns.run_of_le {P : State → Prop} (h : Returns p s P) :
    ∃ n s', P s' ∧ ∀ m, n ≤ m → p.run m s = .ok (.returned s') := by
  obtain ⟨n, s', hr, hp⟩ := h
  exact ⟨n, s', hp, fun m hm => Program.run_mono hr hm⟩

theorem Returns.neverPanics {P : State → Prop} (h : Returns p s P) : NeverPanics p s := by
  obtain ⟨n, s', hr, _⟩ := h
  intro m
  refine ⟨fun name s'' hm => ?_, fun e he => ?_⟩
  · cases Program.run_ok_unique hr hm
  · by_cases he' : e = .outOfFuel
    · exact he'
    · exact (Program.run_ok_not_error hr he he').elim

theorem Returns.not_panics {P : State → Prop} (h : Returns p s P) : ¬ Panics p s := by
  rintro ⟨m, name, s'', hm⟩; exact (h.neverPanics m).1 name s'' hm

theorem Returns.not_faults {P : State → Prop} (h : Returns p s P) : ¬ Faults p s := by
  rintro ⟨m, e, hm, he⟩; exact he ((h.neverPanics m).2 e hm)

theorem NeverPanics.not_panics (h : NeverPanics p s) : ¬ Panics p s := by
  rintro ⟨m, name, s'', hm⟩; exact (h m).1 name s'' hm

theorem NeverPanics.not_faults (h : NeverPanics p s) : ¬ Faults p s := by
  rintro ⟨m, e, hm, he⟩; exact he ((h m).2 e hm)

/-- "Never panics" is exactly "no panic stub and no fault". -/
theorem neverPanics_iff : NeverPanics p s ↔ ¬ Panics p s ∧ ¬ Faults p s := by
  refine ⟨fun h => ⟨h.not_panics, h.not_faults⟩, fun ⟨hp, hf⟩ m => ⟨?_, fun e he => ?_⟩⟩
  · intro name s'' hm; exact hp ⟨m, name, s'', hm⟩
  · by_cases he' : e = .outOfFuel
    · exact he'
    · exact (hf ⟨m, e, he, he'⟩).elim

theorem Faults.not_returns {P : State → Prop} (h : Faults p s) : ¬ Returns p s P :=
  fun hr => hr.not_faults h

theorem Faults.not_panics (h : Faults p s) : ¬ Panics p s := by
  rintro ⟨m, name, s'', hm⟩
  obtain ⟨n, e, hn, he⟩ := h
  exact Program.run_ok_not_error hm hn he

/-- Steps reaching a faulting instruction establish `Faults`. -/
theorem faults_of_steps {k w : Nat} {e : Fault} (hs : Program.Steps p s k s')
    (hx : s'.pc.toNat ≠ p.exitAddr) (hst : p.stubAt s'.pc.toNat = none)
    (hf : p.fetch s'.pc.toNat = some w) (he : Arm64.step w s' = .error e) (he' : e ≠ .outOfFuel) :
    Faults p s :=
  ⟨k + 1, e, by rw [Program.run_steps hs 1, Program.run_succ_fault hx hst hf he], he'⟩

theorem Faults.of_steps {k : Nat} (hs : Program.Steps p s k s') (h : Faults p s') :
    Faults p s := by
  obtain ⟨n, e, hr, he⟩ := h
  exact ⟨k + n, e, by rw [Program.run_steps hs, hr], he⟩

theorem Returns.not_growsStack {P : State → Prop} (h : Returns p s P) : ¬ GrowsStack p s := by
  obtain ⟨n, s', hr, _⟩ := h
  rintro ⟨m, name, s'', hm⟩
  cases Program.run_ok_unique hr hm

theorem Panics.not_returns {P : State → Prop} (h : Panics p s) : ¬ Returns p s P :=
  fun hr => hr.not_panics h

/-- Prefix composition: ordinary steps, then a call state that returns. -/
theorem Returns.of_steps {k : Nat} {P : State → Prop} (hs : Program.Steps p s k s')
    (h : Returns p s' P) : Returns p s P := by
  obtain ⟨n, s'', hr, hp⟩ := h
  exact ⟨k + n, s'', by rw [Program.run_steps hs, hr], hp⟩

/-- Steps reaching the exit address establish `Returns`. -/
theorem returns_of_steps {k : Nat} {P : State → Prop} (hs : Program.Steps p s k s')
    (hx : s'.pc.toNat = p.exitAddr) (hp : P s') : Returns p s P :=
  ⟨k + 1, s', Program.run_steps_exit hs hx, hp⟩

/-- Steps reaching a panic stub establish `Panics`. -/
theorem panics_of_steps {k : Nat} {st : Stub} (hs : Program.Steps p s k s')
    (hx : s'.pc.toNat ≠ p.exitAddr) (hst : p.stubAt s'.pc.toNat = some st)
    (hk : st.kind = .panic) : Panics p s :=
  ⟨k + 1, st.name, s', by rw [Program.run_steps_stub hs hx hst, hk]⟩

theorem Panics.of_steps {k : Nat} (hs : Program.Steps p s k s') (h : Panics p s') :
    Panics p s := by
  obtain ⟨n, name, s'', hr⟩ := h
  exact ⟨k + n, name, s'', by rw [Program.run_steps hs, hr]⟩

theorem NeverPanics.of_steps {k : Nat} (hs : Program.Steps p s k s') (h : NeverPanics p s) :
    NeverPanics p s' := by
  intro n
  have := h (k + n)
  rw [Program.run_steps hs] at this
  exact this

/-! ### `Ensures` -/

theorem Ensures.returns {pre : State → Prop} {post : State → State → Prop} {ret : Nat}
    (h : Ensures p entry args pre post) (hret : RetAddr p ret)
    (hs : CallSetup (p.withExit ret) entry args s) (hpre : pre s) :
    Returns (p.withExit ret) s (fun s' => ABIReturn s s' ∧ post s s') := h ret hret s hs hpre

theorem Ensures.neverPanics {pre : State → Prop} {post : State → State → Prop} {ret : Nat}
    (h : Ensures p entry args pre post) (hret : RetAddr p ret)
    (hs : CallSetup (p.withExit ret) entry args s) (hpre : pre s) :
    NeverPanics (p.withExit ret) s := (h ret hret s hs hpre).neverPanics

theorem Ensures.mono {pre pre' : State → Prop} {post post' : State → State → Prop}
    (h : Ensures p entry args pre post) (hpre : ∀ s, pre' s → pre s)
    (hpost : ∀ s s', pre' s → post s s' → post' s s') : Ensures p entry args pre' post' :=
  fun ret hret s hs hp => (h ret hret s hs (hpre s hp)).mono fun _ ⟨ha, hq⟩ => ⟨ha, hpost _ _ hp hq⟩

/-! ### Return addresses -/

/-- There is no code at an admissible return address. -/
theorem RetAddr.fetch_none {ret : Nat} (h : RetAddr p ret) : p.fetch ret = none :=
  Program.fetchIn_eq_none h.notCode

/-- No stub sits at an admissible return address. -/
theorem RetAddr.stubAt_none {ret : Nat} (h : RetAddr p ret) : p.stubAt ret = none :=
  Program.stubAt_eq_none h.notStub

theorem RetAddr.lt64 {ret : Nat} (h : RetAddr p ret) : ret < 2 ^ 64 := by
  have := h.user; omega

/-- An address that holds code is not the return address. -/
theorem RetAddr.ne_of_fetch {ret pc w : Nat} (h : RetAddr p ret) (hf : p.fetch pc = some w) :
    pc ≠ ret := by
  rintro rfl; rw [h.fetch_none] at hf; cases hf

/-- A stub address is not the return address. -/
theorem RetAddr.ne_of_stubAt {ret pc : Nat} {st : Stub} (h : RetAddr p ret)
    (hs : p.stubAt pc = some st) : pc ≠ ret := by
  rintro rfl; rw [h.stubAt_none] at hs; cases hs

/-- Decide `RetAddr` on a concrete program: `retAddrCheck p ret = true` by `decide`/`rfl`. -/
def retAddrCheck (p : Program) (ret : Nat) : Bool :=
  ret % 4 == 0 && decide (ret < 2 ^ 48) &&
    p.segments.all (fun seg => decide (ret < seg.base ∨ seg.base + 4 * seg.words.length ≤ ret)) &&
    p.stubs.all (fun st => st.addr != ret)

theorem RetAddr.of_check {ret : Nat} (h : retAddrCheck p ret = true) : RetAddr p ret := by
  simp only [retAddrCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

end Lemmas

/-! ## Go-level outcomes: a call returns, or a panic leaves its frame

`Ensures` describes calls that return. A Go call may instead **panic**: a panic with value `v`
runs the deferred calls of the panicking frame (which may `recover` it, turning it back into a
return) and then leaves the frame, unwinding into the caller. `EnsuresGo` states both outcomes:
`ret s s'` for a return in state `s'`, `pan s v s'` for a panic with value `v` that leaves the
call's frame in state `s'`.

A Go-level execution of a program ends when ordinary steps reach one of:

* the return address (`.returned s'`): a normal return;
* a **panic stub** (`runtime.gopanic`, `runtime.panicBounds`, …): the classifier `atStub name s'`
  says the panic value for that stub and state (`gopanic` reads it from the argument registers;
  the `panic*` family is the model's runtime error of the stub's kind);
* an instruction that **faults** (`atFault s' e`): a nil dereference or divide becomes a Go panic
  via the signal handler (`runtime.sigpanic`), the classifier gives the runtime error;
* a state where a **deferred/recovered** panic has already left the frame or been turned back into
  a return by the control-flow runtime (`atLeave s'`): the panic/defer contracts
  (`Janus.Contracts.Panic`) supply this and hand control back as another `GoReturns` from the
  resume point (`GoReturns.of_steps`).

* a state where a **`runtime.Goexit`** has run every deferred call of the frame and goes on
  terminating the goroutine (`atExit s'`, outcome `.goexited s'`): the call never returns, and
  no `recover` can stop it.

The classifiers are parameters, supplied by the panic library from the runtime model a theorem
quantifies over; they are part of the printed statement. Existing theorems are unaffected:
`Ensures.toGo` turns every `Ensures` into an `EnsuresGo` whose panic outcomes are impossible, and
`EnsuresGo` (two outcomes) is `EnsuresGoX` (three) with the `Goexit` outcome ruled out. -/

/-- How a Go call ends: it returns in state `s`, a panic with value `v` leaves its frame in
state `s`, or a `runtime.Goexit` leaves its frame in state `s` (the goroutine terminates). -/
inductive GoOutcome where
  | returned (s : State)
  | panicked (v : Eface) (s : State)
  | goexited (s : State)
deriving Inhabited

/-- The instruction at `s.pc` (ordinary code: not the exit, not a stub) stops with fault `e`. -/
def FaultsAt (p : Program) (s : State) (e : Fault) : Prop :=
  s.pc.toNat ≠ p.exitAddr ∧ p.stubAt s.pc.toNat = none ∧
    ∃ w, p.fetch s.pc.toNat = some w ∧ Arm64.step w s = .error e

/-- How a reached state is classified at the Go level: a panic stub (`atStub name s v`), a
faulting instruction delivered as a panic (`atFault s e v`), or a point where a deferred/recovered
panic already left the frame with value `v` (`atLeave s v`), or a point where a
`runtime.Goexit` already left the frame (`atExit s`; `False` unless a classifier says otherwise,
so every classifier written before `Goexit` was modelled keeps its meaning). -/
structure GoClass where
  atStub : String → State → Eface → Prop
  atFault : State → Fault → Eface → Prop
  atLeave : State → Eface → Prop
  atExit : State → Prop := fun _ => False

/-- From `s`, ordinary steps reach a Go-level outcome classified by `C`, and the outcome
satisfies `Q`. -/
def GoReturns (p : Program) (C : GoClass) (s : State) (Q : GoOutcome → Prop) : Prop :=
  ∃ k s', Program.Steps p s k s' ∧
    ((s'.pc.toNat = p.exitAddr ∧ Q (.returned s')) ∨
     (∃ st v, p.stubAt s'.pc.toNat = some st ∧ st.kind = .panic ∧ C.atStub st.name s' v ∧
        Q (.panicked v s')) ∨
     (∃ e v, FaultsAt p s' e ∧ C.atFault s' e v ∧ Q (.panicked v s')) ∨
     (∃ v, C.atLeave s' v ∧ Q (.panicked v s')) ∨
     (C.atExit s' ∧ Q (.goexited s')))

/-- Go function contract with panics: for every admissible return address and every call state
satisfying `pre`, the call either returns (obeying the ABI, with `ret s₀ s₁`) or panics with a
value `v` that leaves its frame in state `s₁` (`pan s₀ v s₁`). The classification `C s₀` may use
the call state. -/
def EnsuresGo (p : Program) (entry : Nat) (args : List W64) (pre : State → Prop)
    (C : State → GoClass) (ret : State → State → Prop) (pan : State → Eface → State → Prop) : Prop :=
  ∀ r, RetAddr p r → ∀ s, CallSetup (p.withExit r) entry args s → pre s →
    GoReturns (p.withExit r) (C s) s fun o =>
      match o with
      | .returned s' => ABIReturn s s' ∧ ret s s'
      | .panicked v s' => pan s v s'
      | .goexited _ => False

/-- `EnsuresGo` with the third outcome: a `runtime.Goexit` that leaves the call's frame in state
`s₁` satisfies `gox s₀ s₁` (the goroutine terminates; the call never returns). -/
def EnsuresGoX (p : Program) (entry : Nat) (args : List W64) (pre : State → Prop)
    (C : State → GoClass) (ret : State → State → Prop) (pan : State → Eface → State → Prop)
    (gox : State → State → Prop) : Prop :=
  ∀ r, RetAddr p r → ∀ s, CallSetup (p.withExit r) entry args s → pre s →
    GoReturns (p.withExit r) (C s) s fun o =>
      match o with
      | .returned s' => ABIReturn s s' ∧ ret s s'
      | .panicked v s' => pan s v s'
      | .goexited s' => gox s s'

section GoLemmas

variable {p : Program} {C : GoClass}

/-- A run that returns is a sequence of ordinary steps to the exit address. -/
theorem steps_of_run_returned : ∀ {n : Nat} {s s' : State}, p.run n s = .ok (.returned s') →
    ∃ k, Program.Steps p s k s' ∧ s'.pc.toNat = p.exitAddr
  | 0, _, _, h => by simp [Program.run] at h
  | n + 1, s, s', h => by
    rw [Program.run_succ] at h
    split at h
    · rename_i hx; cases h; exact ⟨0, .refl _, hx⟩
    · rename_i hx
      split at h
      · cases h
      · rename_i hst
        split at h
        · cases h
        · rename_i w hf
          cases hstep : Arm64.step w s with
          | error e => rw [hstep] at h; cases h
          | ok s₁ =>
            rw [hstep] at h
            obtain ⟨k, hk, he⟩ := steps_of_run_returned h
            exact ⟨k + 1, .step hx hst hf hstep hk, he⟩

/-- A run that reaches a panic stub is ordinary steps to a state at that stub. -/
theorem steps_of_run_stub : ∀ {n : Nat} {s s' : State} {name : String} {k : StubKind},
    p.run n s = .ok (.stub name k s') → ∃ j st, Program.Steps p s j s' ∧
      p.stubAt s'.pc.toNat = some st ∧ st.name = name ∧ st.kind = k
  | 0, _, _, _, _, h => by simp [Program.run] at h
  | n + 1, s, s', name, k, h => by
    rw [Program.run_succ] at h
    split at h
    · cases h
    · rename_i hx
      split at h
      · rename_i st hfind
        cases h; exact ⟨0, st, .refl _, hfind, rfl, rfl⟩
      · rename_i hfind
        split at h
        · cases h
        · rename_i w hf
          cases hstep : Arm64.step w s with
          | error e => rw [hstep] at h; cases h
          | ok s₁ =>
            rw [hstep] at h
            obtain ⟨j, st, hj, hfs, hn, hk⟩ := steps_of_run_stub h
            exact ⟨j + 1, st, .step hx hfind hf hstep hj, hfs, hn, hk⟩

/-- `Returns` gives the return outcome of `GoReturns`. -/
theorem GoReturns.of_returns {s : State} {P : State → Prop} {Q : GoOutcome → Prop}
    (h : Returns p s P) (hq : ∀ s', P s' → Q (.returned s')) : GoReturns p C s Q := by
  obtain ⟨n, s', hr, hp⟩ := h
  obtain ⟨k, hk, he⟩ := steps_of_run_returned hr
  exact ⟨k, s', hk, .inl ⟨he, hq _ hp⟩⟩

/-- Prefix composition: ordinary steps, then a `GoReturns`. -/
theorem GoReturns.of_steps {s s' : State} {k : Nat} {Q : GoOutcome → Prop}
    (h₁ : Program.Steps p s k s') (h₂ : GoReturns p C s' Q) : GoReturns p C s Q := by
  obtain ⟨j, s'', hj, ho⟩ := h₂
  exact ⟨k + j, s'', h₁.trans hj, ho⟩

/-- Reaching the exit address establishes the return outcome. -/
theorem GoReturns.returned {s s' : State} {k : Nat} {Q : GoOutcome → Prop}
    (h : Program.Steps p s k s') (hx : s'.pc.toNat = p.exitAddr) (hq : Q (.returned s')) :
    GoReturns p C s Q := ⟨k, s', h, .inl ⟨hx, hq⟩⟩

/-- Reaching a panic stub establishes the panic outcome. -/
theorem GoReturns.stub {s s' : State} {k : Nat} {st : Stub} {v : Eface} {Q : GoOutcome → Prop}
    (h : Program.Steps p s k s') (hst : p.stubAt s'.pc.toNat = some st) (hk : st.kind = .panic)
    (hc : C.atStub st.name s' v) (hq : Q (.panicked v s')) : GoReturns p C s Q :=
  ⟨k, s', h, .inr (.inl ⟨st, v, hst, hk, hc, hq⟩)⟩

/-- Reaching a faulting instruction establishes the panic outcome (the signal path). -/
theorem GoReturns.fault {s s' : State} {k : Nat} {e : Fault} {v : Eface} {Q : GoOutcome → Prop}
    (h : Program.Steps p s k s') (hf : FaultsAt p s' e) (hc : C.atFault s' e v)
    (hq : Q (.panicked v s')) : GoReturns p C s Q :=
  ⟨k, s', h, .inr (.inr (.inl ⟨e, v, hf, hc, hq⟩))⟩

/-- A deferred/recovered panic that already left the frame establishes the panic outcome. -/
theorem GoReturns.leave {s s' : State} {k : Nat} {v : Eface} {Q : GoOutcome → Prop}
    (h : Program.Steps p s k s') (hc : C.atLeave s' v) (hq : Q (.panicked v s')) :
    GoReturns p C s Q := ⟨k, s', h, .inr (.inr (.inr (.inl ⟨v, hc, hq⟩)))⟩

/-- A `Goexit` that already left the frame establishes the `Goexit` outcome. -/
theorem GoReturns.goexit {s s' : State} {k : Nat} {Q : GoOutcome → Prop}
    (h : Program.Steps p s k s') (hc : C.atExit s') (hq : Q (.goexited s')) :
    GoReturns p C s Q := ⟨k, s', h, .inr (.inr (.inr (.inr ⟨hc, hq⟩)))⟩

theorem GoReturns.mono {s : State} {Q Q' : GoOutcome → Prop} (h : GoReturns p C s Q)
    (hq : ∀ o, Q o → Q' o) : GoReturns p C s Q' := by
  obtain ⟨k, s', hk, h | ⟨st, v, h⟩ | ⟨e, v, h⟩ | ⟨v, h⟩ | h⟩ := h
  · exact ⟨k, s', hk, .inl ⟨h.1, hq _ h.2⟩⟩
  · exact ⟨k, s', hk, .inr (.inl ⟨st, v, h.1, h.2.1, h.2.2.1, hq _ h.2.2.2⟩)⟩
  · exact ⟨k, s', hk, .inr (.inr (.inl ⟨e, v, h.1, h.2.1, hq _ h.2.2⟩))⟩
  · exact ⟨k, s', hk, .inr (.inr (.inr (.inl ⟨v, h.1, hq _ h.2⟩)))⟩
  · exact ⟨k, s', hk, .inr (.inr (.inr (.inr ⟨h.1, hq _ h.2⟩)))⟩

/-- **Compatibility.** Every `Ensures` theorem is an `EnsuresGo` theorem in which the call never
panics, for any classification. -/
theorem Ensures.toGo {entry : Nat} {args : List W64} {pre : State → Prop}
    {post : State → State → Prop} (h : Ensures p entry args pre post) (C : State → GoClass) :
    EnsuresGo p entry args pre C post (fun _ _ _ => False) :=
  fun r hr s hs hp => GoReturns.of_returns (h r hr s hs hp) fun _ h => h

/-- Weaken the outcomes of an `EnsuresGo`. -/
theorem EnsuresGo.mono {entry : Nat} {args : List W64} {pre pre' : State → Prop}
    {Cl : State → GoClass} {ret ret' : State → State → Prop} {pan pan' : State → Eface → State → Prop}
    (h : EnsuresGo p entry args pre Cl ret pan) (hpre : ∀ s, pre' s → pre s)
    (hret : ∀ s s', pre' s → ret s s' → ret' s s') (hpan : ∀ s v s', pre' s → pan s v s' → pan' s v s') :
    EnsuresGo p entry args pre' Cl ret' pan' := by
  intro r hr s hs hp
  refine (h r hr s hs (hpre s hp)).mono fun o ho => ?_
  cases o with
  | returned s' => exact ⟨ho.1, hret _ _ hp ho.2⟩
  | panicked v s' => exact hpan _ _ _ hp ho
  | goexited s' => exact ho

/-- An `EnsuresGo` theorem is an `EnsuresGoX` theorem whose `Goexit` outcome is impossible. -/
theorem EnsuresGo.toX {entry : Nat} {args : List W64} {pre : State → Prop} {Cl : State → GoClass}
    {ret : State → State → Prop} {pan : State → Eface → State → Prop}
    (h : EnsuresGo p entry args pre Cl ret pan) :
    EnsuresGoX p entry args pre Cl ret pan (fun _ _ => False) := by
  intro r hr s hs hp
  refine (h r hr s hs hp).mono fun o ho => ?_
  cases o <;> exact ho

/-- Every `Ensures` theorem is an `EnsuresGoX` theorem that neither panics nor exits. -/
theorem Ensures.toGoX {entry : Nat} {args : List W64} {pre : State → Prop}
    {post : State → State → Prop} (h : Ensures p entry args pre post) (C : State → GoClass) :
    EnsuresGoX p entry args pre C post (fun _ _ _ => False) (fun _ _ => False) :=
  (Ensures.toGo h C).toX

/-- Weaken the outcomes of an `EnsuresGoX`. -/
theorem EnsuresGoX.mono {entry : Nat} {args : List W64} {pre pre' : State → Prop}
    {Cl : State → GoClass} {ret ret' : State → State → Prop} {pan pan' : State → Eface → State → Prop}
    {gox gox' : State → State → Prop}
    (h : EnsuresGoX p entry args pre Cl ret pan gox) (hpre : ∀ s, pre' s → pre s)
    (hret : ∀ s s', pre' s → ret s s' → ret' s s') (hpan : ∀ s v s', pre' s → pan s v s' → pan' s v s')
    (hgox : ∀ s s', pre' s → gox s s' → gox' s s') :
    EnsuresGoX p entry args pre' Cl ret' pan' gox' := by
  intro r hr s hs hp
  refine (h r hr s hs (hpre s hp)).mono fun o ho => ?_
  cases o with
  | returned s' => exact ⟨ho.1, hret _ _ hp ho.2⟩
  | panicked v s' => exact hpan _ _ _ hp ho
  | goexited s' => exact hgox _ _ hp ho

end GoLemmas

end GoABI
end Janus
