import Janus.Run
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

/-- `s` is a state in which `entry` has just been called with integer register
arguments `args`, returning to `p.exitAddr`. Everything else (other registers, flags, SP,
memory) is arbitrary; specifications quantify over all such states. -/
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
  noWrap : (s.regs regG).toNat + stackguard0Offset + 8 ≤ 2 ^ 64
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

/-! ## Specifications (total correctness with finite fuel) -/

/-- The call returns (reaches `p.exitAddr`) after finitely many steps, in a state
satisfying `post`. -/
def Returns (p : Program) (s : State) (post : State → Prop) : Prop :=
  ∃ fuel s', p.run fuel s = .ok (.returned s') ∧ post s'

/-- Execution reaches a Go panic stub. -/
def Panics (p : Program) (s : State) : Prop :=
  ∃ fuel name s', p.run fuel s = .ok (.stub name .panic s')

/-- Execution never reaches a Go panic stub, for any fuel. -/
def NeverPanics (p : Program) (s : State) : Prop :=
  ∀ fuel name s', p.run fuel s ≠ .ok (.stub name .panic s')

/-- Execution reaches `runtime.morestack*`. -/
def GrowsStack (p : Program) (s : State) : Prop :=
  ∃ fuel name s', p.run fuel s = .ok (.stub name .morestack s')

/-- Go function contract: from **every** call state with these arguments satisfying `pre`,
the call returns, obeys the ABI return rules, and satisfies `post s₀ s₁`. -/
def Ensures (p : Program) (entry : Nat) (args : List W64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ s, CallSetup p entry args s → pre s → Returns p s (fun s' => ABIReturn s s' ∧ post s s')

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
  intro m name s'' hm
  cases Program.run_ok_unique hr hm

theorem Returns.not_panics {P : State → Prop} (h : Returns p s P) : ¬ Panics p s := by
  rintro ⟨m, name, s'', hm⟩; exact h.neverPanics m name s'' hm

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
  intro n name s'' hr
  exact h (k + n) name s'' (by rw [Program.run_steps hs, hr])

/-! ### `Ensures` -/

theorem Ensures.returns {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures p entry args pre post) (hs : CallSetup p entry args s) (hpre : pre s) :
    Returns p s (fun s' => ABIReturn s s' ∧ post s s') := h s hs hpre

theorem Ensures.neverPanics {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures p entry args pre post) (hs : CallSetup p entry args s) (hpre : pre s) :
    NeverPanics p s := (h s hs hpre).neverPanics

theorem Ensures.mono {pre pre' : State → Prop} {post post' : State → State → Prop}
    (h : Ensures p entry args pre post) (hpre : ∀ s, pre' s → pre s)
    (hpost : ∀ s s', pre' s → post s s' → post' s s') : Ensures p entry args pre' post' :=
  fun s hs hp => (h s hs (hpre s hp)).mono fun _ ⟨ha, hq⟩ => ⟨ha, hpost _ _ hp hq⟩

end Lemmas

end GoABI
end Janus
