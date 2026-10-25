import Janus.Amd64.Run
import Janus.Eface
import Janus.Arm64.MemoryLemmas

/-!
# Go ABIInternal on amd64, and the specification vocabulary

Source of truth: `$GOROOT/src/cmd/compile/abi-internal.md`, section "amd64 architecture"
(checked against Go 1.26.0).

| Register | At call | At return | In body |
| --- | --- | --- | --- |
| `RAX RBX RCX RDI RSI R8 R9 R10 R11` | integer arguments 1–9 | integer results 1–9 | scratch |
| `RDX` | closure context pointer | scratch | scratch |
| `R12`, `R13`, `R15` | scratch | scratch | scratch |
| `R14` | current goroutine `g` | same | same |
| `RBP` | frame pointer | same | same |
| `RSP` | stack pointer (8-byte aligned), `[RSP]` = return address | `RSP + 8` | |
| `X15` | zero | zero | scratch |
| `X0`–`X14` | floating-point arguments/results (stated by preconditions on `State.xmm`; `CallSetup` has no float arguments) | | scratch |

There are no other callee-saved registers; the status flags are scratch and the direction
flag is clear at calls (no modelled instruction depends on it). `CALL` pushes the return
address, so at entry `[RSP]` holds it and the caller's argument area (stack-assigned arguments,
then results, then spill slots for the register arguments) starts at `8(RSP)`. A function
returns with `RET`, which pops the return address: on return `RSP` is the entry value plus 8.

## Stack-growth prologue (Go 1.26)

Functions that are not `NOSPLIT` start with one of

```
CMPQ SP, 16(R14) ; JLS morestack                                   // frame ≤ StackSmall (128)
LEAQ -k(SP), R12 ; CMPQ R12, 16(R14) ; JLS morestack               // medium frame
MOVQ SP, R12 ; SUBQ $k, R12 ; JCS morestack ; CMPQ R12, 16(R14) ; JLS morestack   // big frame
```

with `k = framesize - StackSmall`. `StackGuardOK s k` (`g.stackguard0` readable, and
`stackguard0 + k < RSP`) makes every form fall through, and also excludes a pending
preemption request (`stackguard0 = stackPreempt`, a huge value).
-/

namespace Janus.Amd64

namespace GoABI

/-! ## Register roles -/

/-- The integer argument / result registers, in order: `RAX RBX RCX RDI RSI R8 R9 R10 R11`. -/
def intArgRegs : List Nat := [0, 3, 1, 7, 6, 8, 9, 10, 11]

def numIntRegs : Nat := 9

/-- The `i`-th integer argument / result register. -/
def argReg (i : Nat) : Nat := intArgRegs.getD i 0

abbrev regSP : Nat := 4
abbrev regFP : Nat := 5
/-- Closure context pointer at calls (`RDX`). -/
abbrev regClosure : Nat := 2
/-- The current goroutine `g` (`R14`). -/
abbrev regG : Nat := 14
/-- The fixed zero SSE register `X15`. -/
abbrev xmmZero : Nat := 15

/-- Offset of the first stack-assigned argument from `RSP` at entry (above the return PC). -/
def stackArgOffset : Nat := 8
def stackSmall : Nat := 128
def stackBig : Nat := 4096
/-- Offset of `stackguard0` in `runtime.g` (after `stack.lo`, `stack.hi`). -/
def stackguard0Offset : Nat := 16

def prologueAdj (frameSize : Nat) : Nat := frameSize - stackSmall

/-! ## Calls -/

/-- `ret` is an admissible return address for a call into `p` from outside the extracted code:
a canonical user address (below `2^47`, as every amd64 user-mode `RIP` is), not inside any
extracted code segment and not a stub address. A real caller's return address is the
instruction after its `CALL`, in the caller's own code. Specifications quantify over **every**
such `ret` and run `p.withExit ret`, so a branch to a fixed address (such as `p.exitAddr`, or a
zero code pointer loaded from memory) cannot count as a return. -/
structure RetAddr (p : Program) (ret : Nat) : Prop where
  user : ret < 2 ^ 47
  notCode : ∀ seg ∈ p.segments, ret < seg.base ∨ seg.base + seg.bytes.length ≤ ret
  notStub : ∀ st ∈ p.stubs, st.addr ≠ ret

/-- `s` is a state in which `entry` has just been called (by `CALL`) with integer register
arguments `args`, returning to `p.exitAddr`: `RIP = entry`, the return address `p.exitAddr`
is stored at `[RSP]`, `X15 = 0`, the direction flag is clear, and argument `i` is in
`argReg i`. Everything else (other
registers, flags, other memory, and which regions exist) is arbitrary; specifications
quantify over all such states and state the regions they need in their precondition. They use
it with `p.withExit ret` for a universally quantified admissible `ret` (`RetAddr`), never with
the extracted placeholder `p.exitAddr`. -/
structure CallSetup (p : Program) (entry : Nat) (args : List W64) (s : State) : Prop where
  rip : s.rip = BitVec.ofNat 64 entry
  ret : s.mem.readLE (s.regs regSP).toNat 8 = p.exitAddr
  zero : s.xmm xmmZero = 0
  len : args.length ≤ numIntRegs
  args : ∀ i (h : i < args.length), s.regs (argReg i) = args[i]
  /-- The direction flag is clear at every call (ABIInternal: "The direction flag (D) is
  always cleared (set to the forward direction) at a call"). -/
  df : s.df = false

abbrev GoCall := CallSetup

/-- `MXCSR` as Go's ABIInternal fixes it at every call (`abi-internal.md`, "amd64
architecture"): the control bits 15:6 (`FTZ`, `RC`, the six exception masks, `DAZ`) are those
of `0x1F80` (round to nearest even, every exception masked, no flushing) and the reserved bits
31:16 are zero, while the six status flags (bits 5:0, `IE DE ZE OE UE PE`) are **arbitrary**.
The flags are sticky and Go code never clears them: in a running Go program `PE` is already set
when `main` starts (`MXCSR = 0x1FA0`; the runtime's own floating point is inexact), so a
precondition `s.mxcsr = 0x1F80` would exclude practically every real call
(`docs/AUDIT-FP.md`, X64-MXCSR-STICKY). Floating-point theorems state this instead. -/
def GoMXCSR (s : State) : Prop := s.mxcsr.toNat / 64 = 0x1F80 / 64

/-- The first `k` integer result registers. -/
def results (k : Nat) (s : State) : List W64 := (intArgRegs.take k).map s.regs

/-- A 64-bit word at `off` bytes above the stack pointer. -/
def stackWord (s : State) (off : Nat) : W64 :=
  BitVec.ofNat 64 (s.mem.readLE ((s.regs regSP).toNat + off) 8)

/-- Stack-assigned 64-bit arguments (or results) starting at `8(RSP)`, plus `skip` bytes. -/
def StackWords (s : State) (skip : Nat) (words : List W64) : Prop :=
  ∀ i (h : i < words.length),
    s.mem.readLE ((s.regs regSP).toNat + stackArgOffset + skip + 8 * i) 8 = words[i].toNat

def ClosureCtx (s : State) (ctx : W64) : Prop := s.regs regClosure = ctx

/-- `RSP` is 8-byte aligned (as at every Go call). -/
def SPAligned (s : State) : Prop := (s.regs regSP).toNat % 8 = 0

/-- The caller owns writable stack from `below` bytes under `RSP` to `above` bytes over it
(the callee's frame below; the return address and the argument/result/spill area above, so
`above ≥ 8` for the `RET` to read the return address), below `2^48`. -/
def StackWritable (s : State) (below above : Nat) : Prop :=
  below ≤ (s.regs regSP).toNat ∧ (s.regs regSP).toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs regSP).toNat - below) (below + above) true = true

/-- `n` bytes at pointer `ptr` are readable (`w = false`) or writable (`w = true`, with no
read-only region overlapping them) and lie below `2^48` (implied by `accessible`; stated so that
destructuring gives `omega` the no-wrap fact). -/
def Buffer (s : State) (ptr : W64) (n : Nat) (w : Bool) : Prop :=
  ptr.toNat + n ≤ 2 ^ 48 ∧ s.mem.accessible ptr.toNat n w = true

/-- The byte ranges `[a, a + n)` and `[b, b + k)` do not overlap. -/
def Disjoint (a : W64) (n : Nat) (b : W64) (k : Nat) : Prop :=
  a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat

/-- The little-endian value of the `n` bytes at `ptr`. -/
def valueAt (s : State) (ptr : W64) (n : Nat) : Nat := s.mem.readLE ptr.toNat n

/-- `g.stackguard0` as read by `CMPQ SP, 16(R14)`. -/
def stackguard0 (s : State) : Nat := s.mem.readLE ((s.regs regG).toNat + stackguard0Offset) 8

structure StackGuardOK (s : State) (adj : Nat) : Prop where
  noWrap : (s.regs regG).toNat + stackguard0Offset + 8 ≤ 2 ^ 48
  readable : s.mem.accessible ((s.regs regG).toNat + stackguard0Offset) 8 false = true
  below : stackguard0 s + adj < (s.regs regSP).toNat

/-- Thread-local storage: Go keeps the current goroutine's `g` pointer in the slot at `FS:-8`
(`runtime.tlsg`: ABI wrappers and assembly reload `R14` with `MOVQ FS:-8, R14`). `TlsG s` says
that slot (the 8 bytes at `fsBase - 8`) is readable, lies below `2^48` and holds `R14`. The
`FS` base is an ordinary state field (`State.fsBase`) that specifications quantify over; the
slot is ordinary memory, so a precondition grants it like any other region. -/
structure TlsG (s : State) : Prop where
  base : 8 ≤ s.fsBase.toNat ∧ s.fsBase.toNat ≤ 2 ^ 48
  readable : s.mem.accessible (s.fsBase.toNat - 8) 8 false = true
  g : s.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs regG).toNat

/-- The address `FS:-8` (`fsBase + sext(-8)`, as the decoder produces it) is `fsBase - 8`. -/
theorem TlsG.addr {s : State} (h : TlsG s) :
    (s.fsBase + BitVec.ofNat 64 18446744073709551608).toNat = s.fsBase.toNat - 8 := by
  have := h.base
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Under `TlsG`, the TLS load `MOVQ FS:-8, r` reads `g`. -/
theorem TlsG.load {s : State} (h : TlsG s) :
    Janus.Amd64.load s.mem (s.fsBase + BitVec.ofNat 64 18446744073709551608).toNat 8 =
      .ok (s.regs regG).toNat := by
  rw [h.addr]; unfold Janus.Amd64.load; rw [h.readable]; simp [h.g]

/-! ## Obligations on return -/

/-- What every Go function must restore on return, relative to its call state `s₀`: `RSP`
(popped past the return address), the frame pointer `RBP`, `g` (`R14`) and `X15`. -/
structure ABIReturn (s₀ s₁ : State) : Prop where
  sp : s₁.regs regSP = s₀.regs regSP + 8
  fp : s₁.regs regFP = s₀.regs regFP
  g : s₁.regs regG = s₀.regs regG
  zero : s₁.xmm xmmZero = s₀.xmm xmmZero

/-! ## Specifications (total correctness with finite fuel)

As on arm64 (`Janus.GoABI`): for a call the predicates are applied to `p.withExit ret` with `ret`
universally quantified (`Ensures` does this itself), and a fault (nil or out-of-bounds access,
read-only store, jump outside the code, `#DE`, undefined flag, unsupported instruction) is a
crash or a Go panic on hardware (`SIGSEGV`/`SIGFPE` become `runtime.sigpanic`), so it is never
success: `Returns` excludes it and `NeverPanics` counts it as a panic. -/

/-- The call returns (reaches `p.exitAddr`) in a state satisfying `post`. Excludes faults,
panics, stack growth and non-termination. -/
def Returns (p : Program) (s : State) (post : State → Prop) : Prop :=
  ∃ fuel s', p.run fuel s = .ok (.returned s') ∧ post s'

/-- Execution reaches a Go panic stub. A nil dereference or a hardware divide error is a fault
instead: see `Faults`. -/
def Panics (p : Program) (s : State) : Prop :=
  ∃ fuel name s', p.run fuel s = .ok (.stub name .panic s')

/-- Execution stops with a fault other than running out of fuel. -/
def Faults (p : Program) (s : State) : Prop :=
  ∃ fuel e, p.run fuel s = .error e ∧ e ≠ .outOfFuel

/-- Execution never faults and never reaches a Go panic stub, for any fuel (it may return,
reach `morestack`, or run forever). -/
def NeverPanics (p : Program) (s : State) : Prop :=
  ∀ fuel, (∀ name s', p.run fuel s ≠ .ok (.stub name .panic s')) ∧
    (∀ e, p.run fuel s = .error e → e = .outOfFuel)

def GrowsStack (p : Program) (s : State) : Prop :=
  ∃ fuel name s', p.run fuel s = .ok (.stub name .morestack s')

/-- Go function contract: for **every** admissible return address `ret` (`RetAddr`) and
**every** call state with these arguments and `[RSP] = ret` satisfying `pre`, the call returns
to `ret` (never faults or panics), obeys the ABI return rules, and satisfies `post s₀ s₁`. -/
def Ensures (p : Program) (entry : Nat) (args : List W64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ ret, RetAddr p ret → ∀ s, CallSetup (p.withExit ret) entry args s → pre s →
    Returns (p.withExit ret) s (fun s' => ABIReturn s s' ∧ post s s')

def EnsuresResults (p : Program) (entry : Nat) (args : List W64) (nres : Nat)
    (pre : State → Prop) (post : List W64 → Prop) : Prop :=
  Ensures p entry args pre (fun _ s' => post (results nres s'))

/-! ## Lemmas -/

section Lemmas

variable {p : Program} {s s' : State} {entry : Nat} {args : List W64}

theorem CallSetup.rip_toNat (h : CallSetup p entry args s) (he : entry < 2 ^ 64) :
    s.rip.toNat = entry := by
  rw [h.rip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]

theorem CallSetup.reg (h : CallSetup p entry args s) {i : Nat} (hi : i < args.length) :
    s.regs (argReg i) = args[i] := h.args i hi

@[simp] theorem results_length (k : Nat) (h : k ≤ numIntRegs) : (results k s).length = k := by
  simp only [results, List.length_map, List.length_take, intArgRegs, numIntRegs] at *
  simp; omega

theorem results_one : results 1 s = [s.regs 0] := rfl
theorem results_two : results 2 s = [s.regs 0, s.regs 3] := rfl
theorem results_three : results 3 s = [s.regs 0, s.regs 3, s.regs 1] := rfl

theorem StackGuardOK.adj_le {adj : Nat} (h : StackGuardOK s adj) : adj ≤ (s.regs regSP).toNat := by
  have := h.below; omega

theorem StackGuardOK.lt_sub {adj : Nat} (h : StackGuardOK s adj) :
    stackguard0 s < (s.regs regSP).toNat - adj := by
  have := h.below; omega

theorem StackGuardOK.addr_toNat {adj : Nat} (h : StackGuardOK s adj) :
    (s.regs regG + BitVec.ofNat 64 stackguard0Offset).toNat =
      (s.regs regG).toNat + stackguard0Offset := by
  have := h.noWrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [stackguard0Offset] at *
  omega

theorem StackGuardOK.load {adj : Nat} (h : StackGuardOK s adj) :
    Amd64.load s.mem ((s.regs regG).toNat + stackguard0Offset) 8 = .ok (stackguard0 s) := by
  simp [Amd64.load, h.readable, stackguard0]

theorem stackguard0_lt : stackguard0 s < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ 8

theorem StackGuardOK.mono {adj adj' : Nat} (h : StackGuardOK s adj) (hle : adj' ≤ adj) :
    StackGuardOK s adj' :=
  ⟨h.noWrap, h.readable, by have := h.below; omega⟩

/-! ### Read-only data -/

/-- A loaded data segment is readable. -/
theorem DataLoaded.accessible {m : Memory} (h : p.DataLoaded m) {d : Janus.DataSegment}
    (hd : d ∈ p.data) : m.accessible d.base d.bytes.length false = true := by
  have h1 := (h d hd).1
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨r, hr, ⟨⟨⟨h2, h3⟩, h4⟩, _⟩⟩ := h1
  exact Janus.Arm64.Memory.accessible_of_mem m hr h2 h3 h4

/-- The bytes of a loaded data segment. -/
theorem DataLoaded.byte {m : Memory} (h : p.DataLoaded m) {d : Janus.DataSegment}
    (hd : d ∈ p.data) (i : Nat) (hi : i < d.bytes.length) :
    m.readLE (d.base + i) 1 = d.bytes[i] := by
  rw [Janus.Arm64.Memory.readLE_one]; exact (h d hd).2 i hi

/-- Little-endian value of the first `n` bytes of a byte list (`0` past its end). -/
def listLE : List Nat → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | b :: bs, n + 1 => b + 256 * listLE bs n

/-- `n` bytes read inside a loaded data segment are the copied bytes; on a concrete segment
the right-hand side evaluates by `decide`. -/
theorem DataLoaded.readLE {m : Memory} (h : p.DataLoaded m) {d : Janus.DataSegment}
    (hd : d ∈ p.data) (off n : Nat) (hn : off + n ≤ d.bytes.length) :
    m.readLE (d.base + off) n = listLE (d.bytes.drop off) n := by
  induction n generalizing off with
  | zero => cases d.bytes.drop off <;> rfl
  | succ n ih =>
    have hoff : off < d.bytes.length := by omega
    rw [Janus.Arm64.Memory.readLE_succ, List.drop_eq_getElem_cons hoff, listLE,
      ← DataLoaded.byte h hd off hoff, Janus.Arm64.Memory.readLE_one,
      show d.base + off + 1 = d.base + (off + 1) by omega, ih (off + 1) (by omega)]

/-! ### `Returns` / `Panics` -/

theorem Returns.mono {P Q : State → Prop} (h : Returns p s P) (hPQ : ∀ s', P s' → Q s') :
    Returns p s Q := by
  obtain ⟨n, s', hr, hp⟩ := h; exact ⟨n, s', hr, hPQ _ hp⟩

theorem Returns.unique {P Q : State → Prop} (hP : Returns p s P) (hQ : Returns p s Q) :
    Returns p s (fun s' => P s' ∧ Q s') := by
  obtain ⟨n, s₁, h₁, hp⟩ := hP
  obtain ⟨m, s₂, h₂, hq⟩ := hQ
  have := Program.run_ok_unique h₁ h₂
  cases this
  exact ⟨n, s₁, h₁, hp, hq⟩

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

theorem Returns.not_growsStack {P : State → Prop} (h : Returns p s P) : ¬ GrowsStack p s := by
  obtain ⟨n, s', hr, _⟩ := h
  rintro ⟨m, name, s'', hm⟩
  cases Program.run_ok_unique hr hm

theorem Panics.not_returns {P : State → Prop} (h : Panics p s) : ¬ Returns p s P :=
  fun hr => hr.not_panics h

theorem Returns.of_steps {k : Nat} {P : State → Prop} (hs : Program.Steps p s k s')
    (h : Returns p s' P) : Returns p s P := by
  obtain ⟨n, s'', hr, hp⟩ := h
  exact ⟨k + n, s'', by rw [Program.run_steps hs, hr], hp⟩

theorem returns_of_steps {k : Nat} {P : State → Prop} (hs : Program.Steps p s k s')
    (hx : s'.rip.toNat = p.exitAddr) (hp : P s') : Returns p s P :=
  ⟨k + 1, s', Program.run_steps_exit hs hx, hp⟩

theorem panics_of_steps {k : Nat} {st : Janus.Stub} (hs : Program.Steps p s k s')
    (hx : s'.rip.toNat ≠ p.exitAddr) (hst : p.stubAt s'.rip.toNat = some st)
    (hk : st.kind = .panic) : Panics p s :=
  ⟨k + 1, st.name, s', by rw [Program.run_steps_stub hs hx hst, hk]⟩

theorem NeverPanics.of_steps {k : Nat} (hs : Program.Steps p s k s') (h : NeverPanics p s) :
    NeverPanics p s' := by
  intro n
  have := h (k + n)
  rw [Program.run_steps hs] at this
  exact this

theorem Faults.of_steps {k : Nat} (hs : Program.Steps p s k s') (h : Faults p s') :
    Faults p s := by
  obtain ⟨n, e, hr, he⟩ := h
  exact ⟨k + n, e, by rw [Program.run_steps hs, hr], he⟩

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

theorem RetAddr.fetch_none {ret : Nat} (h : RetAddr p ret) : p.fetch ret = none :=
  Program.fetchIn_eq_none h.notCode

theorem RetAddr.stubAt_none {ret : Nat} (h : RetAddr p ret) : p.stubAt ret = none :=
  Program.stubAt_eq_none (p := p) h.notStub

theorem RetAddr.lt64 {ret : Nat} (h : RetAddr p ret) : ret < 2 ^ 64 := by
  have := h.user; omega

theorem RetAddr.ne_of_fetch {ret pc : Nat} {w : List Nat} (h : RetAddr p ret)
    (hf : p.fetch pc = some w) : pc ≠ ret := by
  rintro rfl; rw [h.fetch_none] at hf; cases hf

theorem RetAddr.ne_of_stubAt {ret pc : Nat} {st : Janus.Stub} (h : RetAddr p ret)
    (hs : p.stubAt pc = some st) : pc ≠ ret := by
  rintro rfl; rw [h.stubAt_none] at hs; cases hs

/-- Decide `RetAddr` on a concrete program. -/
def retAddrCheck (p : Program) (ret : Nat) : Bool :=
  decide (ret < 2 ^ 47) &&
    p.segments.all (fun seg => decide (ret < seg.base ∨ seg.base + seg.bytes.length ≤ ret)) &&
    p.stubs.all (fun st => st.addr != ret)

theorem RetAddr.of_check {ret : Nat} (h : retAddrCheck p ret = true) : RetAddr p ret := by
  simp only [retAddrCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

end Lemmas

/-! ## Go-level outcomes (amd64)

The amd64 counterpart of `Janus.GoABI` (see there for the full account).

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

The classifiers are parameters, supplied by the panic library from the runtime model a theorem
quantifies over; they are part of the printed statement. Existing theorems are unaffected:
`Ensures.toGo` turns every `Ensures` into an `EnsuresGo` whose panic outcomes are impossible. -/

/-- How a Go call ends: it returns in state `s`, or a panic with value `v` leaves its frame in
state `s`. -/
inductive GoOutcome where
  | returned (s : State)
  | panicked (v : Eface) (s : State)
deriving Inhabited

/-- The instruction at `s.pc` (ordinary code: not the exit, not a stub) stops with fault `e`. -/
def FaultsAt (p : Program) (s : State) (e : Fault) : Prop :=
  s.rip.toNat ≠ p.exitAddr ∧ p.stubAt s.rip.toNat = none ∧
    ∃ w : List Nat, p.fetch s.rip.toNat = some w ∧ Amd64.step w s = .error e

/-- How a reached state is classified at the Go level: a panic stub (`atStub name s v`), a
faulting instruction delivered as a panic (`atFault s e v`), or a point where a deferred/recovered
panic already left the frame with value `v` (`atLeave s v`). -/
structure GoClass where
  atStub : String → State → Eface → Prop
  atFault : State → Fault → Eface → Prop
  atLeave : State → Eface → Prop

/-- From `s`, ordinary steps reach a Go-level outcome classified by `C`, and the outcome
satisfies `Q`. -/
def GoReturns (p : Program) (C : GoClass) (s : State) (Q : GoOutcome → Prop) : Prop :=
  ∃ k s', Program.Steps p s k s' ∧
    ((s'.rip.toNat = p.exitAddr ∧ Q (.returned s')) ∨
     (∃ st v, p.stubAt s'.rip.toNat = some st ∧ st.kind = .panic ∧ C.atStub st.name s' v ∧
        Q (.panicked v s')) ∨
     (∃ e v, FaultsAt p s' e ∧ C.atFault s' e v ∧ Q (.panicked v s')) ∨
     (∃ v, C.atLeave s' v ∧ Q (.panicked v s')))

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

section GoLemmas

variable {p : Program} {C : GoClass}

/-- A run that returns is a sequence of ordinary steps to the exit address. -/
theorem steps_of_run_returned : ∀ {n : Nat} {s s' : State}, p.run n s = .ok (.returned s') →
    ∃ k, Program.Steps p s k s' ∧ s'.rip.toNat = p.exitAddr
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
          cases hstep : Amd64.step w s with
          | error e => rw [hstep] at h; cases h
          | ok s₁ =>
            rw [hstep] at h
            obtain ⟨k, hk, he⟩ := steps_of_run_returned h
            exact ⟨k + 1, .step hx hst hf hstep hk, he⟩

/-- A run that reaches a panic stub is ordinary steps to a state at that stub. -/
theorem steps_of_run_stub : ∀ {n : Nat} {s s' : State} {name : String} {k : StubKind},
    p.run n s = .ok (.stub name k s') → ∃ j st, Program.Steps p s j s' ∧
      p.stubAt s'.rip.toNat = some st ∧ st.name = name ∧ st.kind = k
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
          cases hstep : Amd64.step w s with
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
    (h : Program.Steps p s k s') (hx : s'.rip.toNat = p.exitAddr) (hq : Q (.returned s')) :
    GoReturns p C s Q := ⟨k, s', h, .inl ⟨hx, hq⟩⟩

/-- Reaching a panic stub establishes the panic outcome. -/
theorem GoReturns.stub {s s' : State} {k : Nat} {st : Stub} {v : Eface} {Q : GoOutcome → Prop}
    (h : Program.Steps p s k s') (hst : p.stubAt s'.rip.toNat = some st) (hk : st.kind = .panic)
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
    GoReturns p C s Q := ⟨k, s', h, .inr (.inr (.inr ⟨v, hc, hq⟩))⟩

theorem GoReturns.mono {s : State} {Q Q' : GoOutcome → Prop} (h : GoReturns p C s Q)
    (hq : ∀ o, Q o → Q' o) : GoReturns p C s Q' := by
  obtain ⟨k, s', hk, h | ⟨st, v, h⟩ | ⟨e, v, h⟩ | ⟨v, h⟩⟩ := h
  · exact ⟨k, s', hk, .inl ⟨h.1, hq _ h.2⟩⟩
  · exact ⟨k, s', hk, .inr (.inl ⟨st, v, h.1, h.2.1, h.2.2.1, hq _ h.2.2.2⟩)⟩
  · exact ⟨k, s', hk, .inr (.inr (.inl ⟨e, v, h.1, h.2.1, hq _ h.2.2⟩))⟩
  · exact ⟨k, s', hk, .inr (.inr (.inr ⟨v, h.1, hq _ h.2⟩))⟩

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

end GoLemmas

end GoABI
end Janus.Amd64
