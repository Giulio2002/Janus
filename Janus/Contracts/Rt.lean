import Janus.Contracts.AllocAmd64

/-!
# Runtime contracts from ISA-independent specifications

The allocation contracts (`Janus.Contracts.Alloc`) spell out each function's precondition and
postcondition per ISA. The string, slice and write-barrier contracts (`Janus.Contracts.String`,
`Janus.Contracts.Slice`, `Janus.Contracts.WriteBarrier`) are many more functions with the same
call shape, so they are stated once, ISA-independently, as an `RtSpec`: what the function needs
and does in terms of its **argument words** (the Go ABIInternal integer arguments in order, as
numbers) and memory. `RtContract` (arm64) and `RtContract64` (amd64) turn an `RtSpec` into a
`Summary` hypothesis with the ISA's calling convention:

* **arguments**: arm64 `X0, X1, …` (`argWords`); amd64 `RAX, RBX, RCX, RDI, RSI, R8, R9, R10,
  R11` and, past the ninth word, the stack words at `[RSP + 8, …)` (`argWords64`; Go passes an
  argument that no longer fits in registers on the stack, e.g. the last string of
  `concatstring5`);
* **the call** (`CallOK`/`CallOK64`): an admissible return address, an aligned stack pointer and
  the stack window `[SP - stack, SP + 8 + 8·nargs)` writable, the memory the function reads (the
  spec's `reads`) outside the callee's part of it; when the spec asks for it, the
  stack guard of `g` below `SP - adj` and outside the callee's window (`GuardOK`: the function's
  own stack check falls through, so it neither grows nor moves the stack);
* **readiness** (round 9 C1): when the spec allocates or otherwise depends on the runtime's own
  state, `Ready H rt args s` for the caller-quantified `H : RtReady`;
* **the return**: to the return address, with `SP`, `g`, the frame pointer (and on arm64 `R18`)
  preserved, results `r₀, r₁, r₂` in the first three result registers (`X0–X2`; `RAX, RBX,
  RCX`), every other register, the flags and the vector registers unspecified (on arm64 also
  the exclusive monitor and the store-exclusive outcomes, `retStateX`; on amd64 the AVX-512
  state);
* **memory**: changed only inside the runtime-owned ranges `rt` (unless the spec says the function
  writes none, `rtWrites = false`), the callee's stack window and the spec's `writes args` (e.g.
  a caller's `tmpBuf`), regions unchanged, and the spec's `post` relates the old memory, the
  results and the new memory.
-/

namespace Janus.Contracts

/-- An ISA-independent runtime contract: see the module documentation. -/
structure RtSpec where
  /-- The number of argument words (also the spill area the callee may write). -/
  nargs : Nat
  /-- The precondition on the argument words and the memory. -/
  pre : List Nat → Janus.Arm64.Memory → Prop
  /-- The ranges the function may write besides `rt` and its stack window (from the argument
  words and the memory at the call). -/
  writes : List Nat → Janus.Arm64.Memory → List (Nat × Nat) := fun _ _ => []
  /-- The memory the function reads (`(address, length)` pairs from the argument words and the
  memory at the call): it must lie outside the callee's stack window, which the function writes
  before it reads its inputs. -/
  reads : List Nat → Janus.Arm64.Memory → List (Nat × Nat) := fun _ _ => []
  /-- `some adj`: the function's stack check must fall through (`stackguard0 + adj < SP`). -/
  guard : Option Nat := none
  /-- Whether the precondition includes the runtime's readiness `H` (round 9 C1). -/
  ready : Bool := true
  /-- Whether the function may write the runtime-owned ranges `rt` (`false`: only its stack window
  and `writes`, e.g. `decoderune`). -/
  rtWrites : Bool := true
  /-- The postcondition: the runtime-owned ranges, the argument words, the old memory, the three
  result words and the new memory. -/
  post : List (Nat × Nat) → List Nat → Janus.Arm64.Memory → Nat → Nat → Nat → Janus.Arm64.Memory → Prop

/-- The runtime-owned ranges a function may write: `rt`, or none. -/
def rtIf (b : Bool) (rt : List (Nat × Nat)) : List (Nat × Nat) := if b then rt else []

@[janus_exec, janus_post, janus64_exec, janus64_post] theorem rtIf_true (rt : List (Nat × Nat)) :
    rtIf true rt = rt := rfl
@[janus_exec, janus_post, janus64_exec, janus64_post] theorem rtIf_false (rt : List (Nat × Nat)) :
    rtIf false rt = [] := rfl

/-- `n` words from `f i` for `i = k, k+1, …` (a cons list, so that literal indices reduce). -/
def wordsFrom (f : Nat → Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | k, n + 1 => f k :: wordsFrom f (k + 1) n

@[janus_exec, janus_post, janus64_exec, janus64_post] theorem wordsFrom_zero (f : Nat → Nat) (k : Nat) :
    wordsFrom f k 0 = [] := rfl
@[janus_exec, janus_post, janus64_exec, janus64_post] theorem wordsFrom_succ (f : Nat → Nat) (k n : Nat) :
    wordsFrom f k (n + 1) = f k :: wordsFrom f (k + 1) n := rfl

section Arm64

open Janus Janus.Arm64 Janus.Tactic

/-- The argument words of an arm64 call: `X0, X1, …`. -/
def argWords (s : State) (n : Nat) : List Nat := wordsFrom (fun i => (s.regs i).toNat) 0 n

attribute [janus_exec, janus_post] argWords

/-- Every range of `rs` (what a runtime function reads) lies outside the callee's stack window
`win`. A definition of its own, unfolded one element at a time by the executors
(`readsOutside_cons`), so that their simp sets need no general lemma about `∀ x ∈ l`. -/
def ReadsOutside (rs win : List (Nat × Nat)) : Prop := ∀ r ∈ rs, Outside r.1 r.2 win

@[janus_exec, janus_post, janus64_exec, janus64_post] theorem readsOutside_cons (r : Nat × Nat)
    (rs win : List (Nat × Nat)) :
    ReadsOutside (r :: rs) win = (Outside r.1 r.2 win ∧ ReadsOutside rs win) := by
  simp [ReadsOutside]

@[janus_exec, janus_post, janus64_exec, janus64_post] theorem readsOutside_nil (win : List (Nat × Nat)) :
    ReadsOutside [] win = True := by
  simp [ReadsOutside]

/-- The precondition of `RtContract` (arm64). -/
@[reducible] def RtPre (rt : List (Nat × Nat)) (stack : Nat) (H : RtReady) (sp : RtSpec)
    (s : State) : Prop :=
  CallOK s stack sp.nargs ∧ sp.pre (argWords s sp.nargs) s.mem ∧
    ReadsOutside (sp.reads (argWords s sp.nargs) s.mem) (calleeStack s stack sp.nargs) ∧
    (match sp.guard with
      | some adj => Janus.Spec.GuardOK s adj ∧
          Outside ((s.regs 28).toNat + 16) 8 (calleeStack s stack sp.nargs)
      | none => True) ∧
    (if sp.ready then Ready H rt (argWords s sp.nargs) s else True)

/-- The postcondition of `RtContract` (arm64). -/
@[reducible] def RtPost (rt : List (Nat × Nat)) (stack : Nat) (sp : RtSpec) (s s' : State) : Prop :=
  ∃ (r0 r1 r2 : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
    (ex : Option (Nat × Nat)) (ep : Nat → Bool),
    s' = retStateX s junk [r0, r1, r2] f v m ex ep ∧
      MemFrame s.mem m (rtIf sp.rtWrites rt ++ calleeStack s stack sp.nargs ++
        sp.writes (argWords s sp.nargs) s.mem) ∧
      sp.post rt (argWords s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat m

/-- **The arm64 contract of `sp` at `addr`**: a `Summary` of the linked program (see the module
documentation). -/
def RtContract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat) (H : RtReady)
    (sp : RtSpec) : Prop :=
  Summary p addr (RtPre rt stack H sp) (RtPost rt stack sp)

/-- How a proof from a function's own code ends: the final state `s'` keeps `SP`, `R18`, `R28`,
`R29` and the system registers, returns to `X30`, and its memory and results satisfy the
spec; then it is `RtPost` (the exclusive monitor may be anything). -/
theorem RtPost.intro {rt : List (Nat × Nat)} {stack : Nat} {sp : RtSpec} {s s' : State}
    (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18)
    (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid)
    (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr) (hfs : s'.fpsr = s.fpsr)
    (hf : MemFrame s.mem s'.mem (rtIf sp.rtWrites rt ++ calleeStack s stack sp.nargs ++
      sp.writes (argWords s sp.nargs) s.mem))
    (hq : sp.post rt (argWords s sp.nargs) s.mem (s'.regs 0).toNat (s'.regs 1).toNat (s'.regs 2).toNat s'.mem) :
    RtPost rt stack sp s s' := by
  refine ⟨s'.regs 0, s'.regs 1, s'.regs 2, s'.regs, s'.flags, s'.vregs, s'.mem, s'.excl, s'.exclPass, ?_, hf, hq⟩
  obtain ⟨r, sp', pc, fl, mem, dz, vr, tp, fc, fs, ex, ep⟩ := s'
  simp only at hsp hpc h18 h28 h29 hdz htp hfc hfs ⊢
  subst hsp hpc hdz htp hfc hfs
  simp only [retStateX, State.mk.injEq, and_true]
  funext i
  simp only [callRegs]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rcases i with _ | _ | _ | i <;> rfl

end Arm64

section Amd64

open Janus Janus.Amd64 Janus.Amd64.Tactic

/-- The argument words of an amd64 call: `RAX, RBX, RCX, RDI, RSI, R8, R9, R10, R11`, then the
stack words at `[RSP + 8, …)`. -/
def argWords64 (s : State) (n : Nat) : List Nat :=
  wordsFrom (fun i => if i < 9 then (s.regs (GoABI.argReg i)).toNat
    else s.mem.readLE ((s.regs 4).toNat + 8 + 8 * (i - 9)) 8) 0 n

attribute [janus64_exec, janus64_post] argWords64

/-- The stack check of an amd64 function falls through: `g` (`R14`) points at a readable
`stackguard0` below `RSP - adj`. -/
def GuardOK64 (s : State) (adj : Nat) : Prop :=
  (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + adj < (s.regs 4).toNat

/-- The precondition of `RtContract64`. -/
@[reducible] def RtPre64 (rt : List (Nat × Nat)) (stack : Nat) (H : RtReady) (sp : RtSpec)
    (s : State) : Prop :=
  CallOK64 s stack sp.nargs ∧ sp.pre (argWords64 s sp.nargs) s.mem ∧
    ReadsOutside (sp.reads (argWords64 s sp.nargs) s.mem) (calleeStack64 s stack sp.nargs) ∧
    (match sp.guard with
      | some adj => GuardOK64 s adj ∧
          Outside ((s.regs 14).toNat + 16) 8 (calleeStack64 s stack sp.nargs)
      | none => True) ∧
    (if sp.ready then Ready64 H rt (argWords64 s sp.nargs) s else True)

/-- The postcondition of `RtContract64`. -/
@[reducible] def RtPost64 (rt : List (Nat × Nat)) (stack : Nat) (sp : RtSpec) (s s' : State) :
    Prop :=
  ∃ (r0 r1 r2 : W64) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
    (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = retState64 s junk [r0, r1, r2] f x yh m zh kr ∧
      MemFrame s.mem m (rtIf sp.rtWrites rt ++ calleeStack64 s stack sp.nargs ++
        sp.writes (argWords64 s sp.nargs) s.mem) ∧
      sp.post rt (argWords64 s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat m

/-- How a proof from a function's own code ends (amd64): the final state returns to the return
address with `RSP + 8`, keeps `RBP`, `R14`, `X15`, `FS`, the direction flag and `MXCSR`, and its
memory and results (`RAX`, `RBX`, `RCX`) satisfy the spec; then it is `RtPost64`. -/
theorem RtPost64.intro {rt : List (Nat × Nat)} {stack : Nat} {sp : RtSpec} {s s' : State}
    (hrip : s'.rip = retAddrOf s) (h4 : s'.regs 4 = s.regs 4 + 8#64) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (hmx : s'.mxcsr = s.mxcsr)
    (hf : MemFrame s.mem s'.mem (rtIf sp.rtWrites rt ++ calleeStack64 s stack sp.nargs ++
      sp.writes (argWords64 s sp.nargs) s.mem))
    (hq : sp.post rt (argWords64 s sp.nargs) s.mem (s'.regs 0).toNat (s'.regs 3).toNat (s'.regs 1).toNat s'.mem)
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all) (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) :
    RtPost64 rt stack sp s s' := by
  refine ⟨s'.regs 0, s'.regs 3, s'.regs 1, s'.regs, s'.flags, s'.xmm, s'.ymmHi, s'.mem, s'.zmmHi, s'.kreg, ?_, hf, hq⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx, x8, fw⟩ := s'
  simp only at hrip h4 h5 h14 hx hfs hdf hmx hx87 hfw ⊢
  subst hrip hfs hdf hmx hx87 hfw
  simp only [retState64, State.mk.injEq, and_true, true_and]
  constructor
  · funext i
    simp only [callRegs64]
    split
    · rename_i hi; subst hi; exact h4
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · split
        · rename_i hi; subst hi; rfl
        · split
          · rename_i hi; subst hi; rfl
          · split
            · rename_i hi; subst hi; rfl
            · rfl
  · funext i
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-- **The amd64 contract of `sp` at `addr`**. -/
def RtContract64 (p : Janus.Amd64.Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat)
    (H : RtReady) (sp : RtSpec) : Prop :=
  Summary p addr (RtPre64 rt stack H sp) (RtPost64 rt stack sp)

end Amd64

/-- The readiness part of `RtPre` of a spec with `ready = true`. -/
theorem ready_of {c : Bool} {P : Prop} (h : c = true) (hp : if c then P else True) : P := by
  subst h; exact hp

theorem ready_intro {c : Bool} {P : Prop} (h : c = true) (hp : P) : if c then P else True := by
  subst h; exact hp

/-- A weaker postcondition and a stronger precondition give a weaker contract (arm64). -/
theorem RtContract.mono {p : Janus.Program} {addr : Nat} {rt : List (Nat × Nat)} {stack : Nat}
    {H : RtReady} {sp : RtSpec} (h : RtContract p addr rt stack H sp)
    {pre' : Janus.Arm64.State → Prop} (hpre : ∀ s, pre' s → RtPre rt stack H sp s) :
    Janus.Tactic.Summary p addr pre' (RtPost rt stack sp) :=
  Janus.Tactic.Summary.mono h hpre fun _ _ _ h => h

end Janus.Contracts

namespace Janus.Contracts

attribute [janus_exec, janus_post, janus64_exec, janus64_post] List.nil_append
  Janus.outside_cons Janus.outside_nil

end Janus.Contracts
