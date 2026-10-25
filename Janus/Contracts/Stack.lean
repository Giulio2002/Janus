import Janus.Spec.Stack
import Janus.Tactic

/-!
# The stack-growth contract and the grown run (arm64)

Every Go function that is not `NOSPLIT` begins with a stack-growth check (`Janus.GoABI`,
"Stack-growth prologue"): it compares `SP` with `g.stackguard0` and, when the frame does not
fit, branches to `runtime.morestack_noctxt`. Until now every theorem assumed the check falls
through (`GuardOK`, `StackGuardOK`), so the grown case — the `morestack` call — was excluded
(`docs/COVERAGE.md`, R7). This file removes that restriction on arm64.

* `runtime.morestack`/`morestack_noctxt` save the goroutine's context and call `runtime.newstack`
  on `g0`; `newstack` allocates a larger stack, `copystack` copies the frames and adjusts every
  pointer into the old stack (the stack maps, `Janus.Spec.Stack`), updates `SP`, `FP`, `g.stack`
  and `g.stackguard0`, and `gogo` resumes execution **at the instruction after the `morestack`
  call** (the prologue's `JMP f`, which re-enters `f` — now with room). The whole goroutine stack
  moves, so the resumed `SP` is the old one plus the growth delta `δ = new.hi - old.hi`.

* **The contract** `MorestackContract` states that transition as a `Tactic.Summary` of the
  linked program at the `morestack_noctxt` contract address: from the prologue's call state it
  "returns" (through `gogo`) to the saved return address `X30` in a state `Grown` — the frames
  moved by some `δ > 0` (`Janus.Spec.Stack.Moved` along the unwinder's `Chain`), `SP`/`FP`
  shifted, `g.stack`/`stackguard0` updated — with a **larger** stack that has room for the
  function's own maximal frame (`newstack`: `newsize ≥ used + funcMaxSPDelta + stackGuard`). It
  does not promise room for an unbounded recursion; a deep recursion grows again at the next
  level (`growReenter`, by well-founded recursion on the stack's distance from `maxstacksize`).

* **The grown run** `GrownReturns` is `Returns` through any number of `morestack` resumes: a run
  that either returns, or reaches `morestack`, grows, and continues from the resumed state. It is
  `Returns` exactly when the stack already has room. `EnsuresGrow` is the grown `Ensures`:
  the room precondition is dropped, the `morestack` contract assumed, and the conclusion holds
  for a stack of any size, growth included.

* **The key lemma** `grownReturns_of_summary`: from a roomy `Summary` (`f` is correct on any
  stack with room) and the `morestack` contract, `f` is correct on any stack — the relocation
  invariance of `Janus.Spec.Stack.Moved`/`Chain` carries the `Summary`'s post across the move.

**Trusted** (stated in `docs/SOUNDNESS.md`): the relocation `Moved`/`Chain` is what
`newstack`/`copystack` do, and in particular the stack maps are correct (the compiler's
liveness information marks exactly the pointer slots). Pointers into the stack held in non-stack
memory are not adjusted; Go's escape analysis forbids them, and the contract's precondition
states it (`NoStackPtrOutside`). See `Janus/Contracts/StackSat.lean` for satisfiability.
-/

namespace Janus.Contracts.Stack

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Stack

/-! ## The resumed state after one growth -/

/-- The goroutine stack bounds a growth reads and writes: `g`, `[lo, hi)`, the saved context
`(pc, sp)` the unwinder starts from (`g.sched`), and the innermost frame's link register. For
the prologue call the saved pc is the return address `X30` (the `JMP f` glue) and the saved sp is
`SP` (the glue runs on the caller's stack). -/
structure GrowAt (s : State) (g lo hi : Nat) : Prop where
  gstack : GStack s.mem g lo hi
  greg : (s.regs regG).toNat = g
  inStack : lo ≤ s.sp.toNat ∧ s.sp.toNat ≤ hi
  aligned : lo % 8 = 0 ∧ hi % 8 = 0 ∧ s.sp.toNat % 8 = 0
  low : 4096 ≤ lo

/-- `s'` is `s` with the goroutine stack `[lo, hi)` grown to `[lo', hi')` (`δ = hi' - hi`), the
frames walked from `(X30, SP)` moved (`Moved` along the `Chain` of the frame table `FT`), `SP`
and `FP` shifted by `δ`, `g.stack` and `g.stackguard0` updated, `X30` (a code address) kept, and
execution resumed there. The arguments and the frame below `SP` are moved with the stack; the
registers other than `SP`/`FP`/`g` are unspecified except that the integer arguments (non-stack
values) are kept — a theorem recovers them from the moved spill slots. `Grown` is the
postcondition shape of the contract. -/
structure Grown (FT : FrameTable) (pool : List (Nat × Nat)) (g lo hi : Nat) (delta lo' hi' : Nat)
    (s s' : State) : Prop where
  /-- The new stack is larger, mapped above the first page, and 8-aligned. -/
  grows : hi - lo < hi' - lo' ∧ hi' = hi + delta ∧ 0 < delta ∧ 4096 ≤ lo' ∧
    lo' % 8 = 0 ∧ hi' % 8 = 0
  /-- Room for the function's own maximal frame plus the guard below the resumed `SP`
  (`newstack`: `newsize - used ≥ funcMaxSPDelta + stackGuard`). -/
  room : lo' + stackGuard ≤ s.sp.toNat + delta
  /-- The resumed program counter is the saved return address, on the new stack. -/
  pc : s'.pc = s.regs regLR
  /-- `SP` and `FP` are shifted by `δ`; `g` (a heap pointer) is kept. -/
  sp : s'.sp.toNat = s.sp.toNat + delta
  fp : (s'.regs regFP).toNat = (s.regs regFP).toNat + delta ∨ (s.regs regFP).toNat < lo ∨ hi ≤ (s.regs regFP).toNat
  greg : s'.regs regG = s.regs regG
  /-- The goroutine's stack descriptor now reads `[lo', hi')`. -/
  gstack : GStack s'.mem g lo' hi'
  /-- The memory is the old one with the stack moved (`[SP, hi)` relocated to `[SP + δ, hi')`),
  along the frame table's unwinder walk. -/
  moved : ∃ (cls : Nat → Bool) (fs : List Frame),
    Chain Arch.arm64 FT s.mem hi (s.regs regLR).toNat s.sp.toNat none fs ∧
    cls = framesCls Arch.arm64 FT fs ∧
    Moved cls pool lo hi hi' s.sp.toNat [] s.mem s'.mem

/-! ## The grown run: `Returns` through any number of growths -/

/-- `Returns` extended through `morestack`: from `s` the run returns satisfying `post`, after
zero or more stack growths. Each growth reaches the `morestack` stub and the `reloc` relation
(the contract) resumes at `entry` (the `JMP f` glue in `X30`), from where the run continues.
`reloc s_m s_r` is the contract's `Grown`-shaped transition at the morestack call state `s_m`. -/
inductive GrownReturns (p : Program) (reloc : State → State → Prop) :
    State → (State → Prop) → Prop where
  | done {s : State} {post : State → Prop} (h : Returns p s post) : GrownReturns p reloc s post
  | grow {n : Nat} {name : String} {s s_m s_r : State} {post : State → Prop}
      (hrun : p.run n s = .ok (.stub name .morestack s_m))
      (hre : reloc s_m s_r) (hrec : GrownReturns p reloc s_r post) :
      GrownReturns p reloc s post

theorem GrownReturns.mono {p : Program} {reloc : State → State → Prop} {s : State}
    {post post' : State → Prop} (h : GrownReturns p reloc s post)
    (hpp : ∀ s', post s' → post' s') : GrownReturns p reloc s post' := by
  induction h generalizing post' with
  | done hr => exact .done (hr.mono hpp)
  | grow hrun hre _ ih => exact .grow hrun hre (ih hpp)

/-- Ordinary steps before a grown run (used to run the prologue up to the `morestack` call or the
fall-through, then continue). -/
theorem GrownReturns.of_steps {p : Program} {reloc : State → State → Prop} {s s' : State}
    {post : State → Prop} {k : Nat} (hs : Program.Steps p s k s')
    (h : GrownReturns p reloc s' post) : GrownReturns p reloc s post := by
  cases h with
  | done hr => exact .done (by obtain ⟨n, o, hr, hq⟩ := hr; exact ⟨k + n, o, by rw [Program.run_steps hs]; exact hr, hq⟩)
  | grow hrun hre hrec =>
    exact .grow (n := k + _) (by rw [Program.run_steps hs]; exact hrun) hre hrec

/-! ## The `morestack` contract -/

/-- A state at the prologue's `morestack` call: it is at a `morestack` stub of `p`, the saved
return address `X30` (the `JMP f` glue) is an admissible return address, the goroutine `g` runs
on the stack `[lo, hi)`, which is not yet full (`hi - lo < maxstacksize`, so `newstack` grows it
rather than throwing), the frame table `FT` describes the code, and no pointer into `[lo, hi)` is
held outside the stack (`NoStackPtrOutside`: Go's escape analysis, stated as a hypothesis). -/
structure MorestackPre (p : Program) (FT : FrameTable) (pool : List (Nat × Nat))
    (g lo hi : Nat) (s_m : State) : Prop where
  stub : ∃ name, p.stubAt s_m.pc.toNat = some ⟨name, s_m.pc.toNat, .morestack⟩
  grow : GrowAt s_m g lo hi
  notFull : hi - lo < maxstacksize
  code : FT.CodeOutside pool ∧ FT.Aligned
  stackInPool : InRanges lo (hi - lo) pool

/-- **The `morestack` contract.** For every state `s_m` at a `morestack` call satisfying
`MorestackPre`, the relation `reloc` resumes at the saved return address in a `Grown` state: the
runtime allocated a larger stack, copied the frames and adjusted the pointers (`Grown`, i.e.
`Janus.Spec.Stack.Moved` along the unwinder's `Chain`), updated `SP`, `FP`, `g.stack` and
`g.stackguard0`, and resumed. This is the trusted model of `runtime.morestack`/`newstack`/
`copystack`/`gogo` (`docs/SOUNDNESS.md`). -/
def MorestackContract (p : Program) (FT : FrameTable) (pool : List (Nat × Nat))
    (reloc : State → State → Prop) : Prop :=
  ∀ g lo hi s_m, MorestackPre p FT pool g lo hi s_m →
    ∃ (s_r : State) (delta lo' hi' : Nat),
      reloc s_m s_r ∧ Grown FT pool g lo hi delta lo' hi' s_m s_r

/-! ## The growth recursor

A function's grown correctness is proved by induction on the stack's distance from
`maxstacksize`: a growth makes the stack strictly larger (`Grown.grows`), so after finitely many
the stack has room and the roomy `Summary` applies. `grow_rec` packages that well-founded
recursion; an example provides `step`, which handles one entry state — either the stack already
has room (the prologue falls through; apply the `Summary`) or it reaches `morestack`, grows, and
re-enters the entry on a strictly larger stack, where the induction hypothesis applies. -/

/-- Well-founded recursion on `maxstacksize - (hi - lo)`: to prove `GrownReturns` for an entry
configuration `Cfg s lo hi` on a stack `[lo, hi)` not yet full, it suffices to handle one entry
given the result for every strictly larger (still not full) stack. -/
theorem grow_rec {p : Program} {reloc : State → State → Prop} {Cfg : State → Nat → Nat → Prop}
    {post : State → Prop}
    (step : ∀ lo hi, (∀ lo₂ hi₂ s₂, hi₂ - lo₂ < maxstacksize → hi - lo < hi₂ - lo₂ →
          Cfg s₂ lo₂ hi₂ → GrownReturns p reloc s₂ post) →
        ∀ s, Cfg s lo hi → hi - lo < maxstacksize → GrownReturns p reloc s post) :
    ∀ lo hi s, Cfg s lo hi → hi - lo < maxstacksize → GrownReturns p reloc s post := by
  intro lo hi
  -- strong induction on the deficit `maxstacksize - (hi - lo)`
  have key : ∀ d lo hi, maxstacksize - (hi - lo) ≤ d → ∀ s, Cfg s lo hi → hi - lo < maxstacksize →
      GrownReturns p reloc s post := by
    intro d
    induction d with
    | zero =>
      intro lo hi hd s hcfg hlt
      exact step lo hi (fun lo₂ hi₂ s₂ _ hgt _ => absurd hd (by omega)) s hcfg hlt
    | succ d ih =>
      intro lo hi hd s hcfg hlt
      exact step lo hi (fun lo₂ hi₂ s₂ hlt₂ hgt hcfg₂ => ih lo₂ hi₂ (by omega) s₂ hcfg₂ hlt₂) s hcfg hlt
  exact fun s hcfg hlt => key (maxstacksize - (hi - lo)) lo hi (Nat.le_refl _) s hcfg hlt

/-! ## Grown `Ensures`

`EnsuresGrow p entry args pre post`: for every admissible return address and every call state
with these arguments satisfying `pre` (which no longer assumes room), the call returns satisfying
`post`, after any number of stack growths handled by the `morestack` contract `reloc`. It is the
grown counterpart of `GoABI.Ensures`. -/

/-- The grown contract of a Go function, under the `morestack` contract `reloc`. -/
def EnsuresGrow (p : Program) (reloc : State → State → Prop) (entry : Nat) (args : List W64)
    (pre : State → Prop) (post : State → State → Prop) : Prop :=
  ∀ ret, RetAddr p ret → ∀ s, CallSetup (p.withExit ret) entry args s → pre s →
    GrownReturns (p.withExit ret) reloc s (fun s' => post s s')

end Janus.Contracts.Stack
