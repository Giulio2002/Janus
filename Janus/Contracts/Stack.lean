import Janus.Spec.Stack
import Janus.Contracts.Alloc

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

/-- The memory reserved for goroutine stacks is mapped and writable: every range `[a, b)` of
`pool` is below `2^48` and writable in `m`. -/
def PoolOK (m : Memory) (pool : List (Nat × Nat)) : Prop :=
  ∀ r ∈ pool, r.1 ≤ r.2 ∧ r.2 ≤ 2 ^ 48 ∧ m.accessible r.1 (r.2 - r.1) true = true

/-- A range inside the stack pools is writable. -/
theorem PoolOK.accessible {m : Memory} {pool : List (Nat × Nat)} (h : PoolOK m pool) {a n : Nat}
    (hin : InRanges a n pool) : m.accessible a n true = true := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  obtain ⟨-, -, hacc⟩ := h r hr
  exact Memory.accessible_mono _ hacc h1 (by omega)

/-- `PoolOK` depends only on the regions. -/
theorem PoolOK.of_accessible {m m' : Memory} {pool : List (Nat × Nat)} (h : PoolOK m pool)
    (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) : PoolOK m' pool :=
  fun r hr => by obtain ⟨h1, h2, h3⟩ := h r hr; exact ⟨h1, h2, by rw [hacc]; exact h3⟩

/-- A store inside the pools keeps the goroutine's descriptor (outside the pools). -/
theorem _root_.Janus.Spec.Stack.GStack.writeLE {m : Memory} {g lo hi a k v : Nat} {pool : List (Nat × Nat)}
    (h : GStack m g lo hi) (hg : Outside g 24 pool) (hin : InRanges a k pool) :
    GStack (m.writeLE a k v) g lo hi := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hd := InRanges.disjoint hin hg
  refine ⟨h1, by rw [Memory.accessible_writeLE]; exact h2, ?_, ?_, ?_⟩
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [gStackLo]; omega)]; exact h3
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [gStackHi]; omega)]; exact h4
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [gStackguard0]; omega)]; exact h5

/-- The runtime's view is unchanged by a frame of changes outside the runtime-owned memory that
keeps the regions. -/
theorem rtView_eq_of_frame {rt rs : List (Nat × Nat)} {m m' : Memory} (hf : MemFrame m m' rs)
    (hreg : m'.regions = m.regions) (hout : ∀ a, InRanges a 1 rt → Outside a 1 rs) :
    rtView rt m' = rtView rt m := by
  unfold rtView
  rw [hreg]
  congr 1
  funext a
  split
  · rename_i ha
    obtain ⟨r, hr, hx⟩ := List.any_eq_true.1 ha
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    have := hf.readLE a 1 (hout a ⟨r, hr, hx.1, by omega⟩)
    simp only [Memory.readLE, Nat.mul_zero, Nat.add_zero] at this
    exact BitVec.eq_of_toNat_eq this
  · rfl

/-- The precondition of the `morestack` call in a function's prologue (arm64), at the state
`s_m` reached by the prologue's `BL runtime.morestack_noctxt`:

* `s_m` is at a `morestack` stub; `X30` is the glue after the call (`LDP …; B f`), `X3` the
  function's own return address (`MOVD R30, R3`), `X29 = SP - 8` (the caller's frame pointer,
  Go's frame-pointer convention), `SP` 16-aligned;
* the goroutine `g = X28` runs on `[lo, hi)` (`GStack`, no preemption request), above the first
  page, inside the stack pools `pool`, which are writable; `g`'s descriptor lies outside the
  pools;
* the stack unwinds (`Chain` from the saved context `(X30, SP, X3)`): the runtime throws
  (`unknown caller pc`) otherwise;
* the grown stack fits `maxstacksize` (`newstack` throws `stack overflow` otherwise): both the
  doubled stack and twice the used part plus the function's largest frame and the guard;
* the runtime is ready to allocate the new stack (`H`, round 9's readiness predicate, on the
  runtime-owned memory `rt`). -/
structure MorestackPre (p : Program) (FT : FrameTable) (pool rt : List (Nat × Nat))
    (H : RtReady) (g lo hi : Nat) (s_m : State) : Prop where
  stub : ∃ name, p.stubAt s_m.pc.toNat = some ⟨name, s_m.pc.toNat, .morestack⟩
  greg : (s_m.regs regG).toNat = g
  gstack : GStack s_m.mem g lo hi
  gout : Outside g 24 pool
  low : 4096 ≤ lo ∧ lo + 8 ≤ s_m.sp.toNat ∧ s_m.sp.toNat + 8 ≤ hi ∧ hi ≤ 2 ^ 48
  aligned : lo % 16 = 0 ∧ hi % 16 = 0 ∧ s_m.sp.toNat % 16 = 0
  fp : (s_m.regs regFP).toNat = s_m.sp.toNat - 8
  inPool : InRanges lo (hi - lo) pool ∧ PoolOK s_m.mem pool
  chain : ∃ fs, Chain Arch.arm64 FT s_m.mem hi (s_m.regs regLR).toNat s_m.sp.toNat
    (some (s_m.regs 3).toNat) fs
  fits : 2 * (hi - lo) ≤ maxstacksize ∧
    2 * ((hi - s_m.sp.toNat) + FT.maxspd (s_m.regs regLR).toNat + stackGuard) ≤ maxstacksize
  code : FT.CodeOutside pool ∧ FT.Aligned
  ready : H [] g 0 (rtView rt s_m.mem)

/-- The words a growth at the prologue adjusts (arm64): the caller's saved frame pointer at
`SP - 8` (`adjustctxt`, as `gobuf.bp = SP - 8`) and the words of the walk's frames. -/
def moveCls (FT : FrameTable) (sp : Nat) (fs : List Frame) (a : Nat) : Bool :=
  decide (a = sp - 8) || framesCls Arch.arm64 FT fs a

/-- `s'` is the resumed state after `newstack` grew the stack of the call state `s` (arm64)
from `[lo, hi)` to `[lo', hi')`: an address `a` of the old stack is now at `a + hi' - hi` (the
new stack may lie above or below the old one):

* the new stack is larger, inside the pools, apart from the old one, at most `maxstacksize`,
  and has room below the resumed `SP` for the function's largest frame and the guard
  (`newsize - used ≥ funcMaxSPDelta + stackGuard`);
* `gogo` resumed at `X30` (the glue) with `SP` and `X29` moved, `X30 := X3` (`gobuf.lr`), `X28`
  (`g`) and `X18` kept, `X26 = 0` (`morestack_noctxt`), every other register, the flags and the
  SIMD&FP registers unspecified;
* `g.stack`, `g.stackguard0` read `[lo', hi')`, `lo' + stackGuard`;
* memory: the frames of the walk moved (`Moved` along `framesCls` of the `Chain`), from
  `SP - 8` on: `adjustctxt` also copies and adjusts the word below `SP` where the arm64 frame
  layout keeps the caller's saved frame pointer (`gobuf.bp = SP - 8`), and outside
  the pools and the runtime's own memory `rt` nothing changed (regions included);
* the runtime is ready again (`H`). -/
structure Grown (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (g lo hi lo' hi' : Nat)
    (s s' : State) : Prop where
  grows : hi - lo < hi' - lo' ∧ hi' - lo' ≤ maxstacksize ∧ 4096 ≤ lo' ∧ lo' % 16 = 0 ∧
    hi' % 16 = 0 ∧ hi' ≤ 2 ^ 48 ∧ InRanges lo' (hi' - lo') pool ∧ (hi ≤ lo' ∨ hi' ≤ lo)
  room : lo' + stackGuard + FT.maxspd (s.regs regLR).toNat + (hi - s.sp.toNat) ≤ hi'
  pc : s'.pc = s.regs regLR
  sp : s'.sp = BitVec.ofNat 64 (s.sp.toNat + hi' - hi)
  regs : ∀ i, i = regFP → s'.regs i = BitVec.ofNat 64 ((s.regs regFP).toNat + hi' - hi)
  lr : s'.regs regLR = s.regs 3
  gkeep : s'.regs regG = s.regs regG ∧ s'.regs regPlatform = s.regs regPlatform
  ctxt : s'.regs regClosure = 0
  keep : s'.dczid = s.dczid ∧ s'.tpidr = s.tpidr ∧ s'.fpcr = s.fpcr
  gstack : GStack s'.mem g lo' hi'
  moved : ∀ fs, Chain Arch.arm64 FT s.mem hi (s.regs regLR).toNat s.sp.toNat (some (s.regs 3).toNat) fs →
    Moved (moveCls FT s.sp.toNat fs) pool lo hi hi' (s.sp.toNat - 8) [] s.mem s'.mem
  frame : MemFrame s.mem s'.mem (pool ++ rt)
  ready : H [] g 0 (rtView rt s'.mem)

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

/-- A run that reaches a `morestack` stub continues as a grown run from any state the
contract resumes in. This is how a proof uses the contract: `janus_run` runs the prologue to the
stub, leaving the `morestack` call state, from which the contract gives the resumed state. -/
theorem GrownReturns.of_reaches_stub {p : Program} {reloc : State → State → Prop} {s : State}
    {post : State → Prop}
    (h : Reaches p s (fun o => match o with
      | .stub _ .morestack s_m => ∃ s_r, reloc s_m s_r ∧ GrownReturns p reloc s_r post
      | _ => False)) : GrownReturns p reloc s post := by
  obtain ⟨n, o, hrun, hq⟩ := h
  cases o with
  | returned => exact hq.elim
  | stub name kind s_m =>
    cases kind with
    | morestack => obtain ⟨s_r, hre, hg⟩ := hq; exact .grow hrun hre hg
    | panic => exact hq.elim
    | external => exact hq.elim

/-- A walk stays a walk in memory that agrees on its return-address slots. -/
theorem Chain.congr {A : Arch} {FT : FrameTable} {m m' : Memory} {hi pc sp : Nat}
    {lr0 : Option Nat} {fs : List Frame} (h : Chain A FT m hi pc sp lr0 fs) (h16 : 16 ≤ sp)
    (hslot : ∀ f ∈ fs, FT.stop f.pc = false →
      m'.readLE (A.lrSlot f.sp f.fp) 8 = m.readLE (A.lrSlot f.sp f.fp) 8) :
    Chain A FT m' hi pc sp lr0 fs := by
  have := Chain.mv (m' := m') hi h h16 (by omega) (fun f hf hst => by
    rw [Nat.add_sub_cancel]; exact hslot f hf hst)
  have hid : fs.map (Frame.mv hi hi) = fs := by
    conv => rhs; rw [← List.map_id fs]
    apply List.map_congr_left; intro f _; simp [Frame.mv]
  rw [Nat.add_sub_cancel, hid] at this; exact this

/-! ## Grown callee summaries

A callee that may grow the stack (in its own prologue or deeper) still returns to its caller's
return address — a code address, which a move never changes — but on a moved stack. `GrownRet`
is `ReachesRet` through growths, and `GSummary` the grown `Summary`: what a recursive
function's induction hypothesis is. -/

/-- From `s`, ordinary steps and stack growths (each a run to a `morestack` stub followed by the
contract's resume `reloc`) reach a state at `ret` satisfying `Q`. -/
inductive GrownRet (p : Program) (reloc : State → State → Prop) (ret : W64) :
    State → (State → Prop) → Prop where
  | done {s s' : State} {Q : State → Prop} {k : Nat} (hs : Program.Steps p s k s')
      (hpc : s'.pc = ret) (hq : Q s') : GrownRet p reloc ret s Q
  | grow {s s_m s_r : State} {Q : State → Prop} {k : Nat} {st : Stub}
      (hs : Program.Steps p s k s_m) (hx : s_m.pc.toNat ≠ p.exitAddr)
      (hst : p.stubAt s_m.pc.toNat = some st) (hk : st.kind = .morestack) (hre : reloc s_m s_r)
      (hrec : GrownRet p reloc ret s_r Q) : GrownRet p reloc ret s Q

/-- A callee contract through stack growths: from every state at `entry` satisfying `pre`, the
callee reaches its return address `X30` in a state satisfying `post`, growing the stack any
number of times. -/
def GSummary (p : Program) (reloc : State → State → Prop) (entry : Nat) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ s, s.pc = BitVec.ofNat 64 entry → pre s → GrownRet p reloc (s.regs regLR) s (post s)

namespace GrownRet

variable {p : Program} {reloc : State → State → Prop} {ret : W64}

theorem of_reachesRet {s : State} {Q : State → Prop} (h : ReachesRet p ret s Q) :
    GrownRet p reloc ret s Q := by
  obtain ⟨k, s', hs, hpc, hq⟩ := h; exact .done hs hpc hq

theorem of_steps {s s' : State} {Q : State → Prop} {k : Nat} (hs : Program.Steps p s k s')
    (h : GrownRet p reloc ret s' Q) : GrownRet p reloc ret s Q := by
  cases h with
  | done hs' hpc hq => exact .done (hs.trans hs') hpc hq
  | grow hs' hx hst hk hre hrec => exact .grow (hs.trans hs') hx hst hk hre hrec

theorem mono {s : State} {Q Q' : State → Prop} (h : GrownRet p reloc ret s Q)
    (hq : ∀ s', Q s' → Q' s') : GrownRet p reloc ret s Q' := by
  induction h with
  | done hs hpc h => exact .done hs hpc (hq _ h)
  | grow hs hx hst hk hre _ ih => exact .grow hs hx hst hk hre (ih hq)

/-- Sequencing: a grown run to `r₁`, then from every state it may end in, a grown run to `r₂`. -/
theorem bind {r₁ : W64} {s : State} {Q₁ Q₂ : State → Prop} (h : GrownRet p reloc r₁ s Q₁)
    (hk : ∀ s', s'.pc = r₁ → Q₁ s' → GrownRet p reloc ret s' Q₂) : GrownRet p reloc ret s Q₂ := by
  induction h with
  | done hs hpc hq => exact of_steps hs (hk _ hpc hq)
  | grow hs hx hst hkd hre _ ih => exact .grow hs hx hst hkd hre (ih hk)

/-- A run that reaches a `morestack` stub continues as a grown run from the contract's resume. -/
theorem of_reaches_stub {s : State} {Q : State → Prop}
    (h : Reaches p s (fun o => match o with
      | .stub _ .morestack s_m => ∃ s_r, reloc s_m s_r ∧ GrownRet p reloc ret s_r Q
      | _ => False)) : GrownRet p reloc ret s Q := by
  obtain ⟨n, o, hrun, hq⟩ := h
  cases o with
  | returned => exact hq.elim
  | stub name kind s_m =>
    obtain ⟨j, st, hs, hst, -, hk⟩ := GoABI.steps_of_run_stub hrun
    cases kind with
    | morestack =>
      obtain ⟨s_r, hre, hg⟩ := hq
      refine .grow hs ?_ hst hk hre hg
      intro hx
      have h0 := Program.run_steps_exit (k := j) hs hx
      have := Program.run_ok_unique hrun h0
      cases this
    | panic => exact hq.elim
    | external => exact hq.elim

/-- In the caller's program `p.withExit ret` (no code at `ret`, and no stub there). -/
theorem withExit {r : Nat} {s : State} {Q : State → Prop} (h : GrownRet p reloc ret s Q)
    (hf : p.fetch r = none) (hst : ∀ st ∈ p.stubs, st.addr ≠ r) :
    GrownRet (p.withExit r) reloc ret s Q := by
  induction h with
  | done hs hpc hq => exact .done (hs.withExit hf) hpc hq
  | @grow s s_m s_r Q k st hs hx hstb hk hre _ ih =>
    refine .grow (hs.withExit hf) ?_ hstb hk hre ih
    intro he
    have hfind : p.stubs.find? (·.addr = s_m.pc.toNat) = some st := hstb
    have hmem : st ∈ p.stubs := List.mem_of_find?_eq_some hfind
    have hpc : st.addr = s_m.pc.toNat := by
      have := List.find?_some hfind; simpa using this
    exact hst st hmem (by rw [hpc]; exact he)

/-- At the top: a grown run to the exit address is a grown run that returns. -/
theorem toGrownReturns {r : Nat} {s : State} {Q : State → Prop}
    (h : GrownRet (p.withExit r) reloc (BitVec.ofNat 64 r) s Q) (hr : r < 2 ^ 64) :
    GrownReturns (p.withExit r) reloc s Q := by
  induction h with
  | done hs hpc hq =>
    refine .done ⟨_, _, Program.run_steps_exit hs ?_, hq⟩
    rw [hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]; rfl
  | @grow s s_m s_r Q k st hs hx hst hk hre _ ih =>
    have := Program.run_steps_stub hs hx hst
    rw [hk] at this
    exact .grow this hre ih

end GrownRet

/-- A grown callee summary used at a call: the callee's grown run to the return address, then
the caller's continuation from every state the callee may return in. -/
theorem GrownRet.call {p : Program} {reloc : State → State → Prop} {entry : Nat}
    {pre : State → Prop} {post : State → State → Prop} {s : State} {ret : W64} {Q : State → Prop}
    (hsum : GSummary p reloc entry pre post) (hpc : s.pc = BitVec.ofNat 64 entry) (hpre : pre s)
    (h : ∀ s', s'.pc = s.regs regLR → post s s' → GrownRet p reloc ret s' Q) :
    GrownRet p reloc ret s Q :=
  (hsum s hpc hpre).bind h

/-- Strong induction for grown summaries (`Tactic.Summary.induction`). -/
theorem GSummary.induction {p : Program} {reloc : State → State → Prop} {entry : Nat}
    {pre : State → Prop} {post : State → State → Prop} (μ : State → Nat)
    (step : ∀ n, GSummary p reloc entry (fun s => pre s ∧ μ s < n) post →
      GSummary p reloc entry (fun s => pre s ∧ μ s = n) post) :
    GSummary p reloc entry pre post := by
  have h : ∀ n, GSummary p reloc entry (fun s => pre s ∧ μ s < n) post := by
    intro n
    induction n with
    | zero => intro s _ ⟨_, h⟩; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro s hpc ⟨hp, hlt⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · exact ih s hpc ⟨hp, hlt⟩
      · exact step n ih s hpc ⟨hp, heq⟩
  intro s hpc hp
  exact h (μ s + 1) s hpc ⟨hp, Nat.lt_succ_self _⟩

/-! ## The `morestack` contract -/

/-- **The `morestack` contract** (arm64). From every state at the prologue's `morestack` call
satisfying `MorestackPre`, the relation `reloc` resumes in a `Grown` state: the runtime
allocated a larger stack, copied the frames and adjusted the pointers into the old stack along
the stack maps, updated `SP`, `FP`, `g.stack` and `g.stackguard0`, and resumed at the glue after
the call. The trusted model of `runtime.morestack_noctxt`/`morestack`/`newstack`/`copystack`/
`gogo` (`docs/SOUNDNESS.md`); `Janus/Contracts/StackSat.lean` proves it satisfiable. -/
def MorestackContract (p : Program) (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) : Prop :=
  ∀ g lo hi s_m, MorestackPre p FT pool rt H g lo hi s_m →
    ∃ (s_r : State) (lo' hi' : Nat), reloc s_m s_r ∧ Grown FT pool rt H g lo hi lo' hi' s_m s_r

/-! ## The growth recursor

A function's grown correctness is proved by induction on the stack's distance from
`maxstacksize`: a growth makes the stack strictly larger (`Grown.grows`), so after finitely many
the stack has room and the roomy `Summary` applies. `grow_rec` packages that well-founded
recursion; an example provides `step`, which handles one entry state — either the stack already
has room (the prologue falls through; apply the `Summary`) or it reaches `morestack`, grows, and
re-enters the entry on a strictly larger stack, where the induction hypothesis applies. -/

/-- Well-founded recursion on `maxstacksize - (hi - lo)`: to prove `GrownReturns` for an entry
configuration `Cfg s lo hi` on a stack `[lo, hi)` of at most `maxstacksize` bytes, it suffices to handle one entry
given the result for every strictly larger (still not full) stack. -/
theorem grow_rec {p : Program} {reloc : State → State → Prop} {Cfg : State → Nat → Nat → Prop}
    {post : State → Prop}
    (step : ∀ lo hi, (∀ lo₂ hi₂ s₂, hi₂ - lo₂ ≤ maxstacksize → hi - lo < hi₂ - lo₂ →
          Cfg s₂ lo₂ hi₂ → GrownReturns p reloc s₂ post) →
        ∀ s, Cfg s lo hi → hi - lo ≤ maxstacksize → GrownReturns p reloc s post) :
    ∀ lo hi s, Cfg s lo hi → hi - lo ≤ maxstacksize → GrownReturns p reloc s post := by
  intro lo hi
  -- strong induction on the deficit `maxstacksize - (hi - lo)`
  have key : ∀ d lo hi, maxstacksize - (hi - lo) ≤ d → ∀ s, Cfg s lo hi → hi - lo ≤ maxstacksize →
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
