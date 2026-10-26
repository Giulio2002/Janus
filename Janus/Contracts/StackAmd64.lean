import Janus.Contracts.Stack
import Janus.Amd64.Recursion

/-!
# The stack-growth contract and the grown run (amd64)

The amd64 counterpart of `Janus.Contracts.Stack` (see there, `docs/RUNTIME-CONTRACTS.md` "Stack
growth"). The model of the move (`Janus.Spec.Stack.Moved`, the unwinder's `Chain`, the frame
table and the stack maps) is the same, instantiated with `Arch.amd64`; what differs is the
call sequence:

* the prologue's check (`CMPQ SP, 16(R14); JBE …`, or `LEAQ -k(SP), R12; CMPQ R12, 16(R14)`)
  branches to the function's tail, which spills the register arguments to their slots `8(SP)`,
  `16(SP)`, … in the caller's argument area and `CALL`s `runtime.morestack_noctxt`. At the stub
  `[RSP]` holds the glue address (the instruction after the `CALL`: reload the arguments, `JMP f`)
  and `RSP + 8` is the function's own stack pointer, where its return address is;
* `morestack` records `gobuf.pc = [RSP]`, `gobuf.sp = RSP + 8`, `gobuf.bp = RBP`, `gobuf.ctxt =
  RDX = 0` (`morestack_noctxt`); `newstack` copies `[gobuf.sp, hi)` (`copystack`: the used part
  of the stack; the pushed glue address below it is not copied), adjusts the pointers of the
  unwinder's walk from `(gobuf.pc, gobuf.sp)` and `gobuf.bp` (`adjustctxt`), and `gogo` resumes
  at the glue with `RSP = gobuf.sp + δ`, `RBP = adjust(gobuf.bp)`, `RDX = 0`, `R14 = g`;
* `X15` is still zero (no code on the way writes it: `morestack` and `gogo` do not, and `newstack`
  is ABIInternal Go code, which keeps it zero), the direction flag clear, `MXCSR`'s control bits
  kept; every other register and the flags are unspecified.

`GrownReturns64`, `GrownRet64`, `GSummary64`, `EnsuresGrow64` and `grow_rec64` are the grown run
on amd64 (`GrownReturns`, … of `Janus.Contracts.Stack`), and `MorestackContract64` the contract.
`Janus/Contracts/StackSatAmd64.lean` proves it satisfiable.
-/

namespace Janus.Contracts.StackAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Stack
  Janus.Contracts Janus.Contracts.Stack

/-- The glue address the stub's `CALL` pushed: where `gogo` resumes (`gobuf.pc`). -/
abbrev gluePcOf (s : State) : Nat := s.mem.readLE (s.regs regSP).toNat 8

/-- The function's own stack pointer at the stub (`gobuf.sp`): above the pushed glue address. -/
abbrev fspOf (s : State) : Nat := (s.regs regSP).toNat + 8

/-- The precondition of the `morestack` call in a function's prologue (amd64), at the state
`s_m` reached by the tail's `CALL runtime.morestack_noctxt`:

* `s_m` is at a `morestack` stub; `[RSP]` holds the glue address (`gluePcOf`), `RSP + 8`
  (`fspOf`) is the function's stack pointer, `RSP` 8-aligned;
* the goroutine `g = R14` runs on `[lo, hi)` (`GStack`, no preemption request), above the first
  page, inside the writable stack pools `pool`; `g`'s descriptor lies outside the pools;
* the stack unwinds (`Chain Arch.amd64` from `(gluePcOf, fspOf)`): the runtime throws otherwise;
* the grown stack fits `maxstacksize` (`newstack` throws `stack overflow` otherwise);
* the runtime is ready to allocate the new stack (`H`). -/
structure MorestackPre64 (p : Amd64.Program) (FT : FrameTable) (pool rt : List (Nat × Nat))
    (H : RtReady) (g lo hi : Nat) (s_m : State) : Prop where
  stub : ∃ name, p.stubAt s_m.rip.toNat = some ⟨name, s_m.rip.toNat, .morestack⟩
  greg : (s_m.regs regG).toNat = g
  gstack : GStack s_m.mem g lo hi
  gout : Outside g 24 pool
  low : 4096 ≤ lo ∧ lo ≤ (s_m.regs regSP).toNat ∧ (s_m.regs regSP).toNat + 16 ≤ hi ∧ hi ≤ 2 ^ 48
  aligned : lo % 16 = 0 ∧ hi % 16 = 0 ∧ (s_m.regs regSP).toNat % 8 = 0
  inPool : InRanges lo (hi - lo) pool ∧ PoolOK s_m.mem pool
  chain : ∃ fs, Chain Arch.amd64 FT s_m.mem hi (gluePcOf s_m) (fspOf s_m) none fs
  fits : 2 * (hi - lo) ≤ maxstacksize ∧
    2 * ((hi - fspOf s_m) + FT.maxspd (gluePcOf s_m) + stackGuard) ≤ maxstacksize
  code : FT.CodeOutside pool ∧ FT.Aligned
  ready : H [] g 0 (rtView rt s_m.mem)

/-- `s'` is the resumed state after `newstack` grew the stack of the call state `s` (amd64) from
`[lo, hi)` to `[lo', hi')`; an address `a` of the old stack is now at `a + hi' - hi`:

* the new stack is larger, inside the pools, apart from the old one, at most `maxstacksize`, and
  has room below the resumed `RSP` for the function's largest frame and the guard;
* `gogo` resumed at the glue `[RSP]` with `RSP = RSP + 8 + δ`, `RBP` adjusted (`adjustWord`:
  shifted when it points into the old stack), `RDX = 0`, `R14` kept, `X15 = 0`, the direction
  flag clear, `FS` and `MXCSR`'s control bits kept, every other register and the flags
  unspecified;
* `g.stack`, `g.stackguard0` read `[lo', hi')`, `lo' + stackGuard`;
* memory: the frames of the walk moved (`Moved` along `framesCls` of the `Chain`, from the
  function's stack pointer `RSP + 8`), and outside the pools and `rt` nothing changed;
* the runtime is ready again (`H`). -/
structure Grown64 (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (g lo hi lo' hi' : Nat) (s s' : State) : Prop where
  grows : hi - lo < hi' - lo' ∧ hi' - lo' ≤ maxstacksize ∧ 4096 ≤ lo' ∧ lo' % 16 = 0 ∧
    hi' % 16 = 0 ∧ hi' ≤ 2 ^ 48 ∧ InRanges lo' (hi' - lo') pool ∧ (hi ≤ lo' ∨ hi' ≤ lo)
  room : lo' + stackGuard + FT.maxspd (gluePcOf s) + (hi - fspOf s) ≤ hi'
  pc : s'.rip = retAddrOf s
  sp : s'.regs regSP = BitVec.ofNat 64 (fspOf s + hi' - hi)
  fp : s'.regs regFP = BitVec.ofNat 64 (adjustWord lo hi hi' (s.regs regFP).toNat)
  gkeep : s'.regs regG = s.regs regG
  ctxt : s'.regs regClosure = 0
  zero : s'.xmm xmmZero = 0
  keep : s'.df = false ∧ s'.fsBase = s.fsBase ∧ s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64
  gstack : GStack s'.mem g lo' hi'
  moved : ∀ fs, Chain Arch.amd64 FT s.mem hi (gluePcOf s) (fspOf s) none fs →
    Moved (framesCls Arch.amd64 FT fs) pool lo hi hi' (fspOf s) [] s.mem s'.mem
  frame : MemFrame s.mem s'.mem (pool ++ rt)
  ready : H [] g 0 (rtView rt s'.mem)

/-- **The `morestack` contract** (amd64): from every state at the prologue's `morestack` call
satisfying `MorestackPre64`, the relation `reloc` resumes in a `Grown64` state. The trusted model
of `runtime.morestack_noctxt`/`morestack`/`newstack`/`copystack`/`gogo` on amd64
(`docs/SOUNDNESS.md`); `Janus/Contracts/StackSatAmd64.lean` proves it satisfiable. -/
def MorestackContract64 (p : Amd64.Program) (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) : Prop :=
  ∀ g lo hi s_m, MorestackPre64 p FT pool rt H g lo hi s_m →
    ∃ (s_r : State) (lo' hi' : Nat), reloc s_m s_r ∧ Grown64 FT pool rt H g lo hi lo' hi' s_m s_r

/-! ## The grown run (amd64) -/

/-- `Returns` through any number of `morestack` resumes (amd64 `GrownReturns`). -/
inductive GrownReturns64 (p : Amd64.Program) (reloc : State → State → Prop) :
    State → (State → Prop) → Prop where
  | done {s : State} {post : State → Prop} (h : Returns p s post) : GrownReturns64 p reloc s post
  | grow {n : Nat} {name : String} {s s_m s_r : State} {post : State → Prop}
      (hrun : p.run n s = .ok (.stub name .morestack s_m))
      (hre : reloc s_m s_r) (hrec : GrownReturns64 p reloc s_r post) :
      GrownReturns64 p reloc s post

theorem GrownReturns64.mono {p : Amd64.Program} {reloc : State → State → Prop} {s : State}
    {post post' : State → Prop} (h : GrownReturns64 p reloc s post)
    (hpp : ∀ s', post s' → post' s') : GrownReturns64 p reloc s post' := by
  induction h generalizing post' with
  | done hr => exact .done (hr.mono hpp)
  | grow hrun hre _ ih => exact .grow hrun hre (ih hpp)

theorem GrownReturns64.of_steps {p : Amd64.Program} {reloc : State → State → Prop} {s s' : State}
    {post : State → Prop} {k : Nat} (hs : Amd64.Program.Steps p s k s')
    (h : GrownReturns64 p reloc s' post) : GrownReturns64 p reloc s post := by
  cases h with
  | done hr => exact .done (by obtain ⟨n, o, hr, hq⟩ := hr; exact ⟨k + n, o, by rw [Amd64.Program.run_steps hs]; exact hr, hq⟩)
  | grow hrun hre hrec =>
    exact .grow (n := k + _) (by rw [Amd64.Program.run_steps hs]; exact hrun) hre hrec

/-- A run that reaches a `morestack` stub continues as a grown run from the contract's resume. -/
theorem GrownReturns64.of_reaches_stub {p : Amd64.Program} {reloc : State → State → Prop} {s : State}
    {post : State → Prop}
    (h : Reaches p s (fun o => match o with
      | .stub _ .morestack s_m => ∃ s_r, reloc s_m s_r ∧ GrownReturns64 p reloc s_r post
      | _ => False)) : GrownReturns64 p reloc s post := by
  obtain ⟨n, o, hrun, hq⟩ := h
  cases o with
  | returned => exact hq.elim
  | stub name kind s_m =>
    cases kind with
    | morestack => obtain ⟨s_r, hre, hg⟩ := hq; exact .grow hrun hre hg
    | panic => exact hq.elim
    | external => exact hq.elim

/-- Ordinary steps and stack growths reach a state at `ret` satisfying `Q` (amd64 `GrownRet`). -/
inductive GrownRet64 (p : Amd64.Program) (reloc : State → State → Prop) (ret : W64) :
    State → (State → Prop) → Prop where
  | done {s s' : State} {Q : State → Prop} {k : Nat} (hs : Amd64.Program.Steps p s k s')
      (hpc : s'.rip = ret) (hq : Q s') : GrownRet64 p reloc ret s Q
  | grow {s s_m s_r : State} {Q : State → Prop} {k : Nat} {st : Stub}
      (hs : Amd64.Program.Steps p s k s_m) (hx : s_m.rip.toNat ≠ p.exitAddr)
      (hst : p.stubAt s_m.rip.toNat = some st) (hk : st.kind = .morestack) (hre : reloc s_m s_r)
      (hrec : GrownRet64 p reloc ret s_r Q) : GrownRet64 p reloc ret s Q

/-- A callee contract through stack growths (amd64): from every state at `entry` satisfying
`pre`, the callee reaches its return address `[RSP]` in a state satisfying `post`. -/
def GSummary64 (p : Amd64.Program) (reloc : State → State → Prop) (entry : Nat) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ s, s.rip = BitVec.ofNat 64 entry → pre s → GrownRet64 p reloc (retAddrOf s) s (post s)

namespace GrownRet64

variable {p : Amd64.Program} {reloc : State → State → Prop} {ret : W64}

theorem of_reachesRet {s : State} {Q : State → Prop} (h : ReachesRet p ret s Q) :
    GrownRet64 p reloc ret s Q := by
  obtain ⟨k, s', hs, hpc, hq⟩ := h; exact .done hs hpc hq

theorem of_steps {s s' : State} {Q : State → Prop} {k : Nat} (hs : Amd64.Program.Steps p s k s')
    (h : GrownRet64 p reloc ret s' Q) : GrownRet64 p reloc ret s Q := by
  cases h with
  | done hs' hpc hq => exact .done (hs.trans hs') hpc hq
  | grow hs' hx hst hk hre hrec => exact .grow (hs.trans hs') hx hst hk hre hrec

theorem mono {s : State} {Q Q' : State → Prop} (h : GrownRet64 p reloc ret s Q)
    (hq : ∀ s', Q s' → Q' s') : GrownRet64 p reloc ret s Q' := by
  induction h with
  | done hs hpc h => exact .done hs hpc (hq _ h)
  | grow hs hx hst hk hre _ ih => exact .grow hs hx hst hk hre (ih hq)

theorem bind {r₁ : W64} {s : State} {Q₁ Q₂ : State → Prop} (h : GrownRet64 p reloc r₁ s Q₁)
    (hk : ∀ s', s'.rip = r₁ → Q₁ s' → GrownRet64 p reloc ret s' Q₂) :
    GrownRet64 p reloc ret s Q₂ := by
  induction h with
  | done hs hpc hq => exact of_steps hs (hk _ hpc hq)
  | grow hs hx hst hkd hre _ ih => exact .grow hs hx hst hkd hre (ih hk)

theorem of_reaches_stub {s : State} {Q : State → Prop}
    (h : Reaches p s (fun o => match o with
      | .stub _ .morestack s_m => ∃ s_r, reloc s_m s_r ∧ GrownRet64 p reloc ret s_r Q
      | _ => False)) : GrownRet64 p reloc ret s Q := by
  obtain ⟨n, o, hrun, hq⟩ := h
  cases o with
  | returned => exact hq.elim
  | stub name kind s_m =>
    obtain ⟨j, st, hs, hst, -, hk⟩ := Amd64.GoABI.steps_of_run_stub hrun
    cases kind with
    | morestack =>
      obtain ⟨s_r, hre, hg⟩ := hq
      refine .grow hs ?_ hst hk hre hg
      intro hx
      have h0 := Amd64.Program.run_steps_exit (k := j) hs hx
      have := Amd64.Program.run_ok_unique hrun h0
      cases this
    | panic => exact hq.elim
    | external => exact hq.elim

theorem withExit {r : Nat} {s : State} {Q : State → Prop} (h : GrownRet64 p reloc ret s Q)
    (hf : p.fetch r = none) (hst : ∀ st ∈ p.stubs, st.addr ≠ r) :
    GrownRet64 (p.withExit r) reloc ret s Q := by
  induction h with
  | done hs hpc hq => exact .done (hs.withExit hf) hpc hq
  | @grow s s_m s_r Q k st hs hx hstb hk hre _ ih =>
    refine .grow (hs.withExit hf) ?_ hstb hk hre ih
    intro he
    have hfind : p.stubs.find? (·.addr = s_m.rip.toNat) = some st := hstb
    have hmem : st ∈ p.stubs := List.mem_of_find?_eq_some hfind
    have hpc : st.addr = s_m.rip.toNat := by
      have := List.find?_some hfind; simpa using this
    exact hst st hmem (by rw [hpc]; exact he)

theorem toGrownReturns {r : Nat} {s : State} {Q : State → Prop}
    (h : GrownRet64 (p.withExit r) reloc (BitVec.ofNat 64 r) s Q) (hr : r < 2 ^ 64) :
    GrownReturns64 (p.withExit r) reloc s Q := by
  induction h with
  | done hs hpc hq =>
    refine .done ⟨_, _, Amd64.Program.run_steps_exit hs ?_, hq⟩
    rw [hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]; rfl
  | @grow s s_m s_r Q k st hs hx hst hk hre _ ih =>
    have := Amd64.Program.run_steps_stub hs hx hst
    rw [hk] at this
    exact .grow this hre ih

end GrownRet64

theorem GrownRet64.call {p : Amd64.Program} {reloc : State → State → Prop} {entry : Nat}
    {pre : State → Prop} {post : State → State → Prop} {s : State} {ret : W64} {Q : State → Prop}
    (hsum : GSummary64 p reloc entry pre post) (hpc : s.rip = BitVec.ofNat 64 entry) (hpre : pre s)
    (h : ∀ s', s'.rip = retAddrOf s → post s s' → GrownRet64 p reloc ret s' Q) :
    GrownRet64 p reloc ret s Q :=
  (hsum s hpc hpre).bind h

/-- A roomy summary is a grown summary (no growth happens). -/
theorem GSummary64.of_summary {p : Amd64.Program} {reloc : State → State → Prop} {entry : Nat}
    {pre : State → Prop} {post : State → State → Prop} (h : Summary p entry pre post) :
    GSummary64 p reloc entry pre post :=
  fun s hpc hp => GrownRet64.of_reachesRet (h s hpc hp)

/-- Strong induction for grown summaries (amd64). -/
theorem GSummary64.induction {p : Amd64.Program} {reloc : State → State → Prop} {entry : Nat}
    {pre : State → Prop} {post : State → State → Prop} (μ : State → Nat)
    (step : ∀ n, GSummary64 p reloc entry (fun s => pre s ∧ μ s < n) post →
      GSummary64 p reloc entry (fun s => pre s ∧ μ s = n) post) :
    GSummary64 p reloc entry pre post := by
  have h : ∀ n, GSummary64 p reloc entry (fun s => pre s ∧ μ s < n) post := by
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

/-- Well-founded recursion on `maxstacksize - (hi - lo)` (amd64 `grow_rec`). -/
theorem grow_rec64 {p : Amd64.Program} {reloc : State → State → Prop} {Cfg : State → Nat → Nat → Prop}
    {post : State → Prop}
    (step : ∀ lo hi, (∀ lo₂ hi₂ s₂, hi₂ - lo₂ ≤ maxstacksize → hi - lo < hi₂ - lo₂ →
          Cfg s₂ lo₂ hi₂ → GrownReturns64 p reloc s₂ post) →
        ∀ s, Cfg s lo hi → hi - lo ≤ maxstacksize → GrownReturns64 p reloc s post) :
    ∀ lo hi s, Cfg s lo hi → hi - lo ≤ maxstacksize → GrownReturns64 p reloc s post := by
  intro lo hi
  have key : ∀ d lo hi, maxstacksize - (hi - lo) ≤ d → ∀ s, Cfg s lo hi → hi - lo ≤ maxstacksize →
      GrownReturns64 p reloc s post := by
    intro d
    induction d with
    | zero =>
      intro lo hi hd s hcfg hlt
      exact step lo hi (fun lo₂ hi₂ s₂ _ hgt _ => absurd hd (by omega)) s hcfg hlt
    | succ d ih =>
      intro lo hi hd s hcfg hlt
      exact step lo hi (fun lo₂ hi₂ s₂ hlt₂ hgt hcfg₂ => ih lo₂ hi₂ (by omega) s₂ hcfg₂ hlt₂) s hcfg hlt
  exact fun s hcfg hlt => key (maxstacksize - (hi - lo)) lo hi (Nat.le_refl _) s hcfg hlt

/-- The grown contract of a Go function on amd64, under the `morestack` contract `reloc`. -/
def EnsuresGrow64 (p : Amd64.Program) (reloc : State → State → Prop) (entry : Nat) (args : List W64)
    (pre : State → Prop) (post : State → State → Prop) : Prop :=
  ∀ ret, RetAddr p ret → ∀ s, CallSetup (p.withExit ret) entry args s → pre s →
    GrownReturns64 (p.withExit ret) reloc s (fun s' => post s s')

/-! ## amd64 frames keep their words above their stack pointer -/

/-- **amd64 frames keep their words above their stack pointer**, for an aligned table whose
locals maps fit inside the frame whenever `getStackMap` reads them (a frame of at most 8 bytes,
the pushed `RBP` only, has none read: `varp = sp`), and which has no stack objects. -/
theorem _root_.Janus.Spec.Stack.FrameTable.inFrame_amd64 (FT : FrameTable) (hal : FT.Aligned)
    (hfit : ∀ pc, FT.spdelta pc ≤ 8 ∨ 8 * (FT.locals pc).length + 8 ≤ FT.spdelta pc)
    (ho : ∀ pc, FT.objs pc = []) : FT.InFrame Arch.amd64 := by
  intro pc sp a h
  have h8 := hal pc
  have hb : ∀ (b : Int) (bs : List Bool), (a : Int) < b → bitsAt b bs a = false := by
    intro b bs hlt; simp only [bitsAt]; rw [decide_eq_false (by omega)]; rfl
  have hfp : Arch.amd64.fp FT pc sp = sp + FT.spdelta pc + 8 := rfl
  have harg : Arch.amd64.argp (sp + FT.spdelta pc + 8) = sp + FT.spdelta pc + 8 := rfl
  have hml : Arch.amd64.minLocals = 0 := rfl
  have ha : bitsAt ((sp + FT.spdelta pc + 8 : Nat) : Int) (FT.args pc) a = false := hb _ _ (by omega)
  by_cases hz : FT.spdelta pc = 0
  · have hv : Arch.amd64.varp sp (sp + FT.spdelta pc + 8) = sp := by simp [Arch.varp, hz]
    simp only [frameCls, hfp, hv, harg, hml, ho, List.any_nil, Bool.or_false, ha]
    have e1 : (a == sp) = false := by simp; omega
    have e2 : decide (0 + sp < sp) = false := decide_eq_false (by omega)
    rw [e1, e2]; simp
  · have hv : Arch.amd64.varp sp (sp + FT.spdelta pc + 8) = sp + FT.spdelta pc - 8 := by
      simp only [Arch.varp]; split <;> omega
    simp only [frameCls, hfp, hv, harg, hml, ho, List.any_nil, Bool.or_false, ha]
    have e1 : (a == sp + FT.spdelta pc - 8) = false := by simp; omega
    rw [e1, Bool.and_false, Bool.false_or]
    rcases hfit pc with h1 | h1
    · rw [decide_eq_false (by omega)]; rfl
    · rw [hb (((sp + FT.spdelta pc - 8 : Nat) : Int) - 8 * ((FT.locals pc).length : Int)) _ (by omega),
        Bool.and_false]

/-- A record's frames fit its locals maps on amd64, and it has no stack objects (checked by
evaluation on the binary's record). -/
def _root_.Janus.Spec.Stack.FuncRec.Fits64 (r : FuncRec) : Prop :=
  r.objs = [] ∧ ∀ x ∈ r.pcsp, x.2.toNat % 8 = 0 ∧ (x.2.toNat ≤ 8 ∨ 8 * r.maxLocals + 8 ≤ x.2.toNat)

/-- The table built from fitting records and an `extra` table without frames or stack objects is
aligned and satisfies `InFrame` on amd64. -/
theorem _root_.Janus.Spec.Stack.FrameTable.ofRecs_laws_amd64 (rs : List FuncRec) (extra : FrameTable)
    (hr : ∀ r ∈ rs, r.Fits64) (hsd : ∀ pc, extra.spdelta pc = 0) (ho : ∀ pc, extra.objs pc = []) :
    (FrameTable.ofRecs rs extra).Aligned ∧ (FrameTable.ofRecs rs extra).InFrame Arch.amd64 := by
  have hv : ∀ r ∈ rs, ∀ pc, r.spdeltaAt pc % 8 = 0 ∧
      (r.spdeltaAt pc ≤ 8 ∨ 8 * (r.localsAt pc).length + 8 ≤ r.spdeltaAt pc) := by
    intro r hm pc
    have hl' := r.length_localsAt pc
    unfold FuncRec.spdeltaAt
    rcases runAt_mem (rs := r.pcsp) pc with h | ⟨x, hx, h⟩
    · rw [h]; exact ⟨rfl, .inl (by decide)⟩
    · rw [h]
      obtain ⟨h1, h2⟩ := (hr r hm).2 x hx
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · exact .inl h2
      · exact .inr (by omega)
  have hal' : (FrameTable.ofRecs rs extra).Aligned := by
    intro pc
    rcases FrameTable.ofRecs_spec rs extra pc with ⟨r, hm, h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact (hv r hm pc).1
    · rw [h1, hsd]
  refine ⟨hal', FrameTable.inFrame_amd64 _ hal' (fun pc => ?_) (fun pc => ?_)⟩
  · rcases FrameTable.ofRecs_spec rs extra pc with ⟨r, hm, h1, h2, -⟩ | ⟨h1, h2, -⟩
    · rw [h1, h2]; exact (hv r hm pc).2
    · rw [h1, hsd]; left; decide
  · rcases FrameTable.ofRecs_spec rs extra pc with ⟨r, hm, -, -, -, h4⟩ | ⟨-, -, -, h4⟩
    · rw [h4]; exact (hr r hm).1
    · rw [h4]; exact ho pc

end Janus.Contracts.StackAmd64
