import Lean
import Janus.Arm64.MemoryLemmas

/-!
# ISA-independent parts of the proof automation

Shared by `janus_run` (arm64, `Janus.Tactic.Core`) and `janus64_run` (amd64,
`Janus.Amd64.Tactic`). Nothing here is part of the trusted base: these are tactic-time helpers.

* **Status and budget.** Each run keeps a `Status` (the pc, instruction and phase of the step in
  progress) in an `IO.Ref`. `guardStep` turns a heartbeat timeout, `simp`'s step limit or any
  other failure inside a step into an error that names the pc, the instruction and the phase,
  so a run never fails with a bare "deterministic timeout". `withBudget` limits the heartbeats
  of a whole run (`janus_run (budget := N)`, `N` in thousands, like `maxHeartbeats`).
* **Stuck diagnostics.** `explainStuck` analyses the term an instruction could not be evaluated
  past: memory accesses whose `accessible` side condition failed (with the `accessible` facts
  about the same memory and which of the two range inequalities `omega` could not prove),
  reads over writes whose aliasing is unknown, addresses that may wrap around `2^64`, and
  `match`es on values that are not constructors (e.g. undefined or unknown flags).
* **Simp cache.** `StepCache` keeps the `simp` cache and the simp context between the steps of
  one run, keyed by the local context: a symbolic state is mostly made of values that earlier
  steps already simplified, and re-simplifying them on every step made the cost of a step grow
  with the length of the run.
* `casesBound` (`janus_cases`, `janus64_cases`) and `addReadLEBounds` (`janus_arith`,
  `janus64_arith`).
-/

namespace Janus

/-- `[a, a+n)` lies outside every range `[lo, hi)` of `rs`. -/
def Outside (a n : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | (lo, hi) :: rs => (a + n ≤ lo ∨ hi ≤ a) ∧ Outside a n rs

@[simp] theorem outside_nil (a n : Nat) : Outside a n [] = True := rfl
@[simp] theorem outside_cons (a n lo hi : Nat) (rs : List (Nat × Nat)) :
    Outside a n ((lo, hi) :: rs) = ((a + n ≤ lo ∨ hi ≤ a) ∧ Outside a n rs) := rfl

/-- `m'` is `m` changed at most inside the ranges `rs` (`[lo, hi)` each): every read outside
them agrees, and the regions (what is accessible) are the same. This is the memory part of a
callee `Summary` whose callee writes its stack frame, e.g.
`MemFrame s.mem m [(s.sp.toNat - 40, s.sp.toNat - 24)]` for a frame push of `X29`/`X30`
(several ranges when the callee also spills into its caller's frame). In the caller,
`janus_run`/`janus64_run` use a hypothesis `hf : MemFrame m₀ m rs` as the rewrite rules
`hf.readLE` (a read whose range is outside `rs`, side condition by `omega`) and
`hf.accessible`. -/
structure MemFrame (m m' : Janus.Arm64.Memory) (rs : List (Nat × Nat)) : Prop where
  readLE : ∀ a n, Outside a n rs → m'.readLE a n = m.readLE a n
  accessible : ∀ a n w, m'.accessible a n w = m.accessible a n w

@[simp] theorem outside_append (a n : Nat) (rs rs' : List (Nat × Nat)) :
    Outside a n (rs ++ rs') = (Outside a n rs ∧ Outside a n rs') := by
  induction rs with
  | nil => simp
  | cons r rs ih => obtain ⟨lo, hi⟩ := r; simp [ih, and_assoc]

/-- A sub-range of a range outside `rs` is outside `rs` (for a list `rs` that is a variable,
e.g. a caller-declared list of runtime-owned ranges). -/
theorem Outside.of_sub {b k a n : Nat} {rs : List (Nat × Nat)} (h : Outside b k rs) (h1 : b ≤ a)
    (h2 : a + n ≤ b + k) : Outside a n rs := by
  induction rs with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨lo, hi⟩ := r
    simp only [outside_cons] at h ⊢
    exact ⟨by omega, ih h.2⟩

/-- `[a, a+n)` and `[b, b+k)` do not overlap. The same as `Spec.Disjoint`, but a separate
definition that `omega` does not unfold: a precondition with many disjointness facts states
them as `Apart`, so that `omega` does not case-split on all of them in every side condition;
the dischargers use them one at a time (`janus_apart`). -/
def Apart (a n b k : Nat) : Prop := a + n ≤ b ∨ b + k ≤ a

theorem Apart.symm {a n b k : Nat} (h : Apart a n b k) : Apart b k a n := by
  unfold Apart at *; omega

/-- Shrinking either range keeps them apart. -/
theorem Apart.mono {a n n' b k k' : Nat} (h : Apart a n b k) (h1 : n' ≤ n) (h2 : k' ≤ k) :
    Apart a n' b k' := by
  unfold Apart at *; omega

/-- `[a, a+n)` lies inside one of the ranges `[lo, hi)` of `rs`. -/
def InRanges (a n : Nat) (rs : List (Nat × Nat)) : Prop := ∃ r ∈ rs, r.1 ≤ a ∧ a + n ≤ r.2

theorem InRanges.append_left {a n : Nat} {rs : List (Nat × Nat)} (h : InRanges a n rs)
    (rs' : List (Nat × Nat)) : InRanges a n (rs ++ rs') := by
  obtain ⟨r, hr, h1, h2⟩ := h; exact ⟨r, List.mem_append_left _ hr, h1, h2⟩

theorem InRanges.append_right {a n : Nat} {rs' : List (Nat × Nat)} (rs : List (Nat × Nat))
    (h : InRanges a n rs') : InRanges a n (rs ++ rs') := by
  obtain ⟨r, hr, h1, h2⟩ := h; exact ⟨r, List.mem_append_right _ hr, h1, h2⟩

theorem InRanges.of_subset {a n : Nat} {rs rs' : List (Nat × Nat)} (h : InRanges a n rs)
    (sub : ∀ r, r ∈ rs → r ∈ rs') : InRanges a n rs' := by
  obtain ⟨r, hr, h1, h2⟩ := h; exact ⟨r, sub r hr, h1, h2⟩

theorem InRanges.sub {a n b k : Nat} {rs : List (Nat × Nat)} (h : InRanges b k rs) (h1 : b ≤ a)
    (h2 : a + n ≤ b + k) : InRanges a n rs := by
  obtain ⟨r, hr, h3, h4⟩ := h; exact ⟨r, hr, by omega, by omega⟩

namespace MemFrame

variable {m m' m'' : Janus.Arm64.Memory} {rs : List (Nat × Nat)}

theorem refl (m : Janus.Arm64.Memory) (rs : List (Nat × Nat)) : MemFrame m m rs :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem outside_mem {a n : Nat} {rs : List (Nat × Nat)} (h : Outside a n rs) {r : Nat × Nat}
    (hr : r ∈ rs) : a + n ≤ r.1 ∨ r.2 ≤ a := by
  induction rs with
  | nil => cases hr
  | cons r' rs ih =>
    obtain ⟨lo, hi⟩ := r'
    simp only [outside_cons] at h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h.1
    · exact ih h.2 hr

/-- A store inside one of the ranges keeps the frame. -/
theorem writeLE (h : MemFrame m m' rs) {a k : Nat} (v : Nat) {r : Nat × Nat} (hr : r ∈ rs)
    (h1 : r.1 ≤ a) (h2 : a + k ≤ r.2) : MemFrame m (m'.writeLE a k v) rs :=
  ⟨fun b n hb => by
    have := outside_mem hb hr
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h.readLE b n hb,
   fun b n w => by rw [Janus.Arm64.Memory.accessible_writeLE]; exact h.accessible b n w⟩

/-- A store inside the ranges, known from an `InRanges` fact (e.g. an object a contract placed in
the runtime-owned ranges), keeps the frame. -/
theorem writeLE_inRanges (h : MemFrame m m' rs) {a k : Nat} (v : Nat) (hin : InRanges a k rs) :
    MemFrame m (m'.writeLE a k v) rs := by
  obtain ⟨r, hr, h1, h2⟩ := hin; exact h.writeLE v hr h1 h2

/-- `m.writeLE a k v` is a frame of `m` when the store is inside one of the ranges. -/
theorem of_writeLE (m : Janus.Arm64.Memory) {a k : Nat} (v : Nat) {r : Nat × Nat} (hr : r ∈ rs)
    (h1 : r.1 ≤ a) (h2 : a + k ≤ r.2) : MemFrame m (m.writeLE a k v) rs :=
  (refl m rs).writeLE v hr h1 h2

/-- Compose two frames: the result's ranges must cover both (`sub`). -/
theorem trans {rs' rs'' : List (Nat × Nat)} (h : MemFrame m m' rs) (h' : MemFrame m' m'' rs')
    (sub : ∀ a n, Outside a n rs'' → Outside a n rs ∧ Outside a n rs') : MemFrame m m'' rs'' :=
  ⟨fun b n hb => by rw [h'.readLE b n (sub b n hb).2, h.readLE b n (sub b n hb).1],
   fun b n w => by rw [h'.accessible, h.accessible]⟩

/-- Change the ranges (the new ones must cover the old ones). -/
theorem mono {rs' : List (Nat × Nat)} (h : MemFrame m m' rs)
    (sub : ∀ a n, Outside a n rs' → Outside a n rs) : MemFrame m m' rs' :=
  ⟨fun b n hb => h.readLE b n (sub b n hb), h.accessible⟩

end MemFrame

/-- A range inside `rs` and a range outside `rs` are `Apart` (the form the dischargers use one
fact at a time). -/
theorem InRanges.apart {a n b k : Nat} {rs : List (Nat × Nat)} (hin : InRanges a n rs)
    (hout : Outside b k rs) : Apart b k a n := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem hout hr
  unfold Apart; omega

theorem InRanges.cons_head {a n lo hi : Nat} (rs : List (Nat × Nat)) (h1 : lo ≤ a) (h2 : a + n ≤ hi) :
    InRanges a n ((lo, hi) :: rs) := ⟨(lo, hi), List.mem_cons_self .., h1, h2⟩

theorem InRanges.cons_tail {a n : Nat} {rs : List (Nat × Nat)} (r : Nat × Nat) (h : InRanges a n rs) :
    InRanges a n (r :: rs) := by
  obtain ⟨r', hr, h1, h2⟩ := h; exact ⟨r', List.mem_cons_of_mem _ hr, h1, h2⟩

/-- `m'` agrees with `m` on the objects of the **live set** `L` (ranges `[lo, hi)`), except where
they overlap the ranges `ws` the callee writes on purpose (e.g. the destination of a copy): every
read inside one live object and outside `ws` is the same. This is the memory part of a live
runtime contract (`Janus.Contracts.Live`): an allocation or a write barrier changes runtime
memory, but not the objects the program holds. In the caller, `janus_run`/`janus64_run` use a
hypothesis `hl : LiveFrame m₀ m L ws` as the rewrite rule `hl.readLE` (side conditions
`InRanges a n L` and `Outside a n ws`). -/
structure LiveFrame (m m' : Janus.Arm64.Memory) (L ws : List (Nat × Nat)) : Prop where
  readLE : ∀ a n, InRanges a n L → Outside a n ws → m'.readLE a n = m.readLE a n

namespace LiveFrame

variable {m m' m'' : Janus.Arm64.Memory} {L ws : List (Nat × Nat)}

theorem refl (m : Janus.Arm64.Memory) (L ws : List (Nat × Nat)) : LiveFrame m m L ws :=
  ⟨fun _ _ _ _ => rfl⟩

/-- With no written ranges: a read inside a live object is unchanged (the form of the rewrite
rule, without the trivial `Outside a n []` side condition). -/
theorem readLE_nil (h : LiveFrame m m' L []) (a n : Nat) (hin : InRanges a n L) :
    m'.readLE a n = m.readLE a n := h.readLE a n hin trivial

/-- Two calls in a row: the second keeps a live set that contains the first's (`sub`). -/
theorem trans {L' : List (Nat × Nat)} (h : LiveFrame m m' L ws) (h' : LiveFrame m' m'' L' ws)
    (sub : ∀ a n, InRanges a n L → InRanges a n L') : LiveFrame m m'' L ws :=
  ⟨fun a n hin hout => by rw [h'.readLE a n (sub a n hin) hout, h.readLE a n hin hout]⟩

/-- A store outside the live objects (or inside `ws`) keeps the frame. -/
theorem writeLE (h : LiveFrame m m' L ws) {a k : Nat} (v : Nat) (hout : Outside a k L) :
    LiveFrame m (m'.writeLE a k v) L ws :=
  ⟨fun b n hin hw => by
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := MemFrame.outside_mem hout hr
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact h.readLE b n ⟨r, hr, h1, h2⟩ hw⟩

end LiveFrame
end Janus

namespace Janus.Tactic.Common

open Lean Meta Elab Tactic

register_option janus.aliasInfo : Bool := {
  defValue := true
  descr := "janus_run/janus64_run: report reads over stores whose aliasing is unknown when \
    they are left in the remaining goals (an information message)"
}

register_option janus.merge : Bool := {
  defValue := false
  descr := "janus_run/janus64_run: merge paths that reach the same pc with the same state \
    (the branch conditions they do not share are dropped; see `Common.pickMerged`)"
}

/-- Every identifier inside a syntax tree, in order. -/
partial def collectIdents (stx : Syntax) : Array Syntax :=
  if stx.isIdent then #[stx] else stx.getArgs.foldl (fun acc a => acc ++ collectIdents a) #[]

/-- Close an arithmetic goal by `omega` using one `Apart` hypothesis at a time: for each
`h : Apart a n b k` of the context, `omega` in both cases of `h`. -/
partial def arithAtoms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``HMul.hMul 6 ||
      e.isAppOfArity ``HDiv.hDiv 6 || e.isAppOfArity ``HMod.hMod 6 then
    arithAtoms (e.getArg! 5) (arithAtoms (e.getArg! 4) acc)
  else if e.isAppOfArity ``OfNat.ofNat 3 || e.isRawNatLit then acc
  else if e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``LT.lt 4 || e.isAppOfArity ``Eq 3 then
    arithAtoms (e.getArg! (e.getAppNumArgs - 1)) (arithAtoms (e.getArg! (e.getAppNumArgs - 2)) acc)
  else if e.isAppOfArity ``Or 2 || e.isAppOfArity ``And 2 then
    arithAtoms (e.getArg! 1) (arithAtoms (e.getArg! 0) acc)
  else if acc.contains e then acc else acc.push e

def omegaApart (g : MVarId) : TacticM Bool := g.withContext do
  let gty ← instantiateMVars (← g.getType)
  -- only disjunctions (the read-over-write and frame side conditions) are worth it
  unless gty.consumeMData.isAppOfArity ``Or 2 do return false
  let goalAtoms := arithAtoms gty
  -- relevant `Apart` facts: every atom of their two start addresses occurs in the goal
  let mut full := #[]
  let part : Array (FVarId × Array Expr) := #[]
  let mut aparts := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Janus.Apart 4 then
      aparts := aparts.push d.fvarId
      let hAtoms := arithAtoms (ty.getArg! 2) (arithAtoms (ty.getArg! 0))
      if hAtoms.all goalAtoms.contains then full := full.push (d.fvarId, hAtoms)
  if full.isEmpty && part.isEmpty then return false
  -- the arithmetic hypotheses and their atoms
  let mut hyps := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || aparts.contains d.fvarId then continue
    let ty ← instantiateMVars d.type
    if ← isProp ty then hyps := hyps.push (d.fvarId, arithAtoms ty)
  for (fv, _) in full ++ part do
    let aty ← instantiateMVars (← fv.getType)
    -- the atoms of the two ranges, lengths included
    let hAtoms := arithAtoms (aty.getArg! 3) (arithAtoms (aty.getArg! 2)
      (arithAtoms (aty.getArg! 1) (arithAtoms (aty.getArg! 0))))
    let mut atoms := goalAtoms ++ hAtoms
    -- when a range has atoms the goal does not (an object's symbolic size), two rounds of the
    -- hypotheses about them (e.g. `8·n ≤ round`, `0 < n`)
    if !(hAtoms.all goalAtoms.contains) then
      for _ in [0:2] do
        let mut more := #[]
        for (_, ha) in hyps do
          if ha.size ≤ 4 && ha.any (fun a => atoms.contains a && !goalAtoms.contains a && a.nat?.isNone) then
            more := more ++ ha
        atoms := atoms ++ more
    -- keep only the arithmetic facts about these atoms, so that each `omega` is small
    let mut toClear := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || d.fvarId == fv then continue
      if aparts.contains d.fvarId then toClear := toClear.push d.fvarId; continue
      let ty ← instantiateMVars d.type
      if ← isProp ty then
        unless (arithAtoms ty).all atoms.contains do toClear := toClear.push d.fvarId
    let saved' ← saveState
    try
      let g' ← try g.tryClearMany toClear catch _ => pure g
      let h ← Term.exprToSyntax (mkFVar fv)
      let gs ← Tactic.run g' <| withoutRecover (evalTactic (← `(tactic|
        (have h' : _ := $h
         unfold Janus.Apart at h'
         rcases h' with h' | h' <;> omega))))
      if gs.isEmpty then return true
      saved'.restore
    catch _ => saved'.restore
  return false

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-! ## Status of the step in progress -/

structure Status where
  /-- The pc of the step in progress. -/
  pc : Option Nat := none
  /-- `function+0xoff` of the pc. -/
  sym : Option String := none
  /-- The instruction at the pc, disassembled. -/
  instr : Option String := none
  /-- What the step is doing. -/
  phase : String := "starting"
  /-- Number of instructions executed so far by this run. -/
  steps : Nat := 0
  /-- Reads over stores whose aliasing `simp` could not resolve, with where they appeared. -/
  aliases : Array (Expr × MessageData) := #[]
  deriving Inhabited

/-- The location of a step, for messages: `pc 0x… (f+0x…): instr`. -/
def Status.where_ (st : Status) : MessageData :=
  match st.pc with
  | none => m!"before the first instruction"
  | some pc =>
    let sym := match st.sym with | some s => s!" ({s})" | none => ""
    let ins := match st.instr with | some i => s!": {i}" | none => ""
    m!"at pc {hex pc}{sym}{ins}"

def setPhase (ref : IO.Ref Status) (phase : String) : MetaM Unit :=
  ref.modify fun st => { st with phase }

/-- The symbol `name+0xoff` of `pc` given the segments `(name, base, size)`. -/
def symOf (segs : List (String × Nat × Nat)) (pc : Nat) : Option String :=
  segs.findSome? fun (n, b, sz) =>
    if b ≤ pc ∧ pc < b + sz then some (if pc = b then n else s!"{n}+{hex (pc - b)}") else none

/-- Heartbeats used since the start of the current budget. -/
def heartbeatsUsed : CoreM Nat := do
  return (← IO.getNumHeartbeats) - (← read).initHeartbeats

/-- Run `k` with a budget of `n * 1000` heartbeats counted from now (`none`: the ambient
`maxHeartbeats`). -/
def withBudget (n? : Option Nat) (k : TacticM α) : TacticM α := do
  match n? with
  | none => k
  | some n =>
    withCurrHeartbeats <|
      withTheReader Core.Context (fun c => { c with maxHeartbeats := n * 1000 }) k

/-- Run one step of `tac`; turn a heartbeat timeout or any other exception into an error that
says where execution was and what it was doing. Errors that are already diagnostics (they start
with `tac`) are passed through. -/
def guardStep (tac : String) (ref : IO.Ref Status) (budget? : Option Nat) (k : TacticM α) :
    TacticM α := do
  tryCatchRuntimeEx k fun ex => do
    let st ← ref.get
    if ex.isMaxHeartbeat then
      let lim := (← Lean.getMaxHeartbeats) / 1000
      let how := match budget? with
        | some n => m!"The limit was the budget of this run, `{tac} (budget := {n})` (thousands of \
            heartbeats): raise it"
        | none => m!"The limit was `maxHeartbeats` ({lim}), which covers the whole declaration: \
            raise it with `set_option maxHeartbeats N in` before the theorem (or give this run \
            its own budget with `{tac} (budget := N)`)"
      let msg := m!"{tac}: heartbeat budget exceeded {st.where_} while {st.phase}, after \
        {st.steps} instructions.\n{how}, or stop earlier (`until [...]`, a callee `Summary`) and \
        split the proof."
      if budget?.isSome then throwError msg
      -- the declaration's own limit is used up: anything after this point would fail with a
      -- bare timeout, so report the diagnostic now
      logError msg
      throwAbortTactic
    if ex.isInterrupt || ex.isRuntime then throw ex
    let msg ← ex.toMessageData.toString
    if msg.startsWith tac then throw ex
    throwError m!"{tac}: failed {st.where_} while {st.phase}:\n{ex.toMessageData}"

/-! ## Stuck diagnostics -/

/-- What prevented an instruction from evaluating. -/
inductive Obstacle where
  /-- `fn m a n …`: a checked access of `n` bytes at `a` (`write`: needs a writable region). -/
  | access (fn : Name) (m a n : Expr) (write : Bool)
  /-- `(m.writeLE a n v).readLE b k`: overlap of the read with the write is unknown. -/
  | alias (m a n b k : Expr)
  /-- A `match` (or `if`) on a value that is not a constructor. -/
  | stuckMatch (fn : Name) (discrs : Array Expr)
  deriving Inhabited

/-- Collect the obstacles in `e`. `accessFns` lists the checked memory operations of the ISA as
`(name, isWrite)`, each of the form `fn m addr size …`. -/
partial def obstacles (accessFns : List (Name × Bool)) (e : Expr) : MetaM (Array Obstacle) := do
  let env ← getEnv
  let rec go (e : Expr) (acc : Array Obstacle) : MetaM (Array Obstacle) := do
    let acc ← match e with
      | .app .. =>
        let fn := e.getAppFn
        let args := e.getAppArgs
        let mut acc := acc
        if let some c := fn.constName? then
          if let some (_, w) := accessFns.find? (·.1 == c) then
            if args.size ≥ 3 then acc := acc.push (.access c args[0]! args[1]! args[2]! w)
          if c == ``Janus.Arm64.Memory.readLE && args.size == 3 then
            let m := args[0]!
            if m.isAppOfArity ``Janus.Arm64.Memory.writeLE 4 then
              acc := acc.push (.alias (m.getArg! 0) (m.getArg! 1) (m.getArg! 2) args[1]! args[2]!)
          if let some info := isMatcherAppCore? env e then
            let discrs := args.extract info.getFirstDiscrPos (info.getFirstDiscrPos + info.numDiscrs)
            let mut ctor := true
            for d in discrs do
              if (← isConstructorApp? d.consumeMData).isNone && !d.isRawNatLit && d.nat?.isNone then
                ctor := false
            unless ctor do acc := acc.push (.stuckMatch c discrs)
        for a in args do acc ← go a acc
        pure acc
      | .mdata _ b => go b acc
      | .lam _ t b _ | .forallE _ t b _ => do go b (← go t acc)
      | .letE _ t v b _ => do go b (← go v (← go t acc))
      | .proj _ _ b => go b acc
      | _ => pure acc
    return acc
  go e #[]

/-- Try to prove the proposition `p` by `omega` (restoring the state). -/
def omegaProves (p : Expr) : TacticM Bool := do
  let saved ← saveState
  try
    let g ← mkFreshExprMVar p
    let gs ← Tactic.run g.mvarId! (evalTactic (← `(tactic| omega)))
    saved.restore
    return gs.isEmpty
  catch _ => saved.restore; return false

/-- Strip `writeLE`s off a memory term (they do not change accessibility). -/
partial def stripWrites (m : Expr) : Expr :=
  if m.isAppOfArity ``Janus.Arm64.Memory.writeLE 4 then stripWrites (m.getArg! 0) else m

/-- A natural-number term that contains `x % 2^64` (an address that may wrap). -/
partial def findWrap (e : Expr) : Option Expr :=
  if e.isAppOfArity ``HMod.hMod 6 && (e.getArg! 5).nat? == some 18446744073709551616 then
    some (e.getArg! 4)
  else match e with
    | .app f a => (findWrap f).orElse fun _ => findWrap a
    | .mdata _ b => findWrap b
    | _ => none

/-- `e` on one line, in backticks (for messages). -/
def inlS (e : Expr) : MetaM String := do
  let f ← ppExpr (← instantiateMVars e)
  return " ".intercalate ((f.pretty 100000).splitOn "\n" |>.map String.trimAscii |>.map toString)

/-- `e` on one line, in backticks (for messages). -/
def inl (e : Expr) : MetaM MessageData := do
  return m!"`{← inlS e}`"

/-- "a"/"an" before a number of bytes. -/
def art (n : Expr) : String :=
  match n.nat? <|> n.rawNatLit? with
  | some k => if (toString k).startsWith "8" || k == 11 || k == 18 then "an" else "a"
  | none => "a"

/-- Number of `writeLE`s on top of a memory term. -/
partial def countWrites (m : Expr) : Nat :=
  if m.isAppOfArity ``Janus.Arm64.Memory.writeLE 4 then countWrites (m.getArg! 0) + 1 else 0

/-- Explain one obstacle: the failing side condition and the hypotheses that would discharge
it. -/
def explainObstacle (o : Obstacle) : TacticM MessageData := do
  match o with
  | .access fn m a n w =>
    let m0 := stripWrites m
    let goal ← mkEq (mkAppN (mkConst ``Janus.Arm64.Memory.accessible) #[m0, a, n, toExpr w])
      (mkConst ``Bool.true)
    let kind := if w then "write" else "read"
    let nw := countWrites m
    let mut facts : Array MessageData := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, l, _) := ty.eq? | continue
      unless l.isAppOfArity ``Janus.Arm64.Memory.accessible 4 do continue
      unless ← withReducible (isDefEq (stripWrites (l.getArg! 0)) m0) do continue
      let b := l.getArg! 1
      let k := l.getArg! 2
      let w' := l.getArg! 3
      let lo ← mkAppM ``LE.le #[b, a]
      let hi ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[a, n], ← mkAppM ``HAdd.hAdd #[b, k]]
      let okLo ← omegaProves lo
      let okHi ← omegaProves hi
      let okW := !w || w'.isConstOf ``Bool.true
      let mut why : Array MessageData := #[]
      unless okLo do why := why.push m!"{← inl lo} is not provable by omega"
      unless okHi do why := why.push m!"{← inl hi} is not provable by omega"
      unless okW do why := why.push m!"the region is only known to be readable"
      let status := if why.isEmpty then m!"covers the access" else MessageData.joinSep why.toList "; "
      facts := facts.push m!"  {d.userName} : {← inl ty}\n      {status}"
    let wrap ← match findWrap a with
      | some x =>
        -- `(2^64 - k) + y` is `y - k`: it does not wrap when `k ≤ y`
        let neg? : Option (Nat × Expr) := match x.getAppFnArgs with
          | (``HAdd.hAdd, #[_, _, _, _, c, y]) =>
            match c.nat? with
            | some c => if c ≥ 2 ^ 63 && c < 2 ^ 64 then some (2 ^ 64 - c, y) else none
            | none => none
          | _ => none
        match neg? with
        | some (k, y) =>
          pure m!"\nThe address is {← inl y} - {k} computed modulo 2^64: it could not be shown \
            not to wrap below zero. This needs `{k} ≤ {← inlS y}` (for the stack: a larger \
            `below` in `StackOK`/`StackWritable`, which covers `[SP - below, SP)`)."
        | none =>
          pure m!"\nThe address contains {← inl x} modulo 2^64: it could not be shown not to wrap \
            around. Add a bound such as `{← inlS x} < 2^64` (`Ptr`, `Buffer`, `StackOK` and \
            `StackWritable` give `… ≤ 2^48`)."
      | none => pure m!""
    let m0S ← inl m0
    let factsMsg := if facts.isEmpty then
        m!"There is no `accessible` hypothesis about {m0S} in the context."
      else m!"The `accessible` hypotheses about {m0S}:\n{MessageData.joinSep facts.toList "\n"}"
    let writes := if nw = 0 then m!"" else m!" (the memory is {m0S} after {nw} stores, which do \
      not change what is accessible)"
    let aS ← inlS a
    return m!"cannot prove that the {n}-byte {kind} at {← inl a} is allowed{writes}:\
      {indentExpr goal}\n{factsMsg}{wrap}\nIt is discharged by a hypothesis \
      `{← inlS m0}.accessible b k w = true` with `b ≤ {aS}` and `{aS} + {n} ≤ b + k` provable by \
      omega{if w then " and `w = true`" else ""}: \
      state the region in the precondition (`Ptr`, `Buffer`, `StackOK`, `StackWritable`) together \
      with the arithmetic facts that bound the address (e.g. `i.toNat < len.toNat`)."
  | .alias _ a n b k =>
    let disj ← mkAppM ``Or #[← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[b, k], a],
      ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[a, n], b]]
    return m!"{art k} {k}-byte read at {← inl b} follows {art n} {n}-byte store at {← inl a}, and it is \
      unknown whether they overlap. omega needs either\n  {← inl disj}   (disjoint), or\n  \
      {← inl (← mkEq a b)}   (the same address){if n != k then m!" with the same width" else m!""}.\n\
      Add `Disjoint`/aliasing facts to the precondition, or split on the aliasing before running \
      (`rcases h with rfl | h`)."
  | .stuckMatch fn discrs =>
    let ds ← discrs.toList.mapM fun d => (inl d : MetaM MessageData)
    return m!"a case split ({fn}) on {MessageData.joinSep ds ", "} cannot be decided: the value \
      is not a constructor. If it is a flag or a condition, the flags are unknown at this point \
      (add an equation for them, or keep the comparison that sets them in the same run); on \
      amd64 a `none` flag is architecturally undefined and reading it faults."

/-- The message for an instruction that `simp` could not evaluate to `.ok s'` or a branch. -/
def explainStuck (tac : String) (st : Status) (accessFns : List (Name × Bool)) (r : Expr) :
    TacticM MessageData := do
  let obs ← obstacles accessFns r
  -- report each access/alias once (simp leaves several copies in `match` arms)
  let mut seen : Array Obstacle := #[]
  for o in obs do
    let dup ← seen.anyM fun o' => match o, o' with
      | .access _ _ a n _, .access _ _ a' n' _ => pure (a == a' && n == n')
      | .alias _ a n b k, .alias _ a' n' b' k' => pure (a == a' && n == n' && b == b' && k == k')
      | .stuckMatch f _, .stuckMatch f' _ => pure (f == f')
      | _, _ => pure false
    unless dup do seen := seen.push o
  -- accesses first: an unresolved access usually also leaves a `match` on its result
  let accs := seen.filter fun | .access .. | .alias .. => true | _ => false
  let shown := if accs.isEmpty then seen else accs
  let expl ← shown.mapM explainObstacle
  if expl.isEmpty then
    return m!"{tac}: stuck {st.where_}: the instruction did not evaluate to `.ok s'` or a \
      branch; the unevaluated term is{indentExpr r}"
  return m!"{tac}: stuck {st.where_}\n{MessageData.joinSep (expl.toList.map fun e => m!"• {e}") "\n"}\n\
    (`set_option trace.{if tac.startsWith "janus64" then "janus64" else "janus"} true` shows every step.)"

/-- The branch conditions (`hbr`) of the current path, most recent first, for messages. -/
def branchConds : MetaM MessageData := do
  let mut hs : Array MessageData := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if d.userName.eraseMacroScopes == `hbr then
      hs := #[m!"  hbr : {← inl d.type}"] ++ hs
  if hs.isEmpty then return m!""
  return m!"\nThis path was taken under the branch conditions (most recent first):\n\
    {MessageData.joinSep (hs.toList.take 4) "\n"}\nA path is pruned when omega refutes its \
    branch condition from the hypotheses: add the fact that excludes it."

/-- Record the reads over stores in `e` that `simp` left unresolved (once each, with the
location of the step that produced them). -/
def noteAliases (ref : IO.Ref Status) (e : Expr) : MetaM Unit := do
  let acc ← IO.mkRef (#[] : Array Expr)
  e.forEachWhere (fun t => t.isAppOfArity ``Janus.Arm64.Memory.readLE 3 &&
      (t.getArg! 0).isAppOfArity ``Janus.Arm64.Memory.writeLE 4)
    (fun t => acc.modify (·.push t))
  let ts ← acc.get
  if ts.isEmpty then return
  let st ← ref.get
  let mut al := st.aliases
  for t in ts do
    if al.size ≥ 64 then break
    if al.any (·.1 == t) then continue
    al := al.push (t, st.where_)
  ref.set { st with aliases := al }

/-- After a run: if the remaining goals mention reads over stores whose aliasing was unknown,
say where they come from and what would resolve them (as an information message: the run
itself succeeded). -/
def reportAliases (tac : String) (ref : IO.Ref Status) (goals : List MVarId) : TacticM Unit := do
  unless janus.aliasInfo.get (← getOptions) do return
  let st ← ref.get
  if st.aliases.isEmpty || goals.isEmpty then return
  let mut msgs : Array MessageData := #[]
  for (t, loc) in st.aliases do
    if msgs.size ≥ 4 then break
    let hit ← goals.anyM fun g => do
      let ty ← instantiateMVars (← g.getType)
      return (ty.find? (· == t)).isSome
    unless hit do continue
    let m := t.getArg! 0
    let e ← explainObstacle (.alias (m.getArg! 0) (m.getArg! 1) (m.getArg! 2) (t.getArg! 1) (t.getArg! 2))
    msgs := msgs.push m!"• {loc}: {e}"
  unless msgs.isEmpty do
    logInfo m!"{tac}: the remaining goals contain reads over earlier stores whose aliasing is \
      unknown (they stay as `(m.writeLE a n v).readLE b k` and usually make the goal \
      unprovable):\n{MessageData.joinSep msgs.toList "\n"}"

/-! ## A `simp` cache and context per local context -/

/-- A fingerprint of the local context: the free variables in order. -/
def lctxKey : MetaM UInt64 := do
  let mut h : UInt64 := 7
  for d in ← getLCtx do
    h := mixHash h (hash d.fvarId)
  return h

structure StepCache where
  /-- `(lctx key, simp set name, its simp context, simprocs and discharger)` -/
  ctxs : Array (UInt64 × Name × Simp.Context × Simp.SimprocsArray × Simp.DischargeWrapper) := #[]
  /-- `(lctx key, simp cache)` of the `exec` simplifications. -/
  caches : Array (UInt64 × Simp.Cache) := #[]

/-- `simp e` with the methods of `simp (disch := d)` and the cache stored for the current local
context (updated afterwards). -/
def simpCached (cref : IO.Ref StepCache) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray)
    (d? : Option Simp.Discharge) (e : Expr) : MetaM Simp.Result := do
  let key ← lctxKey
  let c := ((← cref.get).caches.find? (·.1 == key)).map (·.2) |>.getD {}
  let (r, s) ← simpCore e ctx simprocs d? { cache := c }
  cref.modify fun sc =>
    let caches := sc.caches.filter (·.1 != key)
    -- keep a few: branches of the same run alternate between local contexts
    let caches := if caches.size ≥ 8 then caches.extract 1 caches.size else caches
    { sc with caches := caches.push (key, s.cache) }
  return r

/-- Look up or build (with `mk`) the simp context of simp set `set` for the current local
context, and run `k` with it. -/
def withCachedCtx (cref : IO.Ref StepCache) (set : Name)
    (mk : TacticM (Simp.Context × Simp.SimprocsArray × Simp.DischargeWrapper))
    (k : Simp.Context → Simp.SimprocsArray → Option Simp.Discharge → TacticM α) : TacticM α := do
  let key ← lctxKey
  let (ctx, simprocs, dw) ← match (← cref.get).ctxs.find? (fun e => e.1 == key && e.2.1 == set) with
    | some (_, _, c, sp, dw) => pure (c, sp, dw)
    | none =>
      let (c, sp, dw) ← mk
      cref.modify fun sc =>
        let ctxs := if sc.ctxs.size ≥ 16 then sc.ctxs.extract 1 sc.ctxs.size else sc.ctxs
        { sc with ctxs := ctxs.push (key, set, c, sp, dw) }
      pure (c, sp, dw)
  dw.with fun d? => k ctx simprocs d?

/-! ## Closed side conditions

Most side conditions of the simp sets are closed comparisons of literals (`4 < 3`, `0 ≠ 31`,
`(Nat.ble c 2^63 && Nat.blt c 2^64) = true`, `(5#64).toNat < 2^63`). `evalClosedProp?` decides
them by evaluating the literals at tactic time; the proof is `of_decide_eq_true rfl`, checked by
the kernel with the rest of the proof. This avoids adding one auxiliary declaration (and a kernel
check) per side condition, and fails fast on the false ones. Anything it does not recognise is
left to `decide`. -/

partial def evalClosedNat? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  if let some n := e.rawNatLit? then some n else
  if let some n := e.nat? then some n else
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do return (← evalClosedNat? a) + (← evalClosedNat? b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do return (← evalClosedNat? a) - (← evalClosedNat? b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do return (← evalClosedNat? a) * (← evalClosedNat? b)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => do return (← evalClosedNat? a) / (← evalClosedNat? b)
  | (``HMod.hMod, #[_, _, _, _, a, b]) => do return (← evalClosedNat? a) % (← evalClosedNat? b)
  | (``HPow.hPow, #[_, _, _, _, a, b]) => do
    let b ← evalClosedNat? b
    if b > 4096 then none else return (← evalClosedNat? a) ^ b
  | (``Nat.add, #[a, b]) => do return (← evalClosedNat? a) + (← evalClosedNat? b)
  | (``Nat.sub, #[a, b]) => do return (← evalClosedNat? a) - (← evalClosedNat? b)
  | (``Nat.mul, #[a, b]) => do return (← evalClosedNat? a) * (← evalClosedNat? b)
  | (``Nat.succ, #[a]) => do return (← evalClosedNat? a) + 1
  | (``BitVec.toNat, #[w, x]) => do
    let w ← evalClosedNat? w
    match x.consumeMData.getAppFnArgs with
    | (``BitVec.ofNat, #[_, n]) => return (← evalClosedNat? n) % 2 ^ w
    | (``OfNat.ofNat, #[_, n, _]) => return (← evalClosedNat? n) % 2 ^ w
    | _ => none
  | _ => none

partial def evalClosedBool? (e : Expr) : Option Bool :=
  let e := e.consumeMData
  if e.isConstOf ``Bool.true then some true else
  if e.isConstOf ``Bool.false then some false else
  match e.getAppFnArgs with
  | (``Nat.ble, #[a, b]) => do return decide ((← evalClosedNat? a) ≤ (← evalClosedNat? b))
  | (``Nat.blt, #[a, b]) => do return decide ((← evalClosedNat? a) < (← evalClosedNat? b))
  | (``Nat.beq, #[a, b]) => do return (← evalClosedNat? a) == (← evalClosedNat? b)
  | (``and, #[a, b]) => do return (← evalClosedBool? a) && (← evalClosedBool? b)
  | (``or, #[a, b]) => do return (← evalClosedBool? a) || (← evalClosedBool? b)
  | (``not, #[a]) => do return !(← evalClosedBool? a)
  | (``Decidable.decide, #[p, _]) => evalClosedProp? p
  | _ => none
where
  evalClosedProp? (p : Expr) : Option Bool :=
    let p := p.consumeMData
    match p.getAppFnArgs with
    | (``Not, #[a]) => do return !(← evalClosedProp? a)
    | (``And, #[a, b]) => do return (← evalClosedProp? a) && (← evalClosedProp? b)
    | (``Or, #[a, b]) => do return (← evalClosedProp? a) || (← evalClosedProp? b)
    | (``LT.lt, #[ty, _, a, b]) =>
      if ty.isConstOf ``Nat then do return decide ((← evalClosedNat? a) < (← evalClosedNat? b))
      else none
    | (``LE.le, #[ty, _, a, b]) =>
      if ty.isConstOf ``Nat then do return decide ((← evalClosedNat? a) ≤ (← evalClosedNat? b))
      else none
    | (``GT.gt, #[ty, _, a, b]) =>
      if ty.isConstOf ``Nat then do return decide ((← evalClosedNat? b) < (← evalClosedNat? a))
      else none
    | (``GE.ge, #[ty, _, a, b]) =>
      if ty.isConstOf ``Nat then do return decide ((← evalClosedNat? b) ≤ (← evalClosedNat? a))
      else none
    | (``Ne, #[ty, a, b]) =>
      if ty.isConstOf ``Nat then do return (← evalClosedNat? a) != (← evalClosedNat? b)
      else none
    | (``Eq, #[ty, a, b]) =>
      if ty.isConstOf ``Nat then do return (← evalClosedNat? a) == (← evalClosedNat? b)
      else if ty.isConstOf ``Bool then do return (← evalClosedBool? a) == (← evalClosedBool? b)
      else none
    | _ => none

/-- Decide a closed proposition built from literal arithmetic and comparisons (see above):
`some true` / `some false`, or `none` if it is not of that form. -/
def evalClosedProp? (p : Expr) : Option Bool := evalClosedBool?.evalClosedProp? p

/-- Unfold the definitions of the current file (constants that are not imported) in `e`, to its
definitional equal that mentions imported constants only, up to `fuel` rounds; unsafe, opaque and
partial definitions, theorems and anything else are left as they are.

The executor evaluates closed terms (addresses such as `Extracted.entry + 0x28`, program data)
with the compiled evaluator (`evalExpr`). A term that mentions a constant of the current file
can only be compiled against the compiled environment of the whole file so far, so with parallel
elaboration it waits for every earlier theorem of the file to be checked; a term over imported
constants is compiled against the imported environment and does not wait. The value is the same
either way (the unfolding is definitional). -/
partial def unfoldLocalDefs (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  let env ← getEnv
  let isLocal (n : Name) : Bool := !env.isImportedConst n && match env.find? n with
    | some (.defnInfo v) => v.safety == .safe
    | _ => false
  if fuel == 0 || !(e.getUsedConstants.any isLocal) then return e
  let e' ← Core.transform e (pre := fun x => do
    match x with
    | .const n us =>
      if isLocal n then
        match env.find? n with
        | some ci => return .done (ci.instantiateValueLevelParams! us)
        | none => return .continue
      else return .continue
    | _ => return .continue)
  unfoldLocalDefs e'.headBeta (fuel - 1)

/-- Heartbeat budget (in thousands) for the elaborator's attempt in `decideClosed`. -/
def decideClosedHeartbeats : Nat := 50000

/-- Prove the closed goal `g` by `decide`: first the elaborator's evaluation (plain `decide`,
within `decideClosedHeartbeats`), then, if that cannot decide it, `decide +kernel`. Returns
whether `g` was closed (otherwise the state is unchanged).

Both prove `g` by evaluating its `Decidable` instance, and the kernel checks the evaluation
either way: plain `decide` leaves `of_decide_eq_true rfl` in the proof (checked with the
theorem), `decide +kernel` checks it in an auxiliary lemma. The auxiliary lemma is added
synchronously (`decide +kernel` turns `Elab.async` off), which waits for the kernel checks of
every earlier declaration of the file; a proof file whose theorems all use the executor would
then elaborate its theorems one after the other instead of in parallel. -/
def decideClosed (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  let ok ← tryCatchRuntimeEx
    (do
      let gs ← withTheReader Core.Context (fun c => { c with maxHeartbeats := decideClosedHeartbeats * 1000 }) <|
        withCurrHeartbeats <| Tactic.run g <| withoutRecover (evalTactic (← `(tactic| decide)))
      pure gs.isEmpty)
    (fun _ => pure false)
  if ok then return true
  saved.restore
  let ok ← try
      let gs ← Tactic.run g <| withoutRecover (evalTactic (← `(tactic| decide +kernel)))
      pure gs.isEmpty
    catch _ => pure false
  unless ok do saved.restore
  return ok

/-- Close the goal `g` if it is a closed literal comparison that evaluates to `true`; `false` if
it evaluates to `false`; `none` if it is not of that form. -/
def closeByEval? (g : MVarId) : MetaM (Option Bool) := do
  let t ← instantiateMVars (← g.getType)
  match evalClosedProp? t with
  | some true =>
    g.assign (← mkDecideProof t)
    return some true
  | r => return r

/-! ## Applying the step lemmas -/

/-- `g.apply e` for a lemma `e` whose conclusion matches the goal syntactically, without the
`whnf` of the goal that `MVarId.apply` performs to count arguments: on a goal like
`ExecThen p (if c then … else …) Q` that `whnf` unfolds `ExecThen` and evaluates the
decision procedure of the symbolic condition `c`, which can take seconds. Instance arguments
are taken from the unification, never re-synthesised. Returns the unassigned arguments as new
goals, in order. -/
def applyFast (g : MVarId) (e : Expr) : MetaM (List MVarId) := g.withContext do
  let ty ← instantiateMVars (← inferType e)
  let (ms, _, concl) ← forallMetaTelescope ty
  let tgt ← instantiateMVars (← g.getType)
  unless ← isDefEq concl tgt do
    throwError "janus: internal error: cannot apply{indentExpr e}
of type{indentExpr ty}
to the goal{indentExpr tgt}"
  g.assign (mkAppN e ms)
  let mut out := []
  for m in ms do
    let mv := m.mvarId!
    if ← mv.isAssigned then continue
    mv.setKind .syntheticOpaque
    out := out ++ [mv]
  return out

/-! ## Callee preconditions -/

/-- Heads that are not unfolded when proving a precondition. -/
def basicProps : List Name :=
  [``Eq, ``Ne, ``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``Not, ``And, ``Or, ``Iff, ``True, ``False,
   ``Exists]

/-- Prove a callee precondition: split conjunctions, simplify each part with `clean` (the
post simp set with the state hypotheses), close it with `closer`, and unfold named
predicates (`GuardOK`, `StackOK`, …) up to `depth` times when that fails. Returns the parts
that could not be proved. -/
partial def provePreCore (clean : MVarId → TacticM (List MVarId)) (closer : TSyntax `tactic)
    (g : MVarId) (depth : Nat := 4) : TacticM (Array Expr) := g.withContext do
  if ← g.isAssigned then return #[]
  let t ← whnfR (← instantiateMVars (← g.getType)).headBeta
  let g ← g.replaceTargetDefEq t
  if t.isAppOfArity ``And 2 then
    let gs ← applyFast g (← mkConstWithFreshMVarLevels ``And.intro)
    let mut left := #[]
    for g' in gs do left := left ++ (← provePreCore clean closer g' depth)
    return left
  let gs ← clean g
  let some g := gs.head? | return #[]
  let t ← instantiateMVars (← g.getType)
  if t.isAppOfArity ``And 2 then return ← provePreCore clean closer g depth
  let saved ← saveState
  let ok ← try
      let rest ← Tactic.run g <| withoutRecover (evalTactic closer)
      pure rest.isEmpty
    catch _ => pure false
  if ok then return #[]
  saved.restore
  if depth > 0 then
    if let some c := t.getAppFn.constName? then
      unless basicProps.contains c do
        -- a structure (`StackGuardOK`): prove its fields
        if isStructure (← getEnv) c then
          do
            let ctor := getStructureCtor (← getEnv) c
            let gs ← try applyFast g (← mkConstWithFreshMVarLevels ctor.name) catch _ => pure []
            unless gs.isEmpty do
              let mut left := #[]
              for g' in gs do left := left ++ (← provePreCore clean closer g' (depth - 1))
              return left
        if let some t' ← g.withContext (unfoldDefinition? t) then
          let g ← g.replaceTargetDefEq t'
          return ← provePreCore clean closer g (depth - 1)
  return #[t]

/-! ## Callee postconditions -/

/-- After a callee summary: `hpost : post s s'` (with `hpc : s'.pc = …`). Split conjunctions
and existentials into hypotheses, and substitute `s'` if the postcondition contains an equation
`s' = e` (then `hpc` is cleared: it is implied). -/
partial def destructPost (g : MVarId) (s' hpc hpost : FVarId) : MetaM MVarId := do
  let rec go (g : MVarId) (hs : List FVarId) (substituted : Bool) : MetaM MVarId := do
    match hs with
    | [] => return g
    | h :: rest =>
      g.withContext do
      -- `whnfR`: also unfold reducible abbreviations of the postcondition
      let t ← whnfR (← instantiateMVars (← h.getType)).headBeta
      let g ← g.replaceLocalDeclDefEq h t
      if t.isAppOfArity ``And 2 then
        let gs ← g.cases h
        let some sg := gs[0]? | return g
        let fs := sg.fields.toList.filterMap fun e => if e.isFVar then some e.fvarId! else none
        go sg.mvarId (fs ++ rest) substituted
      else if t.isAppOfArity ``Exists 2 then
        let gs ← g.cases h
        let some sg := gs[0]? | return g
        let fs := sg.fields.toList.filterMap fun e => if e.isFVar then some e.fvarId! else none
        -- the witness is a value, the second field the property
        go sg.mvarId (fs.drop 1 ++ rest) substituted
      else if let some (_, lhs, _) := t.eq? then
        if !substituted && lhs.isFVar && lhs.fvarId! == s' then
          let g ← (try g.clear hpc catch _ => pure g)
          let (_, g) ← substCore g h (symm := false) (tryToSkip := true)
          go g rest true
        else go g rest substituted
      else go g rest substituted
  go g [hpost] false

/-! ## Restored registers -/

/-- For a register-file chain `setR (… (setR (x.regs) r₁ v₁) …) rₖ vₖ` (with `setR` the ISA's
`setReg`): the base `x.regs` and the literal indices written, if it has that shape. -/
partial def regChain (setR regs : Name) (f : Expr) (acc : List Nat := []) :
    Option (Expr × List Nat) :=
  if f.isAppOfArity setR 3 then
    match (f.getArg! 1).nat? <|> (f.getArg! 1).rawNatLit? with
    | some r => regChain setR regs (f.getArg! 0) (r :: acc)
    | none => none
  else if f.isAppOfArity regs 1 then some (f, acc)
  else none

/-- `setR f r (x.regs r)` where `f` is a chain over `x.regs` that does not write `r`: the write
restores the old value (a callee-saved register reloaded from the stack), so the result is `f`.
Returns `f` and the proof of `f r = x.regs r` (by `rfl`: the chain lookup reduces on literal
indices). -/
def restoredReg? (setR regs : Name) (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  unless e.isAppOfArity setR 3 do return none
  let f := e.getArg! 0
  let r := e.getArg! 1
  let v := e.getArg! 2
  let some rn := r.nat? <|> r.rawNatLit? | return none
  unless v.isAppOfArity regs 2 do return none
  unless (v.getArg! 1).nat? == some rn || (v.getArg! 1).rawNatLit? == some rn do return none
  let some (base, written) := regChain setR regs f | return none
  unless base.getArg! 0 == v.getArg! 0 do return none
  if written.contains rn then return none
  let pf ← mkEqRefl v
  return some (f, r, v, pf)

/-! ## Memory frames of callees -/

/-- The rewrite rules of a `MemFrame` hypothesis (`readLE`, `accessible`), for the state simp
set. -/
def frameRules (d : LocalDecl) (ty : Expr) : MetaM (Array Expr) := do
  if ty.isAppOfArity ``Janus.LiveFrame 4 then
    if (ty.getArg! 3).isAppOfArity ``List.nil 1 then
      return #[← mkAppM ``Janus.LiveFrame.readLE_nil #[d.toExpr]]
    return #[← mkAppM ``Janus.LiveFrame.readLE #[d.toExpr]]
  unless ty.isAppOfArity ``Janus.MemFrame 3 do return #[]
  return #[← mkAppM ``Janus.MemFrame.readLE #[d.toExpr], ← mkAppM ``Janus.MemFrame.accessible #[d.toExpr]]

/-- Reduce a goal `m.accessible a n w = true` to one about the underlying memory: strip stores
(`accessible_writeLE` holds by `rfl`) and go through `MemFrame` hypotheses (`hf.accessible`). -/
partial def reduceAccessible (g : MVarId) (fuel : Nat := 64) : MetaM MVarId := g.withContext do
  if fuel = 0 then return g
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := t.eq? | return g
  unless lhs.isAppOfArity ``Janus.Arm64.Memory.accessible 4 do return g
  let m := lhs.getArg! 0
  let m0 := stripWrites m
  let mkGoal (m' : Expr) : MetaM Expr := do
    mkEq (mkAppN (mkConst ``Janus.Arm64.Memory.accessible)
      #[m', lhs.getArg! 1, lhs.getArg! 2, lhs.getArg! 3]) rhs
  let g ← if m0 != m then g.replaceTargetDefEq (← mkGoal m0) else pure g
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``Janus.MemFrame 3 do continue
    unless ← withReducible (isDefEq (ty.getArg! 1) m0) do continue
    let base := ty.getArg! 0
    let t' ← mkGoal base
    let g' ← mkFreshExprSyntheticOpaqueMVar t'
    let eqv ← mkAppM ``Janus.MemFrame.accessible #[d.toExpr, lhs.getArg! 1, lhs.getArg! 2, lhs.getArg! 3]
    -- `(m0.accessible … = true) = (base.accessible … = true)`
    let eqT ← mkCongrArg (← mkFunOfEq rhs) eqv
    g.assign (← mkEqMPR eqT g')
    return ← reduceAccessible g'.mvarId! (fuel - 1)
  return g
where
  mkFunOfEq (rhs : Expr) : MetaM Expr := do
    return .lam `x (mkConst ``Bool) (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (.bvar 0) rhs) .default

/-- Clear the propositional hypotheses that mention atoms the (arithmetic) goal does not: what an
`omega`/`simp … at *` on a goal about a few addresses needs is small, and the contexts after
several calls are large. -/
def clearIrrelevant (g : MVarId) : MetaM MVarId := g.withContext do
  let goalAtoms := arithAtoms (← instantiateMVars (← g.getType))
  let mut toClear := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    unless (arithAtoms ty).all goalAtoms.contains do toClear := toClear.push d.fvarId
  g.tryClearMany toClear

/-- A side condition `Outside a n rs` (of a `MemFrame` read rule): unfold the literal list and
prove each range condition by `omega`. -/
def dischargeOutside (g : MVarId) : TacticM Bool := do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Janus.Outside 3 do return false
  let saved ← saveState
  try
    let gs ← Tactic.run g <| withoutRecover (evalTactic (← `(tactic|
      (simp (config := { failIfUnchanged := false }) only [Janus.outside_cons, Janus.outside_nil,
        Janus.outside_append, and_true,
        BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
       repeat' apply And.intro))))
    for g' in gs do
      unless ← closePart g' do saved.restore; return false
    return true
  catch _ => saved.restore; return false
where
  /-- One conjunct: arithmetic by `omega`, or `Outside a n rs` for a list `rs` that is not a
  literal (a variable such as the runtime-owned ranges of a contract) from a hypothesis
  `Outside b k rs` with `[a, a+n) ⊆ [b, b+k)` (`Outside.of_sub`). -/
  closePart (g : MVarId) : TacticM Bool := g.withContext do
    let t ← instantiateMVars (← g.getType)
    if t.isAppOfArity ``Janus.Outside 3 then
      let rs := t.getArg! 2
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        unless ty.isAppOfArity ``Janus.Outside 3 do continue
        unless ← withReducible (isDefEq (ty.getArg! 2) rs) do continue
        let saved ← saveState
        try
          let h ← Term.exprToSyntax d.toExpr
          let gs ← Tactic.run g <| withoutRecover do
            evalTactic (← `(tactic| (apply Janus.Outside.of_sub $h <;> omega)))
          if gs.isEmpty then return true
          saved.restore
        catch _ => saved.restore
      return false
    let saved ← saveState
    -- first with only the hypotheses about the goal's atoms (cheap: the contexts after several
    -- calls are large, and `omega` splits on every disjunction in them), then with all
    try
      let g' ← clearIrrelevant g
      let gs ← Tactic.run g' <| withoutRecover (evalTactic (← `(tactic| omega)))
      if gs.isEmpty then return true
      saved.restore
    catch _ => saved.restore
    try
      let gs ← Tactic.run g <| withoutRecover (evalTactic (← `(tactic| omega)))
      if gs.isEmpty then return true
      saved.restore; omegaApart g
    catch _ => saved.restore; omegaApart g

/-- Split the conjunctions among the hypotheses the call introduced (the `Apart` facts `simp`
normalised from `ApartAll` are conjunctions), so that the dischargers see each fact. -/
partial def splitNewConj (g : MVarId) (before : Array FVarId) : MetaM MVarId := do
  let lctx ← g.withContext getLCtx
  for d in lctx do
    if d.isImplementationDetail || before.contains d.fvarId then continue
    let ty ← g.withContext (instantiateMVars d.type)
    if ty.isAppOfArity ``And 2 then
      let gs ← g.cases d.fvarId
      let some sg := gs[0]? | return g
      return ← splitNewConj sg.mvarId before
  return g

/-- After a live contract's call: for every new `InRanges p n rs` hypothesis (an object the call
returned inside the runtime-owned ranges) and every `Outside a k rs` hypothesis (caller data
outside them), add `Apart a k p n`, so that the read-over-write side conditions see the object
apart from the caller's frame, `g`, type descriptors (`janus_apart`, one fact at a time). -/
def addApartFacts (g : MVarId) (before : Array FVarId) : MetaM MVarId := g.withContext do
  let mut ins := #[]
  let mut outs := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Janus.InRanges 3 && !before.contains d.fvarId then ins := ins.push (d, ty)
    else if ty.isAppOfArity ``Janus.Outside 3 then outs := outs.push (d, ty)
  let mut g := g
  for (di, ti) in ins do
    for (do_, to) in outs do
      unless ← withReducible (isDefEq (ti.getArg! 2) (to.getArg! 2)) do continue
      let pf ← mkAppM ``Janus.InRanges.apart #[di.toExpr, do_.toExpr]
      let (_, g') ← (← g.assert `h_apart (← inferType pf) pf).intro1P
      g := g'
  return g

/-- `rs[i] ∈ rs` for a list literal `rs = [e₀, …]`. -/
def memProof (ty : Expr) (elems : List Expr) (i : Nat) : MetaM Expr := do
  match elems, i with
  | e :: rest, 0 => mkAppOptM ``List.mem_cons_self #[ty, e, ← mkListLit ty rest]
  | e :: rest, i + 1 =>
    let h ← memProof ty rest i
    mkAppOptM ``List.mem_cons_of_mem #[ty, e, none, none, h]
  | [], _ => throwError "janus_frame: index out of range"

/-- The arithmetic closer of `janus_frame`'s side goals. -/
def frameArith (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  -- the goal's own atoms first (the contexts after several calls are large), then everything
  try
    let g' ← clearIrrelevant g
    let gs ← Tactic.run g' <| withoutRecover (evalTactic (← `(tactic|
      ((try simp only [Janus.outside_cons, Janus.outside_nil, and_true, BitVec.toNat_sub,
          BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *); omega))))
    if gs.isEmpty then return true
    saved.restore
  catch _ => saved.restore
  try
    let gs ← Tactic.run g <| withoutRecover (evalTactic (← `(tactic|
      ((try simp only [Janus.outside_cons, Janus.outside_nil, and_true, BitVec.toNat_sub,
          BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *); omega))))
    if gs.isEmpty then return true
    saved.restore; omegaApart g
  catch _ => saved.restore; omegaApart g

/-- A side condition `InRanges a n rs` (of a `LiveFrame` read rule, or of the view lemmas of
`Janus.Contracts.Live`): `[a, a+n)` inside one range of `rs`. For `l ++ r` either side; for a
literal `(lo, hi) :: rest` the head by `omega` or the rest; for anything else (a variable such as a
live set or the runtime-owned ranges) a hypothesis `InRanges b k rs` with `[a, a+n) ⊆ [b, b+k)`. -/
partial def dischargeInRanges (g : MVarId) (fuel : Nat := 32) : TacticM Bool := g.withContext do
  if fuel = 0 then return false
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``Janus.InRanges 3 do return false
  let a := t.getArg! 0
  let n := t.getArg! 1
  let rs ← whnfR (← instantiateMVars (t.getArg! 2))
  let arith (lhs rhs : Expr) : TacticM (Option Expr) := do
    let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[lhs, rhs])
    if ← frameArith m.mvarId! then return some m else return none
  -- hypotheses first (cheap, and the only way for a variable)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``Janus.InRanges 3 do continue
    unless ← withReducible (isDefEq (ty.getArg! 2) (t.getArg! 2)) do continue
    let saved ← saveState
    let b := ty.getArg! 0
    let k := ty.getArg! 1
    let some h1 ← arith b a | saved.restore; continue
    let some h2 ← arith (← mkAppM ``HAdd.hAdd #[a, n]) (← mkAppM ``HAdd.hAdd #[b, k]) | saved.restore; continue
    g.assign (← mkAppM ``Janus.InRanges.sub #[d.toExpr, h1, h2])
    return true
  match rs.getAppFnArgs with
  | (``HAppend.hAppend, #[_, _, _, _, l, r]) =>
    let saved ← saveState
    let gr ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Janus.InRanges #[a, n, r])
    if ← dischargeInRanges gr.mvarId! (fuel - 1) then
      g.assign (← mkAppM ``Janus.InRanges.append_right #[l, gr]); return true
    saved.restore
    let gl ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Janus.InRanges #[a, n, l])
    if ← dischargeInRanges gl.mvarId! (fuel - 1) then
      g.assign (← mkAppM ``Janus.InRanges.append_left #[gl, r]); return true
    saved.restore
    return false
  | (``List.cons, #[_, hd, tl]) =>
    let saved ← saveState
    let hd ← whnfR hd
    if hd.isAppOfArity ``Prod.mk 4 then
      let lo := hd.getArg! 2
      let hi := hd.getArg! 3
      if let some h1 ← arith lo a then
        if let some h2 ← arith (← mkAppM ``HAdd.hAdd #[a, n]) hi then
          g.assign (← mkAppM ``Janus.InRanges.cons_head #[tl, h1, h2]); return true
    saved.restore
    let gt ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Janus.InRanges #[a, n, tl])
    if ← dischargeInRanges gt.mvarId! (fuel - 1) then
      g.assign (← mkAppM ``Janus.InRanges.cons_tail #[hd, gt]); return true
    saved.restore
    return false
  | _ => return false

elab "janus_clear_irrel" : tactic => do
  replaceMainGoal [← clearIrrelevant (← getMainGoal)]

/-- Peel the store `m = m'.writeLE a k v` of a `MemFrame m₀ m rs` goal using a hypothesis
`InRanges b k' rs'` (with `rs'` contained in `rs`, e.g. `rs = rs' ++ …`, and `[a, a+k) ⊆ [b, b+k')`
by omega); on success the main goal is `MemFrame m₀ m' rs`. -/
def tryInRanges (g : MVarId) (m0 m rs : Expr) : TacticM Bool := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``Janus.InRanges 3 do continue
    -- the hypothesis's ranges must be `rs` or one side of `l ++ r` (cheap syntactic filter)
    let hl := ty.getArg! 2
    let okList ← do
      if ← withReducible (isDefEq hl rs) then pure true
      else match (← instantiateMVars rs).getAppFnArgs with
        | (``HAppend.hAppend, #[_, _, _, _, l, r]) =>
          pure ((← withReducible (isDefEq hl l)) || (← withReducible (isDefEq hl r)))
        | _ => pure false
    unless okList do continue
    let saved ← saveState
    try
      let hinTy ← mkAppM ``Janus.InRanges #[m.getArg! 1, m.getArg! 2, rs]
      let hin ← mkFreshExprSyntheticOpaqueMVar hinTy
      let h ← Term.exprToSyntax d.toExpr
      let gs ← Tactic.run hin.mvarId! <| withoutRecover (evalTactic (← `(tactic|
        exact Janus.InRanges.of_subset
          (Janus.InRanges.sub $h (by first | (janus_clear_irrel; omega) | omega | (simp only [BitVec.toNat_sub,
              BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *; omega))
            (by first | (janus_clear_irrel; omega) | omega | (simp only [BitVec.toNat_sub, BitVec.toNat_add,
              BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *; omega)))
          (by intro r hr; simp [List.mem_append, hr]))))
      unless gs.isEmpty do saved.restore; continue
      let hm ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Janus.MemFrame #[m0, m.getArg! 0, rs])
      g.assign (← mkAppM ``Janus.MemFrame.writeLE_inRanges #[hm, m.getArg! 3, hin])
      setGoals [hm.mvarId!]
      return true
    catch e => trace[janus.disch] "tryInRanges: {e.toMessageData}"; saved.restore
  return false

/-- Prove `MemFrame m₀ m rs`: peel the stores of `m` (each must fall inside one of the ranges),
go through `MemFrame` hypotheses of the context (their ranges must be covered by `rs`), and end
with `MemFrame.refl` when the memory is `m₀`. -/
partial def proveFrame (g : MVarId) (fuel : Nat := 256) : TacticM Unit := g.withContext do
  if fuel = 0 then throwError "janus_frame: too deep"
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``Janus.MemFrame 3 do
    throwError "janus_frame: the goal is not `MemFrame m₀ m rs`:{indentExpr t}"
  let m0 ← whnfR (t.getArg! 0)
  let m ← whnfR (t.getArg! 1)
  let rs := t.getArg! 2
  if ← withReducible (isDefEq m m0) then
    g.assign (← mkAppM ``Janus.MemFrame.refl #[m0, rs]); return
  if m.isAppOfArity ``Janus.Arm64.Memory.writeLE 4 then
    -- a store inside an object known to lie in the ranges (`InRanges b k rs'` with `rs'` a part
    -- of `rs`, e.g. the runtime-owned ranges of an allocation contract)
    if ← tryInRanges g m0 m rs then return ← proveFrame (← getMainGoal) (fuel - 1)
    -- the literal ranges: `rs` itself, or the literal right side of `l ++ [ … ]` (`l` e.g. the
    -- runtime-owned ranges of a contract)
    let rsI ← instantiateMVars rs
    let (lit, pre?) := match rsI.getAppFnArgs with
      | (``HAppend.hAppend, #[_, _, _, _, l, r]) => (r, some l)
      | _ => (rsI, none)
    let some (pty, elems) := lit.listLit? |
      throwError "janus_frame: the ranges must be a list literal (or `l ++ [ … ]`){indentExpr rs}"
    for i in [0:elems.length] do
      let saved ← saveState
      let hm ← mkFreshExprSyntheticOpaqueMVar
        (← mkAppM ``Janus.MemFrame #[m0, m.getArg! 0, rs])
      let hr ← memProof pty elems i
      let hr ← match pre? with
        | some l => mkAppM ``List.mem_append_right #[l, hr]
        | none => pure hr
      let e := elems[i]!
      let a := m.getArg! 1
      let k := m.getArg! 2
      let h1 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[← mkAppM ``Prod.fst #[e], a])
      let h2 ← mkFreshExprSyntheticOpaqueMVar
        (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[a, k], ← mkAppM ``Prod.snd #[e]])
      if (← frameArith h1.mvarId!) && (← frameArith h2.mvarId!) then
        let pf ← mkAppOptM ``Janus.MemFrame.writeLE
          #[m0, m.getArg! 0, rs, hm, a, k, m.getArg! 3, e, hr, h1, h2]
        g.assign pf
        return ← proveFrame hm.mvarId! (fuel - 1)
      saved.restore
    throwError "janus_frame: the store of{indentExpr (m.getArg! 2)}\nbytes at{indentExpr (m.getArg! 1)}\nis in none of the ranges{indentExpr rs}"
  -- a callee's frame: `hf : MemFrame m₁ m rs₁`
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``Janus.MemFrame 3 do continue
    unless ← withReducible (isDefEq (← whnfR (ty.getArg! 1)) m) do continue
    let m1 := ty.getArg! 0
    let saved ← saveState
    let hm ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Janus.MemFrame #[m0, m1, rs])
    -- `∀ a n, Outside a n rs → Outside a n rs ∧ Outside a n rs₁`
    let subTy ← withLocalDeclD `a (mkConst ``Nat) fun a => withLocalDeclD `n (mkConst ``Nat) fun n => do
      let o (r : Expr) := mkAppN (mkConst ``Janus.Outside) #[a, n, r]
      mkForallFVars #[a, n] (← mkArrow (o rs) (mkAnd (o rs) (o (ty.getArg! 2))))
    let sub ← mkFreshExprSyntheticOpaqueMVar subTy
    let sg := sub.mvarId!
    let ok ← try
        let gs ← Tactic.run sg <| withoutRecover (evalTactic (← `(tactic|
          (intro a n h
           refine ⟨h, ?_⟩
           revert h
           simp only [Janus.outside_cons, Janus.outside_nil, Janus.outside_append, and_true,
             and_imp]
           intros
           janus_clear_irrel
           try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
             Nat.reduceMod] at *
           repeat' apply And.intro
           all_goals first | assumption | omega))))
        pure gs.isEmpty
      catch _ => pure false
    unless ok do saved.restore; continue
    g.assign (← mkAppM ``Janus.MemFrame.trans #[hm, d.toExpr, sub])
    return ← proveFrame hm.mvarId! (fuel - 1)
  throwError "janus_frame: cannot relate the memory{indentExpr m}\nto{indentExpr m0}\n(no store to peel, and no `MemFrame` hypothesis about it whose ranges are covered)"

/-- `janus_live`: close a live-runtime goal of a callee precondition (`RtInv.inv R b L g v`,
`RtInv.ok R a args`) from the context. Declared here so that the executors' precondition closers
can name it; its elaborator is `Janus.Contracts.Live`'s (without that module it fails, and the
closers go on). -/
syntax "janus_live" : tactic

/-- `janus_apart`: `omega` with the `Apart` hypotheses of the context, one at a time. -/
elab "janus_apart" : tactic => do
  let g ← getMainGoal
  unless ← omegaApart g do throwError "janus_apart: no `Apart` hypothesis makes omega succeed"
  replaceMainGoal []

/-- Prove a goal `MemFrame m₀ m rs` (the memory part of a callee summary). -/
elab "janus_frame" : tactic => do proveFrame (← getMainGoal); replaceMainGoal []

/-- `janus_eval% t`: the closed natural number `t` (e.g. `segAddr Extracted.program "f" + 8`),
evaluated at elaboration time and inserted as a numeral. For arguments that must be literals
(a lemma whose `rfl` side conditions are checked against them), without copying the number
into the proof. -/
elab "janus_eval% " t:term : term => do
  let e ← Term.elabTerm t (some (mkConst ``Nat))
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar then throwError "janus_eval%: not a closed term{indentExpr e}"
  let v ← unsafe evalExpr Nat (mkConst ``Nat) e
  return mkNatLit v

/-! ## `janus_cases` -/

/-- `h : k < N` (or `k ≤ N`) with `N` a literal: one goal per value of `k` (substituted if `k` is
a variable, else rewritten with `h_case : k = i`). -/
def casesBound (tac : String) (h : TSyntax `ident) : TacticM Unit := withMainContext do
  let hE ← elabTerm h none
  let ty ← instantiateMVars (← inferType hE)
  let evalLit (e : Expr) : MetaM (Option Nat) := do
    let e ← instantiateMVars e
    if let some n := e.nat? then return some n
    if let some n := e.rawNatLit? then return some n
    let e' ← whnfR e
    return e'.nat? <|> e'.rawNatLit?
  let (k, n) ← match ty.getAppFnArgs with
    | (``LT.lt, #[_, _, k, n]) => pure (k, ← evalLit n)
    | (``LE.le, #[_, _, k, n]) => pure (k, (← evalLit n).map (· + 1))
    | _ => throwError "{tac}: expected `k < N` or `k ≤ N`, got{indentExpr ty}"
  let some n := n | throwError "{tac}: the bound must be a literal{indentExpr ty}"
  if n == 0 then
    evalTactic (← `(tactic| exact absurd $h (by omega)))
    return
  let kStx ← Term.exprToSyntax k
  let alts : List Term ← (List.range n).mapM fun i => `($kStx = $(Syntax.mkNumLit (toString i)))
  let disj ← match alts.reverse with
    | [] => unreachable!
    | a :: rest => rest.foldlM (fun acc t => `($t ∨ $acc)) a
  evalTactic (← `(tactic| rcases (show $disj from by omega) with $(mkIdent `h_case):ident))
  let mut goals ← getGoals
  let mut out := []
  for _ in [0:n] do
    match goals with
    | [] => break
    | g :: rest =>
      goals := rest
      let gs ← Tactic.run g <| withoutRecover do
        let some d := (← getLCtx).findFromUserName? `h_case | return
        let t ← instantiateMVars d.type
        if t.isAppOfArity ``Or 2 then
          evalTactic (← `(tactic| rcases $(mkIdent `h_case):ident with $(mkIdent `h_case):ident | $(mkIdent `h_case):ident))
      match gs with
      | [g1, g2] => out := out ++ [g1]; goals := g2 :: goals
      | gs => out := out ++ gs
  let mut res := []
  for g in out do
    let gs ← Tactic.run g <| withoutRecover do
      if k.isFVar then
        evalTactic (← `(tactic| subst $(mkIdent `h_case):ident))
      else
        evalTactic (← `(tactic| try simp only [$(mkIdent `h_case):ident] at *))
    res := res ++ gs
  replaceMainGoal (res ++ goals)

/-! ## Range facts of memory reads -/

partial def collectReadLE (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``Janus.Arm64.Memory.readLE 3 then acc.push e else
  match e with
  | .app f a => collectReadLE a (collectReadLE f acc)
  | .lam _ t b _ | .forallE _ t b _ => collectReadLE b (collectReadLE t acc)
  | .letE _ t v b _ => collectReadLE b (collectReadLE v (collectReadLE t acc))
  | .mdata _ b => collectReadLE b acc
  | .proj _ _ b => collectReadLE b acc
  | _ => acc

/-- Add `Memory.readLE m a n < 256^n` (as a literal bound) for every `readLE` with a literal
width in the goal and the hypotheses. -/
def addReadLEBounds : TacticM Unit := withMainContext do
  let mut seen : Std.HashSet Expr := {}
  let mut tys := #[← instantiateMVars (← getMainTarget)]
  for d in ← getLCtx do
    if !d.isImplementationDetail then tys := tys.push (← instantiateMVars d.type)
  for t in tys do
    for e in collectReadLE t #[] do
      if seen.contains e then continue
      seen := seen.insert e
      if e.hasLooseBVars then continue
      let some n := (e.getArg! 2).nat? | continue
      let g ← getMainGoal
      let bound := mkNatLit (256 ^ n)
      let ty ← mkAppM ``LT.lt #[e, bound]
      let pf ← mkExpectedTypeHint
        (← mkAppM ``Janus.Arm64.Memory.readLE_lt #[e.getArg! 0, e.getArg! 1, e.getArg! 2]) ty
      let (_, g') ← (← g.assert `h_rd ty pf).intro1P
      replaceMainGoal [g']

/-! ## Robustness to the shape of `State` -/

/-- For a structure `S` with field `f`: `(number of fields, index of f)`. Used to read the pc
of a state literal `S.mk …` without depending on how many fields the structure has. -/
def fieldIndex (S f : Name) : MetaM (Option (Nat × Nat)) := do
  let fields := getStructureFields (← getEnv) S
  return (fields.idxOf? f).map (fields.size, ·)

/-! ## Address arithmetic without `omega`

Most side conditions of a memory step are linear facts about addresses of the form
`base + offset` with literal offsets: "the 8-byte read at `x + 16` is disjoint from the store
at `x + 8`" (same base: a comparison of literals), "… from the store at `z + 8`" (different
bases: one case split on the aliasing fact `z + 64 ≤ x ∨ x + 64 ≤ z`), "the read is at the
address of the store" (`x + 8 = x + 8`). `omega` proves each of them, but a call (and the
kernel check of its proof) costs 10-40 ms, and a straight-line run asks for thousands. `addrDisch`
decides them directly, with proofs built from the lemmas below and `Nat.ble`/`Nat.beq` on
literals; anything else is left to `omega`. -/

theorem addr_le_same {x a b : Nat} (h : Nat.ble a b = true) : x + a ≤ x + b :=
  Nat.add_le_add_left (Nat.le_of_ble_eq_true h) x

theorem addr_eq_same {x a b : Nat} (h : Nat.beq a b = true) : x + a = x + b := by
  rw [Nat.eq_of_beq_eq_true h]

theorem addr_le_hyp {x y A B a b : Nat} (hd : x + A ≤ y + B) (h : Nat.ble (a + B) (A + b) = true) :
    x + a ≤ y + b := by
  have := Nat.le_of_ble_eq_true h; omega

theorem addr_le_congr {L R l r : Nat} (pL : L = l) (pR : R = r) (h : l ≤ r) : L ≤ R := pL ▸ pR ▸ h
theorem addr_eq_congr {L R l r : Nat} (pL : L = l) (pR : R = r) (h : l = r) : L = R := pL ▸ pR ▸ h
theorem addr_le_of_congr {L R l r : Nat} (pL : L = l) (pR : R = r) (h : L ≤ R) : l ≤ r := pL ▸ pR ▸ h

theorem addr_lin_add {a b B c : Nat} (pa : a = B + c) : a + b = B + (c + b) := by
  rw [pa, Nat.add_assoc]
theorem addr_lin_add' {a b B c : Nat} (pb : b = B + c) : a + b = B + (c + a) := by
  rw [pb]; omega

/-- A linear address: `base + c` (`base = none`: the literal `c`), with a proof of
`e = base + c` (resp. `e = c`). Offsets are literals; the base is any other term. -/
partial def linAddr (e : Expr) : MetaM (Option Expr × Nat × Expr) := do
  let e := e.consumeMData
  if let some n := evalClosedNat? e then
    let ty ← mkEq e (mkRawNatLit n)
    return (none, n, ← mkExpectedTypeHint (← mkEqRefl e) ty)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[t, _, _, _, a, b]) =>
    if t.isConstOf ``Nat then
      if let some k := evalClosedNat? b then
        let (B, c, pa) ← linAddr a
        match B with
        | some B =>
          let pf := mkAppN (mkConst ``addr_lin_add) #[a, b, B, mkRawNatLit c, pa]
          let ty ← mkEq e (← mkAdd B (mkRawNatLit (c + k)))
          return (some B, c + k, ← mkExpectedTypeHint pf ty)
        | none =>
          let ty ← mkEq e (mkRawNatLit (c + k))
          return (none, c + k, ← mkExpectedTypeHint (← mkEqRefl e) ty)
      if let some k := evalClosedNat? a then
        let (B, c, pb) ← linAddr b
        if let some B := B then
          let pf := mkAppN (mkConst ``addr_lin_add') #[a, b, B, mkRawNatLit c, pb]
          let ty ← mkEq e (← mkAdd B (mkRawNatLit (c + k)))
          return (some B, c + k, ← mkExpectedTypeHint pf ty)
  | _ => pure ()
  let ty ← mkEq e (← mkAdd e (mkRawNatLit 0))
  return (some e, 0, ← mkExpectedTypeHint (← mkEqRefl e) ty)

/-- `base + c` as an expression. -/
def linExpr : Option Expr × Nat → MetaM Expr
  | (some B, c) => mkAdd B (mkRawNatLit c)
  | (none, c) => pure (mkRawNatLit c)

/-- An atomic fact `l ≤ r` in linear form, with its proof. -/
structure LinLe where
  l : Option Expr × Nat
  r : Option Expr × Nat
  pf : Expr

/-- `L ≤ R` or `L < R` (as `L + 1 ≤ R`) between natural numbers. -/
def leParts? (t : Expr) : MetaM (Option (Expr × Expr)) := do
  let t := t.consumeMData
  match t.getAppFnArgs with
  | (``LE.le, #[ty, _, a, b]) => return if ty.isConstOf ``Nat then some (a, b) else none
  | (``LT.lt, #[ty, _, a, b]) =>
    if ty.isConstOf ``Nat then return some (← mkAdd a (mkRawNatLit 1), b) else return none
  | (``GE.ge, #[ty, _, a, b]) => return if ty.isConstOf ``Nat then some (b, a) else none
  | (``GT.gt, #[ty, _, a, b]) =>
    if ty.isConstOf ``Nat then return some (← mkAdd b (mkRawNatLit 1), a) else return none
  | _ => return none

/-- The linear form of a hypothesis `h : L ≤ R`. -/
def linHyp (h : Expr) (L R : Expr) : MetaM LinLe := do
  let (bl, cl, pl) ← linAddr L
  let (br, cr, pr) ← linAddr R
  let pf := mkAppN (mkConst ``addr_le_of_congr)
    #[L, R, ← linExpr (bl, cl), ← linExpr (br, cr), pl, pr, h]
  return ⟨(bl, cl), (br, cr), pf⟩

def sameBase : Option Expr → Option Expr → Bool
  | some a, some b => a == b
  | none, none => true
  | _, _ => false

/-- Prove `l ≤ r` (linear forms) from the atomic facts `hs`: `some (some pf)` proved,
`some none` refuted (same base, offsets in the wrong order), `none` unknown. -/
def proveLinLe (hs : Array LinLe) (l r : Option Expr × Nat) : MetaM (Option (Option Expr)) := do
  if sameBase l.1 r.1 then
    if l.2 ≤ r.2 then
      let h ← mkEqRefl (mkConst ``Bool.true)
      match l.1 with
      | some x =>
        return some (some (mkAppN (mkConst ``addr_le_same) #[x, mkRawNatLit l.2, mkRawNatLit r.2, h]))
      | none =>
        return some (some (mkAppN (mkConst ``Nat.le_of_ble_eq_true) #[mkRawNatLit l.2, mkRawNatLit r.2, h]))
    return some none
  -- `x + A ≤ y + B` gives `x + a ≤ y + b` when `a + B ≤ A + b`
  let (some x, a) := l | return none
  let (some y, b) := r | return none
  for h in hs do
    let (some x', A) := h.l | continue
    let (some y', B) := h.r | continue
    unless x' == x && y' == y do continue
    if a + B ≤ A + b then
      let hb ← mkEqRefl (mkConst ``Bool.true)
      return some (some (mkAppN (mkConst ``addr_le_hyp)
        #[x, y, mkRawNatLit A, mkRawNatLit B, mkRawNatLit a, mkRawNatLit b, h.pf, hb]))
  return none

/-- Prove an atomic goal `L ≤ R` / `L < R` / `L = R`, or a disjunction of them, from the
atomic facts `hs` (and, at the top, one case split on a disjunctive fact of `ors`).
`some (some pf)`: proved; `some none`: refuted (every disjunct contradicts its own offsets);
`none`: unknown. -/
partial def proveAddr (hs : Array LinLe) (t : Expr) : MetaM (Option (Option Expr)) := do
  let t := t.consumeMData
  if let some (P, Q) := t.app2? ``Or then
    let rp ← proveAddr hs P
    if let some (some pf) := rp then return some (some (mkApp3 (mkConst ``Or.inl) P Q pf))
    let rq ← proveAddr hs Q
    if let some (some pf) := rq then return some (some (mkApp3 (mkConst ``Or.inr) P Q pf))
    if rp == some none && rq == some none then return some none
    return none
  if let some (ty, L, R) := t.eq? then
    unless ty.isConstOf ``Nat do return none
    let (bl, cl, pl) ← linAddr L
    let (br, cr, pr) ← linAddr R
    unless sameBase bl br do return none
    unless cl == cr do return some none
    let h ← mkEqRefl (mkConst ``Bool.true)
    let core := match bl with
      | some x => mkAppN (mkConst ``addr_eq_same) #[x, mkRawNatLit cl, mkRawNatLit cr, h]
      | none => mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkRawNatLit cl)
    return some (some (mkAppN (mkConst ``addr_eq_congr)
      #[L, R, ← linExpr (bl, cl), ← linExpr (br, cr), pl, pr, core]))
  let some (L, R) ← leParts? t | return none
  let (bl, cl, pl) ← linAddr L
  let (br, cr, pr) ← linAddr R
  match ← proveLinLe hs (bl, cl) (br, cr) with
  | some (some core) =>
    return some (some (mkAppN (mkConst ``addr_le_congr)
      #[L, R, ← linExpr (bl, cl), ← linExpr (br, cr), pl, pr, core]))
  | r => return r.map fun _ => none

/-- `≤`/`<`/`=`, or a disjunction of them. -/
partial def addrShape (t : Expr) : Bool :=
  match t.consumeMData.app2? ``Or with
  | some (P, Q) => addrShape P && addrShape Q
  | none =>
    let t := t.consumeMData
    t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 || t.isAppOfArity ``Eq 3

/-- Decide a linear address side condition (see above). `some true`: closed; `some false`:
refuted by its own offsets (so `omega` need not try); `none`: not decided here. -/
def addrDisch (g : MVarId) : MetaM (Option Bool) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  -- only goals about addresses: `≤`/`<`/`=` on `Nat`, or disjunctions of them
  unless addrShape t do return none
  -- atomic facts, and the disjunctive ones for one case split
  let mut hs : Array LinLe := #[]
  let mut ors : Array (Expr × Expr × Expr) := #[]
  let goalFVars := (collectFVars {} t).fvarSet
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let fv := (collectFVars {} ty).fvarSet
    unless fv.toList.any goalFVars.contains do continue
    if let some (L, R) ← leParts? ty then
      hs := hs.push (← linHyp d.toExpr L R)
    else if let some (P, Q) := ty.consumeMData.app2? ``Or then
      if (← leParts? P).isSome && (← leParts? Q).isSome then ors := ors.push (d.toExpr, P, Q)
  match ← proveAddr hs t with
  | some (some pf) =>
    trace[janus.addr] "proved {t}"
    g.assign (← mkExpectedTypeHint pf t); return some true
  | some none =>
    trace[janus.addr] "refuted {t}"
    return some false
  | none => pure ()
  -- one case split on a disjunctive fact
  for (h, P, Q) in ors do
    let some (LP, RP) ← leParts? P | continue
    let some (LQ, RQ) ← leParts? Q | continue
    let r ← withLocalDeclD `hp P fun hp => do
      let rp ← proveAddr (hs.push (← linHyp hp LP RP)) t
      let some (some pp) := rp | return none
      withLocalDeclD `hq Q fun hq => do
        let rq ← proveAddr (hs.push (← linHyp hq LQ RQ)) t
        let some (some pq) := rq | return none
        let motive := t
        return some (mkAppN (mkConst ``Or.elim) #[P, Q, motive, h,
          ← mkLambdaFVars #[hp] pp, ← mkLambdaFVars #[hq] pq])
    if let some pf := r then
      g.assign (← mkExpectedTypeHint pf t)
      return some true
  return none

/-- The local hypotheses, those whose free variables overlap with those of the address of
the `accessible` goal `lhs` first (the region a pointer's access lies in is almost always
stated about that pointer; trying the others first costs failed `omega` calls). -/
initialize registerTraceClass `janus.addr

def accessibleOrder (lhs : Expr) : MetaM (Array LocalDecl) := do
  let addrFVars := (collectFVars {} (← instantiateMVars (lhs.getArg! 1))).fvarSet
  let mut first : Array LocalDecl := #[]
  let mut rest : Array LocalDecl := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let fv := (collectFVars {} (← instantiateMVars d.type)).fvarSet
    if fv.toList.any addrFVars.contains then first := first.push d else rest := rest.push d
  return first ++ rest

/-! ## Focused `omega`

Side conditions (address disjointness, no-wrap facts) are usually consequences of the few
hypotheses that talk about the same variables. `omega` on the full context also sees every
other fact, in particular the disjunctions of the aliasing preconditions, which it splits:
with six `Disjoint` facts, a disjointness side condition cost 100-400 ms. `omegaFocused` first
runs `omega` in the context restricted to the propositions whose free variables all occur in
the goal; only if that fails is the full context used. -/

/-- `omega` on `g` in the context restricted to the hypotheses that only mention free
variables of the goal. `true` if it closed the goal. -/
def omegaFocused (g : MVarId) : TacticM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let goalFVars := (collectFVars {} t).fvarSet
  if goalFVars.isEmpty then return false
  let lctx ← getLCtx
  let mut lctx' := lctx
  let mut dropped := 0
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    let fv := (collectFVars {} ty).fvarSet
    unless fv.toList.all goalFVars.contains do
      lctx' := lctx'.erase d.fvarId
      dropped := dropped + 1
  if dropped == 0 then return false
  let m ← mkFreshExprMVarAt lctx' (← getLocalInstances) t
  let saved ← saveState
  try
    let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| omega)))
    if gs.isEmpty then
      g.assign m
      return true
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

/-- `omega` for side conditions: linear address facts by `addrDisch`, then `omega` in the focused
context (`omegaFocused`), then in the full one. -/
initialize registerTraceClass `janus.omega

elab "janus_omega" : tactic => do
  let g ← getMainGoal
  match ← addrDisch g with
  | some true => replaceMainGoal []; return
  | some false => throwError "janus_omega: the address fact contradicts its own offsets"
  | none => pure ()
  let t0 ← IO.monoNanosNow
  if ← omegaFocused g then
    trace[janus.omega] "focused {((← IO.monoNanosNow) - t0) / 1000000} ms: {← g.getType}"
    replaceMainGoal []
  else
    let t1 ← IO.monoNanosNow
    try evalTactic (← `(tactic| omega))
    finally
      trace[janus.omega] "full {((← IO.monoNanosNow) - t1) / 1000000} ms (focused {(t1 - t0) / 1000000} ms): {← g.getType}"

/-! ## `rfl` equations for structurally recursive definitions

`simp [f]` unfolds a non-recursive definition by delta reduction: no proof term. A recursive `f`
is unfolded with its equation lemmas `f.eq_<k>` instead, and Lean does not tag those `@[defeq]`
(they need `f` unfolded, beyond the transparency `dsimp` works at), so every unfolding becomes a
propositional rewrite whose proof (`Eq.mpr`/`congrArg` over the instantiated right-hand side) is
part of the step proof. `janus_rfl_eqns f [attr]` restates each `f.eq_<k>` as `f.rfl_<k>` with
the proof `Eq.refl` (checked by the kernel when it is added, so nothing is trusted), tags it
`@[defeq]` and adds it to the simp set `attr`. `simp` then applies them as definitional
rewrites, exactly as it unfolds a non-recursive definition. Only for structural recursion
(where the equations hold by `rfl`); for anything else `addDecl` rejects the proof. -/

open Command in
elab "janus_rfl_eqns " id:ident " [" attr:ident "]" : command => do
  let names ← liftTermElabM do
    let n ← realizeGlobalConstNoOverloadWithInfo id
    let some eqs ← getEqnsFor? n | throwError "janus_rfl_eqns: no equation lemmas for {n}"
    let mut out := #[]
    for e in eqs, k in [0:eqs.size] do
      let ci ← getConstInfo e
      let val ← forallTelescope ci.type fun xs t => do
        let some (_, lhs, _) := t.eq? | throwError "janus_rfl_eqns: {e} is not an equation"
        mkLambdaFVars xs (← mkEqRefl lhs)
      let nm := n ++ Name.mkSimple s!"rfl_{k+1}"
      addDecl (.thmDecl { name := nm, levelParams := ci.levelParams, type := ci.type, value := val })
      defeqAttr.setTag nm
      out := out.push nm
    return out
  for nm in names do
    elabCommand (← `(attribute [$attr:ident] $(mkIdent nm):ident))

/-! ## Path merging (`set_option janus.merge true`)

A branch whose two sides rejoin (`if c { x++ }; …`, a `&&` condition, a lock count that is
or is not 1) doubles the work of every later instruction: each path is executed to the end on
its own. With `janus.merge`, the run steps the pending path with the smallest pc first, so that
the paths of a forward diamond wait for each other at the join. Two pending goals at the same
pc whose targets are the same expression (the same state, the same postcondition) and whose
local contexts differ only in branch hypotheses (`hbr`) are merged: the branch hypotheses that
are not common to both are cleared and one goal is assigned to the other, so the rest of the
run is executed once. Clearing hypotheses is always sound; it loses the facts of the branches
taken, which is why merging is opt-in (a later branch decided by an earlier condition becomes
two paths again, and a proof may need the dropped fact). -/

/-- The branch hypotheses (`hbr`) of a local context and the other declarations. -/
def splitBranchHyps (lctx : LocalContext) : Array FVarId × Array FVarId := Id.run do
  let mut hb := #[]
  let mut rest := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    if d.userName.eraseMacroScopes == `hbr then hb := hb.push d.fvarId
    else rest := rest.push d.fvarId
  return (hb, rest)

/-- What path merging needs to know about an ISA's state: the memory type (never
generalised), the register-file chains `setR (… (x.regs) …) r v` (`(setR, regs)`) and the
simprocs that remove a write-back of a register's own value (`setR f r (x.regs r) = f`). -/
structure MergeSpec where
  memTypes : List Name
  regChains : List (Name × Name) := []
  restore : List Name := []

/-- A register-file chain `setR (… (setR base r₁ v₁) …) rₖ vₖ`, innermost first: the base and the
writes `(index, literal, value)`. -/
partial def regWrites (setR regs : Name) (f : Expr) (acc : List (Expr × Nat × Expr) := []) :
    Option (Expr × List (Expr × Nat × Expr)) :=
  if f.isAppOfArity setR 3 then
    match (f.getArg! 1).nat? <|> (f.getArg! 1).rawNatLit? with
    | some r => regWrites setR regs (f.getArg! 0) ((f.getArg! 1, r, f.getArg! 2) :: acc)
    | none => none
  else if f.isAppOfArity regs 1 then some (f, acc)
  else none

/-- Anti-unification of two goal targets: the common term, with every maximal pair of
differing subterms replaced by a fresh free variable (`vars`: the variable, its type and the two
subterms; the same pair, the same variable). A subterm is only generalised if it has no loose
bound variables, both sides have the same type and that type is not a memory (a memory is never
generalised: the run needs its stores; differing memories make the goals unmergeable). Two
register-file chains over the same base are aligned by register: a register written on one side
only gets a variable whose other value is the base's (`x.regs r`, removed again by the
`restore` simprocs when the merged goal is instantiated). -/
partial def antiUnify (spec : MergeSpec) (a b : Expr) :
    StateRefT (Array (FVarId × Expr × Expr × Expr)) MetaM Expr := do
  if a == b then return a
  let fresh (ta a b : Expr) : StateRefT (Array (FVarId × Expr × Expr × Expr)) MetaM Expr := do
    for (v, _, a', b') in ← get do
      if a' == a && b' == b then return mkFVar v
    let v ← mkFreshFVarId
    modify (·.push (v, ta, a, b))
    return mkFVar v
  for (setR, regs) in spec.regChains do
    if let (some (baseA, wa), some (baseB, wb)) := (regWrites setR regs a, regWrites setR regs b) then
      if baseA == baseB && (wa.map (·.2.1) != wb.map (·.2.1)) then
        let idx := (wa.map (·.2.1) ++ wb.map (·.2.1)).eraseDups.mergeSort
        let wty ← instantiateMVars (← inferType (baseA.beta #[mkNatLit 0]))
        let mut acc := baseA
        for r in idx do
          let va := wa.find? (·.2.1 == r)
          let vb := wb.find? (·.2.1 == r)
          let (ie, v) ← match va, vb with
            | some (ie, _, x), some (_, _, y) => pure (ie, ← antiUnify spec x y)
            | some (ie, _, x), none => pure (ie, ← fresh wty x (mkApp baseA ie))
            | none, some (ie, _, y) => pure (ie, ← fresh wty (mkApp baseA ie) y)
            | none, none => unreachable!
          acc := mkApp3 (mkConst setR) acc ie v
        return acc
  let fa := a.getAppFn
  let fb := b.getAppFn
  if a.isApp && b.isApp && fa == fb && a.getAppNumArgs == b.getAppNumArgs && !fa.isMVar then
    let xs := a.getAppArgs
    let ys := b.getAppArgs
    let mut out := #[]
    for x in xs, y in ys do
      out := out.push (← antiUnify spec x y)
    return mkAppN fa out
  if a.hasLooseBVars || b.hasLooseBVars || a.hasMVar || b.hasMVar then
    throwError "antiUnify: bound variables{indentExpr a}\nvs{indentExpr b}"
  let ta ← instantiateMVars (← inferType a)
  if ta.getAppFn.constName?.any (spec.memTypes.contains ·) then
    throwError "the memories differ{indentExpr a}\nvs{indentExpr b}"
  if (← isProp ta) || ta.isSort then throwError "antiUnify: proposition or type"
  unless ← withReducible (isDefEq ta (← inferType b)) do throwError "antiUnify: types"
  fresh ta a b

/-- `e` with the register write-backs `setR f r (x.regs r)` removed (the `restore` simprocs). -/
def restoreRegs (spec : MergeSpec) (e : Expr) : MetaM Simp.Result := do
  if spec.restore.isEmpty then return { expr := e }
  let cfg : Simp.Config := { zeta := false, iota := false, proj := false, decide := false, beta := false, eta := false }
  let ctx ← Simp.mkContext (config := cfg)
    (simpTheorems := #[]) (congrTheorems := ← getSimpCongrTheorems)
  let mut sp : Simp.Simprocs := {}
  for n in spec.restore do sp ← sp.add n (post := true)
  let (r, _) ← simp e ctx #[sp] none
  return r

/-- Merge `h` into `g` (same pc): `some g'` (the goal that remains; both `g` and `h` are
assigned through it) if their contexts differ only in branch hypotheses and their targets differ
in at most `maxVars` non-memory subterms (registers, flags), which the merged goal quantifies
over (`∀ jv…`; e.g. a scratch register or the flags that the two sides of a diamond left
differently, and that the code after the join overwrites). -/
def tryMerge (spec : MergeSpec) (g h : MVarId) (maxVars : Nat := 8) : MetaM (Option MVarId) := do
  let (hbG, restG) := splitBranchHyps (← g.getDecl).lctx
  let (hbH, restH) := splitBranchHyps (← h.getDecl).lctx
  unless restG == restH do
    trace[janus] "not merged: the local contexts differ beyond branch hypotheses"
    return none
  let tg ← instantiateMVars (← g.getType)
  let th ← instantiateMVars (← h.getType)
  let some (tmpl, vars) ← g.withContext (try some <$> (antiUnify spec tg th).run #[]
      catch e => do
        trace[janus] "not merged: {e.toMessageData}"
        pure none) | return none
  if vars.size > maxVars then
    trace[janus] "not merged: {vars.size} differing subterms, e.g.{MessageData.joinSep ((vars.toList.take 4).map fun (_, _, a, b) => m!"{indentExpr a}\nvs{indentExpr b}") "\n"}"
    return none
  let dropG := hbG.filter (!hbH.contains ·)
  let dropH := hbH.filter (!hbG.contains ·)
  let saved ← saveState
  let g' ← g.tryClearMany dropG
  let h' ← h.tryClearMany dropH
  let idsG := (← g'.getDecl).lctx.getFVarIds
  let idsH := (← h'.getDecl).lctx.getFVarIds
  if idsG != idsH then saved.restore; return none
  if vars.isEmpty then
    h'.assign (mkMVar g')
    return some g'
  -- `∀ jv…, tmpl`, instantiated with each side's subterms
  let fvs := vars.map (mkFVar ·.1)
  let body := tmpl.abstract fvs
  let mut ty := body
  for i in [0:vars.size] do
    let j := vars.size - 1 - i
    ty := .forallE (Name.mkSimple s!"jv{j}") ((vars[j]!.2.1).abstractRange j fvs) ty .default
  let ok ← g'.withContext do try Meta.check ty; pure true catch _ => pure false
  unless ok do saved.restore; return none
  let m ← g'.withContext (mkFreshExprSyntheticOpaqueMVar ty (← g'.getTag))
  -- each side: the merged goal at its values, up to the register write-backs
  let inst (side : MVarId) (vals : Array Expr) (target : Expr) : MetaM Bool := side.withContext do
    let pf := mkAppN m vals
    let r ← restoreRegs spec (body.instantiateRev vals)
    unless r.expr == target do
      unless ← withReducible (isDefEq r.expr target) do return false
    match r.proof? with
    | none => side.assign pf
    | some eq => side.assign (← mkEqMP eq pf)
    return true
  unless ← inst g' (vars.map (·.2.2.1)) tg do
    trace[janus] "not merged: the merged goal does not instantiate to the first one"
    saved.restore; return none
  unless ← inst h' (vars.map (·.2.2.2)) th do
    trace[janus] "not merged: the merged goal does not instantiate to the second one"
    saved.restore; return none
  let (_, g'') ← m.mvarId!.introNP vars.size
  return some g''

/-- Pick the pending goal to step next when merging: the one with the smallest pc (goals
without a literal pc, e.g. outcomes, first), after merging into it every other pending goal
at the same pc that `tryMerge` accepts. -/
def pickMerged (spec : MergeSpec) (pcOf : MVarId → MetaM (Option Nat))
    (todo : List (MVarId × Bool)) :
    MetaM (List (MVarId × Bool)) := do
  let mut pend : Array (MVarId × Bool × Option Nat) := #[]
  for (g, f) in todo do
    if ← g.isAssigned then continue
    pend := pend.push (g, f, ← pcOf g)
  if pend.isEmpty then return []
  let key (o : Option Nat) : Nat := match o with | none => 0 | some c => c + 1
  let mut best := 0
  for i in [1:pend.size] do
    if key pend[i]!.2.2 < key pend[best]!.2.2 then best := i
  let (g0, f0, pc0) := pend[best]!
  let mut g := g0
  let mut rest := #[]
  for i in [0:pend.size] do
    if i == best then continue
    let (h, fh, pch) := pend[i]!
    if pc0.isSome && pch == pc0 then
      if let some g' ← tryMerge spec g h then
        trace[janus] "merged two paths at pc {hex pc0.get!}"
        g := g'
        continue
    rest := rest.push (h, fh)
  return (g, f0) :: rest.toList

end Janus.Tactic.Common
