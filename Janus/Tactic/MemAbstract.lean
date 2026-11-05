import Lean
import Janus.Tactic.Common

/-!
# `janus_mem_abstract`: the stores of a run as a `MemFrame`, the memory as an atom

After `janus_run` the memory of a goal is a chain `((m₀.writeLE a₁ k₁ v₁).writeLE a₂ k₂ v₂)…` of every
store of the path (a 40-limb routine on the stack: dozens of stores, each value a carry term). A read
whose address `omega` cannot show apart from a store stays as `(chain).readLE b n`, and the whole chain
is part of the goal (80 K characters in the `AddMod` fast path), although the proof only needs
"outside the stored ranges, the memory is `m₀`".

`janus_mem_abstract` (opt-in; `janus_run` never calls it)

1. finds the maximal store chains `M` of the goal (at least `min` stores, default 2) over a base `m₀`;
2. proves `hf_M : MemFrame m₀ M [(a₁, a₁ + k₁), …]` (the ranges of the stores; kernel-checked, by
   `janus_frame`'s `proveFrame`) and adds it to the context;
3. rewrites the goal with `hf_M.readLE` / `hf_M.accessible` (a read outside every stored range, side
   condition by `omega`): reads of the inputs through the stack stores become reads of `m₀`;
4. if `M` then occurs in the goal only as the memory argument of `MemFrame`/`accessible` (nothing reads
   the stored values any more), replaces it by a fresh atom `m'` (`generalize`): the goal no longer
   contains the chain, `hf : MemFrame m₀ m' ranges` states what is known of it. If some read of `M`
   remains (a read of a stored value, or one whose address is not provably outside), the chain stays
   (the goal is not abstracted, since the stored values matter), but `hf` is still added and used.
-/

namespace Janus.Tactic.MemAbstract

open Lean Meta Elab Tactic

/-- `janus_outside_disch`: the side condition `Outside a n rs` of a `MemFrame` read rule. -/
elab "janus_outside_disch" : tactic => do
  unless ← Common.dischargeOutside (← getMainGoal) do
    throwError "janus_outside_disch: cannot show the read outside the ranges"
  replaceMainGoal []

private def isStore (e : Expr) : Bool := e.isAppOfArity ``Janus.Arm64.Memory.writeLE 4

/-- The base memory of a store chain and its stores (address, length), last store first. -/
partial def chainOf (m : Expr) (acc : Array (Expr × Expr)) : Expr × Array (Expr × Expr) :=
  if isStore m then chainOf (m.getArg! 0) (acc.push (m.getArg! 1, m.getArg! 2)) else (m, acc)

/-- The maximal store chains of `e` with at least `minLen` stores, in order of first occurrence. -/
def findChains (e : Expr) (minLen : Nat) : Array Expr := Id.run do
  let mut out : Array Expr := #[]
  let mut seen : Std.HashSet Expr := {}
  let mut todo : Array Expr := #[e]
  while todo.size > 0 do
    let x := todo.back!
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    if isStore x then
      let (_, st) := chainOf x #[]
      if st.size ≥ minLen && !out.contains x then out := out.push x
      -- stored addresses and values may contain further chains; the spine itself is one chain
      let mut m := x
      while isStore m do
        todo := todo.push (m.getArg! 1) |>.push (m.getArg! 2) |>.push (m.getArg! 3)
        m := m.getArg! 0
      todo := todo.push m
      continue
    match x with
    | .app f a => todo := todo.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | _ => pure ()
  return out

/-- The ranges `[(a, a + k), …]` of the stores of a chain, without repetitions. -/
def rangesOf (m : Expr) : MetaM Expr := do
  let (_, st) := chainOf m #[]
  let mut seen : Array (Expr × Expr) := #[]
  for (a, k) in st.reverse do
    unless seen.contains (a, k) do seen := seen.push (a, k)
  let nat := mkConst ``Nat
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) nat nat
  let elems ← seen.toList.mapM fun (a, k) => do
    mkAppM ``Prod.mk #[a, ← mkAppM ``HAdd.hAdd #[a, k]]
  mkListLit pairTy elems

/-- Is `M` used in `e` other than as a memory argument of `MemFrame` / `accessible` (that is: does anything
depend on its stored values)? -/
partial def otherUses (e M : Expr) : Bool :=
  if e == M then true
  else if e.isAppOfArity ``Janus.MemFrame 3 then
    (e.getArg! 0 != M && otherUses (e.getArg! 0) M) || (e.getArg! 1 != M && otherUses (e.getArg! 1) M) ||
      otherUses (e.getArg! 2) M
  else if e.isAppOfArity ``Janus.Arm64.Memory.accessible 4 then
    (e.getArg! 0 != M && otherUses (e.getArg! 0) M) || otherUses (e.getArg! 1) M ||
      otherUses (e.getArg! 2) M || otherUses (e.getArg! 3) M
  else match e with
    | .app f a => otherUses f M || otherUses a M
    | .lam _ t b _ | .forallE _ t b _ => otherUses t M || otherUses b M
    | .mdata _ b | .proj _ _ b => otherUses b M
    | .letE _ t v b _ => otherUses t M || otherUses v M || otherUses b M
    | _ => false

/-- `janus_mem_abstract` (chains of at least 2 stores) or `janus_mem_abstract n` (at least `n`). -/
syntax (name := janusMemAbstract) "janus_mem_abstract" (ppSpace num)? : tactic

@[tactic janusMemAbstract] def evalMemAbstract : Tactic := fun stx => do
  let minLen := (stx[1].getOptional?.map (·.isNatLit?.getD 2)).getD 2
  let g0 ← getMainGoal
  let chains := findChains (← instantiateMVars (← g0.getType)) minLen
  if chains.isEmpty then
    throwError "janus_mem_abstract: no store chain of at least {minLen} stores in the goal"
  let mut i : Nat := 0
  for M in chains do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    -- the chain may have been rewritten away by an earlier step
    unless (t.find? (· == M)).isSome do continue
    let (m0, _) := chainOf M #[]
    let rs ← g.withContext (rangesOf M)
    let hfTy ← g.withContext (mkAppM ``Janus.MemFrame #[m0, M, rs])
    let hfName := Name.mkSimple s!"hf_mem{i}"
    let memName := Name.mkSimple s!"mem{i}"
    i := i + 1
    -- the frame, proved in the goal's context
    let pf ← g.withContext do
      let pg ← mkFreshExprSyntheticOpaqueMVar hfTy
      Common.proveFrame pg.mvarId!
      instantiateMVars pg
    let (_, g1) ← (← g.assert hfName hfTy pf).intro1P
    replaceMainGoal [g1]
    let hfS := mkIdent hfName
    -- reads outside the stored ranges go to the base memory
    try
      evalTactic (← `(tactic| simp (disch := janus_outside_disch) only
        [Janus.MemFrame.readLE $hfS, Janus.MemFrame.accessible $hfS]))
    catch _ => pure ()
    -- abstract the chain if nothing reads its stored values
    let g2 ← getMainGoal
    let t2 ← instantiateMVars (← g2.getType)
    if (t2.find? (· == M)).isSome then
      if otherUses t2 M then
        logInfo m!"janus_mem_abstract: the stored values of store chain {i} are still read in the goal; the chain stays (hypothesis {hfName} added)"
      else
        let mS ← g2.withContext (Term.exprToSyntax M)
        evalTactic (← `(tactic| generalize $mS = $(mkIdent memName) at $hfS ⊢))

end Janus.Tactic.MemAbstract
