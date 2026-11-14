import Lean
import Janus.GoABI
import Janus.Spec.Basic

/-!
# `janus_pre_setRet` (arm64): migrating a precondition to the v0.4.0 `Ensures`

Since v0.4.0 the precondition of `Ensures`, `EnsuresWithin`, `EnsuresGo`, `EnsuresGoX` and
`RunsAtLeastOnCall` is evaluated on the call state **before** the return address is installed
(`State.setRet`). A proof written for the old statement runs on the state with `X30 = ret`, so it
needs the precondition at `s.setRet ret`:

```
theorem correctness : Ensures prog entry args pre post :=
  Ensures.of_old (by janus_pre_setRet) (by
    intro ret hret s hs hpre
    …  -- the old proof, unchanged
  )
```

`janus_pre_setRet` proves the first argument of `Ensures.of_old` (`∀ s ret, CallSetup0 entry args s → RetAddr p ret →
pre s → pre (s.setRet ret)`): it introduces `s ret hs hret hp`, unfolds the listed definitions and the
standard memory predicates, and rewrites `s.setRet ret` away with the `setRet_*` simp lemmas (on
arm64 only `X30` changes, so every register, `SP`, the flags and the memory are untouched), then
closes the goal from `hp`. It fails, by design, on a precondition that constrains `X30` itself: such
a precondition is not invariant under installing the return address, and the new theorem must not
state it.

`janus_split_hyps` destructures every `∧` / `∃` hypothesis of the context into its components
(used by the amd64 variant to give `omega` the facts of the precondition).
-/

namespace Janus.Tactic

open Lean Elab Tactic Meta

/-- Keeps a copy of a hypothesis out of `omega`'s sight (it flattens every conjunction of the context, and a second copy of a
precondition doubles the disjunction case splits of each side condition). Unfolds at default transparency (`exact`). -/
def Hide (p : Prop) : Prop := p

theorem Hide.elim {p : Prop} (h : Hide p) : p := h

/-- Destructure every hypothesis of the form `A ∧ B` or `∃ x, A` of the local context, repeatedly
(except the one named by `keep`). With `deep`, a hypothesis whose type *unfolds* (default transparency) to a
structure-like proposition (`∧`, `∃`, `StackGuardOK`, a consumer's `CallEnv`, …) is split too. -/
syntax "janus_split_hyps" (&" deep")? (&" keep " ident)? : tactic

elab_rules : tactic
  | `(tactic| janus_split_hyps $[deep%$dp]? $[keep $k:ident]?) => do
    let keepName : Option Name := k.map (·.getId)
    let deep := dp.isSome
    let mut fuel := if deep then 400 else 200
    while fuel > 0 do
      fuel := fuel - 1
      let g ← getMainGoal
      let some fv ← g.withContext do
          for d in (← getLCtx) do
            if d.isImplementationDetail || keepName == some d.userName then continue
            let ty ← instantiateMVars d.type
            if deep then
              let ty' ← whnfD ty
              let some c := ty'.getAppFn.constName? | continue
              unless (← isProp ty') do continue
              let some (.inductInfo ii) := (← getEnv).find? c | continue
              if ii.ctors.length == 1 && ii.numIndices == 0 && !ii.isRec && c != ``Eq && c != ``HEq && c != ``Iff
                  && c != ``True && c != ``Acc && c != ``Subtype then return some d.fvarId
            else
              let ty ← whnfR ty
              if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then return some d.fvarId
          return none
        | break
      let subs ← g.cases fv
      replaceMainGoal (subs.map (·.mvarId)).toList

/-- `janus_disj_omega`: a side condition `a + n ≤ RSP ∨ RSP + 8 ≤ a` that follows from ONE disjunction of the context
(`x + n ≤ RSP - k ∨ RSP + m ≤ x`, an unfolded `Outside`/`Apart` of the precondition): split that disjunction, clear the other
disjunctions and close both branches with `omega`. A plain `omega` splits every disjunction of the context (exponential in
their number for a big precondition); this tries each disjunction on its own, which is linear in their number. -/
elab "janus_disj_omega" : tactic => do
  let g ← getMainGoal
  let hyps ← g.withContext do
    let mut acc : Array FVarId := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isAppOfArity ``Or 2 then acc := acc.push d.fvarId
    return acc
  for hy in hyps do
    let st ← saveState
    try
      let mut g' := g
      for o in hyps do
        if o != hy then g' ← g'.tryClear o
      replaceMainGoal [g']
      let hs ← g'.withContext (Term.exprToSyntax (mkFVar hy))
      Tactic.withoutRecover <| evalTactic (← `(tactic| rcases $hs:term with h | h <;> omega))
      return
    catch _ => st.restore
  throwError "janus_disj_omega: no single disjunction of the context closes the goal"

/-- `janus_have_rsp8 h : T`: add `h : s.mem.accessible (s.regs 4).toNat 8 true = true` (the return slot is writable)
when some hypothesis `m.accessible a n true = true` of the context contains `[RSP, RSP + 8)` (syntactic scan of
the hypotheses, then `accessible_mono` with the two bounds closed by `omega`); no-op if none does. -/
syntax "janus_have_rsp8 " ident " : " term : tactic

elab_rules : tactic
  | `(tactic| janus_have_rsp8 $h:ident : $T:term) => do
    let g ← getMainGoal
    let hyps ← g.withContext do
      let mut acc : Array Expr := #[]
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Janus.Arm64.Memory.accessible 4 then
          acc := acc.push d.toExpr
      return acc
    -- first without splitting the context's disjunctions (a failing `omega` is exponential in their number), then with
    for full in [false, true] do
      for hy in hyps do
        let hs ← g.withContext (Term.exprToSyntax hy)
        let st ← saveState
        try
          Tactic.withoutRecover <|
            evalTactic (← if full then
              `(tactic| have $h : $T := Janus.Arm64.Memory.accessible_mono _ $hs (by omega) (by omega))
            else
              `(tactic| have $h : $T := Janus.Arm64.Memory.accessible_mono _ $hs (by omega -splitDisjunctions) (by omega -splitDisjunctions)))
          return
        catch _ => st.restore

/-- The body of `janus_pre_setRet`, on the introduced `s ret hret hp` (names passed in so that the
variants for preconditions with more arguments, `janus_pre_setRet_k`, share it). -/
syntax "janus_pre_setRet_core " ident ident ident ident " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| janus_pre_setRet_core $s $ret $hret $hp [$ds,*]) => do
    -- `CStack` lives in a module imported after this one: an identifier built with `mkIdent` resolves where the tactic is used
    let c1 := mkIdent `Janus.CABI.CStack
    let mut us ← `(tactic| skip)
    for d in ds.getElems do
      us ← `(tactic| ($us; try simp only [$d] at $hp:ident ⊢))
    `(tactic|
      ($us
       try simp only [Janus.GoABI.StackWritable, Janus.GoABI.SPAligned, Janus.GoABI.FPConvention,
         Janus.GoABI.ClosureCtx, Janus.GoABI.StackWords, Janus.GoABI.stackWord, Janus.GoABI.stackArgOffset,
         Janus.GoABI.StackGuardOK, Janus.GoABI.stackguard0] at $hp:ident ⊢
       try simp only [$c1:ident] at $hp:ident ⊢
       try simp only [Janus.GoABI.setRet_pc, Janus.GoABI.setRet_sp, Janus.GoABI.setRet_flags,
         Janus.GoABI.setRet_mem, Janus.GoABI.setRet_dczid, Janus.GoABI.setRet_vregs,
         Janus.GoABI.setRet_tpidr, Janus.GoABI.setRet_fpcr, Janus.GoABI.setRet_fpsr,
         Janus.GoABI.setRet_excl, Janus.GoABI.setRet_exclPass] at $hp:ident ⊢
       try simp (disch := first | decide | simp) only [Janus.GoABI.setRet_regs_of_ne] at $hp:ident ⊢
       all_goals first | exact $hp | assumption | simpa using $hp))

syntax "janus_pre_setRet" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| janus_pre_setRet) => `(tactic| janus_pre_setRet [])
  | `(tactic| janus_pre_setRet [$ds,*]) => `(tactic|
      (intro s ret hs hret hp
       janus_pre_setRet_core s ret hret hp [$ds,*]))

/-- `janus_pre_setRet_k`: as `janus_pre_setRet` for a precondition on a state and a kernel state
(`EnsuresK`: `pre s k`, goal `∀ s k ret, CallSetup0 … s → RetAddr p ret → pre s k → pre (s.setRet ret) k`). -/
syntax "janus_pre_setRet_k" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| janus_pre_setRet_k) => `(tactic| janus_pre_setRet_k [])
  | `(tactic| janus_pre_setRet_k [$ds,*]) => `(tactic|
      (intro s k ret hs hret hp
       janus_pre_setRet_core s ret hret hp [$ds,*]))

/-- `janus_pre_setRet_c`: as `janus_pre_setRet` for a precondition with a `caller` hypothesis (`EnsuresGrow`: the goal is
`∀ s ret, CallSetup0 … s → RetAddr p ret → pre s → caller (s.setRet ret) → pre (s.setRet ret)`; `hc` is available to the proof). -/
syntax "janus_pre_setRet_c" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules 
  | `(tactic| janus_pre_setRet_c) => `(tactic| janus_pre_setRet_c [])
  | `(tactic| janus_pre_setRet_c [$ds,*]) => `(tactic|
      (intro s ret hs hret hp hc
       janus_pre_setRet_core s ret hret hp [$ds,*]))

/-- `janus_ensures_old [defs]`: reduce a goal `Ensures … pre post` (or `EnsuresWithin`, `EnsuresGo`,
`EnsuresGoX`, `RunsAtLeastOnCall`, and the other main-theorem forms `Ensures0`, `CEnsures`, `CEnsuresA`,
`EnsuresC`, `CEnsuresC`, `EnsuresK`, `EnsuresGrow`) to the pre-v0.4.0 statement `∀ ret, RetAddr … → ∀ s,
<setup> … → pre s → …` (the goal an old proof starts from: `intro ret hret s hs hpre` follows), proving the
invariance of `pre` under `setRet` with `janus_pre_setRet [defs]`. The form's module must be imported
(the alternatives name each form's bridge). -/
syntax "janus_ensures_old" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

/-- The bridge of each main-theorem form (arm64) and the pre-setRet tactic that proves its `hinv`. The names
are resolved where `janus_ensures_old` is used (the form's module need not be imported here). -/
def ensuresOldForms : List (Name × Nat) :=
  [(`Janus.GoABI.Ensures.of_old, 0), (`Janus.GoABI.EnsuresWithin.of_old, 0),
   (`Janus.GoABI.EnsuresGoX.of_old, 0), (`Janus.GoABI.EnsuresGo.of_old, 0),
   (`Janus.GoABI.RunsAtLeastOnCall.of_old, 0), (`Janus.GoABI0.Ensures0.of_old, 0),
   (`Janus.CABI.CEnsures.of_old, 0), (`Janus.CABI.CEnsuresA.of_old, 0),
   (`Janus.FFI.EnsuresC.of_old, 0), (`Janus.FFI.CEnsuresC.of_old, 0),
   (`Janus.Kernel.EnsuresK.of_old, 1), (`Janus.Contracts.Stack.EnsuresGrow.of_old, 2)]

open Lean Macro in
macro_rules
  | `(tactic| janus_ensures_old) => `(tactic| janus_ensures_old [])
  | `(tactic| janus_ensures_old [$ds,*]) => do
    let mut acc ← `(Lean.Parser.Tactic.tacticSeq| fail "janus_ensures_old: the goal is not a main-theorem form with an `of_old` bridge")
    for (n, kind) in ensuresOldForms.reverse do
      let alt ← if kind == 1 then
          `(Lean.Parser.Tactic.tacticSeq| refine $(mkIdent n) (by janus_pre_setRet_k [$ds,*]) ?_)
        else if kind == 2 then
          `(Lean.Parser.Tactic.tacticSeq| refine $(mkIdent n) (by janus_pre_setRet_c [$ds,*]) ?_)
        else `(Lean.Parser.Tactic.tacticSeq| refine $(mkIdent n) (by janus_pre_setRet [$ds,*]) ?_)
      acc ← `(Lean.Parser.Tactic.tacticSeq| first | $alt | $acc)
    `(tactic| ($acc))

end Janus.Tactic

namespace Janus.GoABI

open Janus Janus.Arm64 Janus.Tactic

/-- Weaken the precondition and the postcondition, with the pre-v0.4.0 `hpost` (about the state that already holds the
return address in `X30`: `pre' s → post s s' → post' s s'`). The invariance of `pre'` under `setRet` is the new
obligation, proved by default with `janus_pre_setRet`. (`Ensures.mono_ret` states `hpost` at `s.setRet ret`.) -/
theorem Ensures.mono {p : Program} {entry : Nat} {args : List W64} {pre pre' : State → Prop}
    {post post' : State → State → Prop}
    (h : Ensures p entry args pre post) (hpre : ∀ s, pre' s → pre s)
    (hpost : ∀ s s', pre' s → post s s' → post' s s')
    (hinv : Ensures.SetRetInv p entry args pre' := by janus_pre_setRet) :
    Ensures p entry args pre' post' :=
  fun s hs hp ret hret => (h s hs (hpre s hp) ret hret).mono fun _ ⟨ha, hq⟩ =>
    ⟨ha, hpost _ _ (hinv s ret hs hret hp) hq⟩

end Janus.GoABI
