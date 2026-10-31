import Lean

/-!
# `janus_assumption`: `assumption` that does not unify with every giant hypothesis

After `janus_run calls [...]` the context holds dozens of hypotheses, many of them huge
(callee post-conditions with whole `State` records and nested `writeLE` memories).
`assumption` (and `‹T›`) tests the wanted type against the hypotheses with default
transparency, one after the other, so a mismatch against a giant hypothesis can unfold definitions
along the whole term: seconds to minutes per use. `janus_assumption` tries, last hypothesis first,

1. the hypotheses whose type has the same head constant as the goal, at reducible
   transparency (this succeeds for every use of the usual shape: `InRanges _ 32 rt`, `a ≤ b`, ...);
2. all hypotheses at reducible transparency;
3. the ordinary `assumption`.

It proves exactly what `assumption` proves (rule 3 is the fallback); it only chooses faster. Use it
as `by janus_assumption` where `‹T›` was used.
-/

namespace Janus.Tactic

open Lean Meta Elab Tactic

/-- The head constant of a type (looking through `mdata`). -/
private def headConst? (e : Expr) : Option Name := e.consumeMData.getAppFn.constName?

def janusAssumption (g : MVarId) : MetaM Bool := g.withContext do
  g.checkNotAssigned `janus_assumption
  let target ← instantiateMVars (← g.getType)
  let hd := headConst? target
  let decls := (← getLCtx).decls.toList.filterMap id |>.filter (fun d => !d.isImplementationDetail) |>.reverse
  -- 1. same head constant, reducible
  for pass in [0:2] do
    for d in decls do
      if pass == 0 then
        match hd with
        | some h =>
          unless headConst? (← instantiateMVars d.type) == some h do continue
        | none => continue
      let saved ← saveState
      if ← withReducible (isDefEq target d.type) then
        g.assign d.toExpr
        return true
      saved.restore
  -- 3. the ordinary assumption
  try
    g.assumption
    return true
  catch _ => return false

/-- `assumption` that avoids unifying the goal with every giant hypothesis (see the module doc). -/
elab "janus_assumption" : tactic => withMainContext do
  let g ← getMainGoal
  if ← janusAssumption g then
    replaceMainGoal []
  else
    throwError "janus_assumption: no hypothesis matches{indentExpr (← g.getType)}"

end Janus.Tactic
