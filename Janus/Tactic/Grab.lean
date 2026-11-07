import Lean

/-!
# `janus_grab`: content-based lookup of facts after `janus_run` / a summary application

Positional `rename_i` after `janus_run … calls [..]` (or after applying a callee's summary) binds names by the position
of the hypotheses, and silently re-binds them when a contract gains or reorders a conjunct. `janus_grab` finds the
hypothesis by its content instead:

* `janus_grab c as h`: `h` names the first local hypothesis whose type mentions the constant `c`;
* `janus_grab 112 as h`: `h` names the first `MemFrame` hypothesis whose range list mentions the numeral `112`
  (the callee's output object is at `SP - 112`);
* `janus_grab fr f 3 as h`: `h` names the hypothesis `st.f 3 = _`, where `st` is the returned state of the callee whose
  `MemFrame` hypothesis is `fr` (its final memory is `st.mem`).

Each fails with a message naming what was not found. The linter `linter.janusRenameI` reports a `rename_i` after
`janus_run`/`janus64_run` (disable with `set_option linter.janusRenameI false`).
-/

namespace Janus.Tactic.Grab

open Lean Elab Tactic Meta Linter

/-- does `e` contain the numeral `n` (as `OfNat.ofNat _ n _` or a raw literal)? -/
def hasNumeral (e : Expr) (n : Nat) : Bool :=
  (e.find? fun x =>
    (x.isAppOfArity ``OfNat.ofNat 3 && (x.getArg! 1).rawNatLit? == some n) || x.rawNatLit? == some n).isSome

private def noteAs (n : Name) (d : LocalDecl) (ty : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let (_, g') ← g.withContext (g.note n (mkFVar d.fvarId) ty)
  replaceMainGoal [g']

/-- After binding the first match: warn when other hypotheses also match (the lookup is by content, not position, but
the first of several is not necessarily the one meant; refine the pattern). -/
private def warnIfAmbiguous (what : String) (n : Name) (matches_ : Nat) : TacticM Unit := do
  if matches_ > 1 then
    logWarning m!"janus_grab {what}: {matches_} hypotheses match; `{n}` is the first. Select the one you mean by a more specific pattern (another constant, numeral or projection)"

/-- `janus_grab c as h`: name `h` the first local hypothesis whose type mentions the constant `c`. -/
elab "janus_grab " c:ident " as " n:ident : tactic => do
  let cn ← realizeGlobalConstNoOverloadWithInfo c
  let g ← getMainGoal
  let mut first : Option (LocalDecl × Expr) := none
  let mut cnt := 0
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (ty.find? fun e => e.isConstOf cn).isSome then
      if first.isNone then first := some (d, ty)
      cnt := cnt + 1
  let some (d, ty) := first | throwError "janus_grab: no hypothesis mentions {cn}"
  noteAs n.getId d ty
  warnIfAmbiguous s!"{cn}" n.getId cnt

/-- `janus_grab k as h`: name `h` the first `MemFrame` hypothesis whose range list mentions the numeral `k`. -/
elab "janus_grab " k:num " as " n:ident : tactic => do
  let g ← getMainGoal
  let mut first : Option (LocalDecl × Expr) := none
  let mut cnt := 0
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf `Janus.MemFrame && hasNumeral ty.getAppArgs.back! k.getNat then
      if first.isNone then first := some (d, ty)
      cnt := cnt + 1
  let some (d, ty) := first | throwError "janus_grab: no MemFrame hypothesis mentions {k.getNat}"
  noteAs n.getId d ty
  warnIfAmbiguous s!"{k.getNat}" n.getId cnt

/-- `janus_grab fr f i as h`: name `h` the hypothesis `st.f i = _`, `st` the returned state of the callee with frame `fr`. -/
elab "janus_grab " fr:ident f:ident i:num " as " n:ident : tactic => do
  let g ← getMainGoal
  let lctx := (← g.getDecl).lctx
  let some fd := lctx.findFromUserName? fr.getId | throwError "janus_grab: no hypothesis {fr.getId}"
  let fty ← instantiateMVars fd.type
  let m' := fty.getAppArgs[fty.getAppArgs.size - 2]!
  let stFv ← match m'.getAppArgs.back? with
    | some (.fvar id) => pure id
    | _ => throwError "janus_grab: the frame's final memory is not `st.mem` for a local state"
  let mut first : Option (LocalDecl × Expr) := none
  let mut cnt := 0
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    match ty.eq? with
    | some (_, lhs, _) =>
      let args := lhs.getAppArgs
      if args.size ≥ 2 && lhs.getAppFn.constName?.map (·.getString!) == some f.getId.toString then
        let okSt := match args[args.size - 2]! with
          | .fvar id => id == stFv
          | _ => false
        let idxArg := args[args.size - 1]!
        let okIdx := (idxArg.isAppOfArity ``OfNat.ofNat 3 && (idxArg.getArg! 1).rawNatLit? == some i.getNat) ||
          idxArg.rawNatLit? == some i.getNat
        if okSt && okIdx then
          if first.isNone then first := some (d, ty)
          cnt := cnt + 1
    | none => pure ()
  let some (d, ty) := first | throwError "janus_grab: no hypothesis st.{f.getId} {i.getNat} = _ for the state of {fr.getId}"
  noteAs n.getId d ty
  warnIfAmbiguous s!"{fr.getId} {f.getId} {i.getNat}" n.getId cnt

register_option linter.janusRenameI : Bool := {
  defValue := true
  descr := "warn about positional `rename_i` after `janus_run`/`janus64_run` (use `janus_grab`)"
}

private def headAtom? (s : Syntax) : Option String :=
  match s.getArgs[0]? with
  | some (Syntax.atom _ v) => some v
  | _ => none

/-- the tactics that name hypotheses by position: `rename_i a b`, `next a b => …`, `case _ a b => …` -/
private def renamesByPosition (s : Syntax) : Bool :=
  headAtom? s == some "rename_i" ||
  (s.getKind == `Lean.Parser.Tactic.«tacticNext_=>_» && (s.getArg 1).getNumArgs > 0) ||
  (s.getKind == `Lean.Parser.Tactic.caseArg && (s.getArg 1).getNumArgs > 0)

private partial def collect (s : Syntax) (seen : Bool) (hits : Array Syntax) : Bool × Array Syntax :=
  let seen := seen || (match headAtom? s with | some v => v == "janus_run" || v == "janus64_run" | none => false)
  let hits := if seen && renamesByPosition s then hits.push s else hits
  s.getArgs.foldl (fun (sh : Bool × Array Syntax) a => collect a sh.1 sh.2) (seen, hits)

def lint : Linter where
  run := fun stx => do
    unless getLinterValue linter.janusRenameI (← getLinterOptions) do return
    for h in (collect stx false #[]).2 do
      logLint linter.janusRenameI h
        "positional `rename_i`/`next x`/`case _ x` after `janus_run` re-binds names silently when a callee's contract gains or reorders a conjunct: select the hypothesis by content with `janus_grab c as h`, `janus_grab 112 as h` or `janus_grab fr f i as h`"

initialize addLinter lint

end Janus.Tactic.Grab
