import Lean

/-!
# Warning: `‹T›` / `assumption` after `janus_run`

`assumption` and `‹T›` unify the wanted type with every hypothesis at default transparency; after a
`janus_run` the context is full of giant hypotheses, and a failed or late match costs seconds to minutes
(the same shape recurred in Bytes and Exp). This linter only reports: it never changes how a proof
elaborates. Disable with `set_option linter.janusAssumption false`. Use `janus_assumption` (or
`janus_assumption_reducible` in a `first`) instead.
-/

namespace Janus.Tactic.AssumptionLint

open Lean Elab Linter

register_option linter.janusAssumption : Bool := {
  defValue := true
  descr := "warn about `‹T›` and `assumption` after `janus_run`/`janus64_run` (use `janus_assumption`)"
}

private def headAtom? (s : Syntax) : Option String :=
  match s.getArgs[0]? with
  | some (Syntax.atom _ v) => some v
  | _ => none

/-- Walk the syntax in source order; after the first `janus_run`/`janus64_run`, collect the `‹…›` and
`assumption` nodes. -/
private partial def collect (s : Syntax) (seen : Bool) (hits : Array Syntax) : Bool × Array Syntax :=
  let seen := seen || (match headAtom? s with | some v => v == "janus_run" || v == "janus64_run" | none => false)
  let hits := if seen && (match headAtom? s with | some v => v == "‹" || v == "assumption" | none => false)
    then hits.push s else hits
  s.getArgs.foldl (fun (sh : Bool × Array Syntax) a => collect a sh.1 sh.2) (seen, hits)

def lint : Linter where
  run := fun stx => do
    unless getLinterValue linter.janusAssumption (← getLinterOptions) do return
    for h in (collect stx false #[]).2 do
      logLint linter.janusAssumption h
        "`‹T›`/`assumption` after `janus_run` tries every hypothesis at default transparency and can cost minutes in the large context of a run: use `by janus_assumption` (or `janus_assumption_reducible` in a `first`)"

initialize addLinter lint

end Janus.Tactic.AssumptionLint
