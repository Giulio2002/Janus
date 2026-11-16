import Janus
import Janus.Tools.Audit

/-!
# `JanusAudit.aslCorollary` refuses non-`Ensures` and foreign-program theorems (ASL forgery X2, X6)

`janus verify --asl` derives the ASL corollary of an `Ensures` theorem about the constant `Extracted.program` with
`JanusAudit.aslCorollary`. The Go test `TestASLForgeryRejected/X2_own_toASL` (test/redteam/asl/attacks) forges a theorem
about proof-local definitions (`aslRun Extracted.program fuel s = true`); since v0.3 such a theorem has a fact-only conclusion,
no non-vacuity witness can exist for it, and it is rejected at the non-vacuity stage before its ASL corollary is ever shown.
This test keeps the ASL-stage check itself covered: the forged shape is refused by `aslCorollary`, with the "is not
`Janus.GoABI.Ensures`" diagnostic, as is an `Ensures` statement about a program variable (X6's shape).
-/

open Lean Meta Elab

namespace JanusTests.AslCorollaryReject

/-- Add `n : src` as an axiom and require `aslCorollary n` to throw a message containing `want`. -/
def refuses (n : Name) (src : String) (want : String) : TermElabM Unit := do
  let stx ← match Parser.runParserCategory (← getEnv) `term src with
    | .ok s => pure s
    | .error e => throwError e
  let ty ← Term.elabType stx
  Term.synthesizeSyntheticMVarsNoPostponing
  addDecl (.axiomDecl { name := n, levelParams := [], type := ← instantiateMVars ty, isUnsafe := false })
  try
    let _ ← liftM (m := MetaM) (JanusAudit.aslCorollary n `JanusASLWords.covered)
    throwError "{n}: aslCorollary accepted a forged theorem"
  catch e =>
    let m ← e.toMessageData.toString
    unless (m.splitOn want).length > 1 do throwError "{n}: refused for another reason: {m}"

-- X2's shape: a fact about proof-local definitions, not an `Ensures`.
run_elab refuses `x2_fact "∀ (fuel s : Nat), (fun (_p : Nat) (_f _s : Nat) => true) 0 fuel s = true" "is not `Janus.GoABI.Ensures"

-- X6's shape: an `Ensures` about a program variable, not `Extracted.program`.
run_elab refuses `x6_var "∀ (p : Janus.Program), Janus.GoABI.Ensures p 0 [] (fun _ => True) (fun _ _ => True)" "not about Extracted.program itself"

end JanusTests.AslCorollaryReject
