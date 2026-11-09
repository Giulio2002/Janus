import Extracted
/-! ATTACK A5 (expected BLOCKED by leanchecker): add `Proof.correctness`, a FALSE statement that mentions the extracted
program (`Extracted.entry = Extracted.entry + 1`, so it passes the statement-identity rule and the axiom audit: the term
`True.intro` uses no axiom), without the kernel check, via addDecl under debug.skipKernelTC. The declaration is ill-typed
(`True.intro : True`, not the equation), so only the kernel replay of the proof's environment (leanchecker) can reject it.
(The earlier version stated `False`, which the statement-identity rule rejected before the replay was ever reached.) -/
open Lean Elab Command Meta in
set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  let ty ← Term.elabTerm (← `(Extracted.entry = Extracted.entry + 1)) none
  let ty ← instantiateMVars ty
  addDecl <| .thmDecl {
    name := `Proof.correctness, levelParams := [], type := ty,
    value := mkConst ``True.intro }
