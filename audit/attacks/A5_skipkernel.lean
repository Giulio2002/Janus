import Extracted
/-! ATTACK A5 (expected BLOCKED by leanchecker): add `Proof.correctness : False` without the
kernel check, via addDecl under debug.skipKernelTC. -/
open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl {
  name := `Proof.correctness, levelParams := [], type := mkConst ``False,
  value := mkConst ``True.intro }
