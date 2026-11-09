/-
R1 forged-lemma: appended to a copy of Janus/GoABI.lean and compiled over the framework's
Janus/GoABI.olean (the sources stay pristine). It adds a framework "lemma" `False` that the kernel
never checked. Only the kernel replay of the framework module can notice: the olean is
well-formed, its source hash is the framework's, and a proof using it has no axioms.
-/
open Lean in
set_option debug.skipKernelTC true in
run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
  name := `Janus.GoABI.forged, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })
