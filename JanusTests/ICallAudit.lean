import Janus.Tools.Audit
import Janus.Contracts.ICall

/-!
# The auditor's rule for the callee address of an abstract-callee contract (U-ICALL)

`ICallContract (Extracted.program.link impl) FN …`: `FN` must be a variable of the statement (a dynamic callee) or exactly
`Extracted.program.contractAddr "name"` (a static call to a non-extracted function that the extraction lists as a
`--contract` stub). The address of an extracted function, `Extracted.entry`, a numeral, an offset of a stub address or
the `contractAddr` of another program are rejected: such a hypothesis would be a contract about code the statement
chooses, false for the real code at that address.
-/

open Lean Meta Elab

namespace Extracted
def program : Janus.Program := { segments := [], stubs := [], exitAddr := 0, contracts := [("fmt.Fprint", 0x5000)] }
def entry : Nat := 0x4000
end Extracted

namespace JanusTests.ICallAudit

def stmt (fn : String) : String :=
  "∀ (impl : List Janus.Segment) (fn : Nat) (other : Janus.Program) (rt : List (Nat × Nat)) (R : Janus.Contracts.ICall.Res), " ++
  "Janus.Contracts.ICall.ICallContract (Extracted.program.link impl) (" ++ fn ++ ") 4 16 48 rt (fun _ => []) R (fun _ => True) → True"

def audit (src : String) : TermElabM (Option String) := do
  let stx ← match Parser.runParserCategory (← getEnv) `term src with
    | .ok s => pure s
    | .error e => throwError e
  let ty ← Term.elabType stx
  Term.synthesizeSyntheticMVarsNoPostponing
  JanusAudit.checkContractHyps (← instantiateMVars ty)

def accepts (fn : String) : TermElabM Unit := do
  if let some m ← audit (stmt fn) then throwError "the callee address `{fn}` was rejected: {m}"

def rejects (fn : String) : TermElabM Unit := do
  if (← audit (stmt fn)).isNone then throwError "the callee address `{fn}` was accepted"

-- accepted: a variable (dynamic callee), a stub the extraction lists (static, non-extracted callee)
run_elab accepts "fn"
run_elab accepts "Extracted.program.contractAddr \"fmt.Fprint\""
-- rejected: a numeral, the entry, an extracted function, an offset of a stub address, another program's stub
run_elab rejects "0x1000"
run_elab rejects "Extracted.entry"
run_elab rejects "Janus.Tactic.segAddr Extracted.program \"main.f\""
run_elab rejects "Extracted.program.contractAddr \"fmt.Fprint\" + 4"
run_elab rejects "Janus.Program.contractAddr other \"fmt.Fprint\""
run_elab rejects "Janus.Program.contractAddr Extracted.program (\"fmt.\" ++ \"Fprint\")"

end JanusTests.ICallAudit
