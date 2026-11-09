import Janus.Tools.Audit
import Janus.Contracts.ICallAmd64
import Janus.Contracts.Live
import Janus.Contracts.LiveToy

/-!
# (standalone: `Extracted.program` of the amd64 type cannot share an environment with the arm64 test; run `audit/icall/run-preserves64.sh`)
# The auditor's rule for the `preserves` argument of an abstract-callee contract (U-ICALL-PRESERVES, amd64)

`preserves` may be exactly `fun _ _ => True` (the default) or `RtPreserves64 R2` for a VARIABLE `R2 : RtInv` of the statement. Everything
else is a post smuggled into the hypothesis: a lambda that constrains bytes, values or registers, `False`, a closed
runtime model, an eta-expanded `RtPreserves64`. And the same assumption stated as a SEPARATE premise of the theorem is
rejected (the contract itself must carry it).
-/

open Lean Meta Elab

namespace Extracted
def program : Janus.Amd64.Program := { segments := [], stubs := [], exitAddr := 0, contracts := [] }
end Extracted

namespace ICallPreservesAudit64

def stmt (pres extra : String) : String :=
  "∀ (impl : List Janus.Amd64.Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Janus.Contracts.ICall.Res) (R2 : Janus.Contracts.RtInv)" ++
  " (st : Janus.Amd64.State) (m : Janus.Arm64.Memory), " ++ extra ++
  "Janus.Contracts.ICall.ICallContract64 (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R (fun _ => True) " ++ pres ++ " → True"

def audit (src : String) : TermElabM (Option String) := do
  let stx ← match Parser.runParserCategory (← getEnv) `term src with
    | .ok s => pure s
    | .error e => throwError e
  let ty ← Term.elabType stx
  Term.synthesizeSyntheticMVarsNoPostponing
  JanusAudit.checkContractHyps (← instantiateMVars ty)

def accepts (pres : String) (extra : String := "") : TermElabM Unit := do
  if let some msg ← audit (stmt pres extra) then throwError "`{pres}` was rejected: {msg}"

def rejects (pres : String) (extra : String := "") : TermElabM Unit := do
  if (← audit (stmt pres extra)).isNone then throwError "`{pres}` {extra} was accepted"

-- accepted: the default, an explicit `fun _ _ => True`, the recognised form for a variable runtime model
run_elab accepts ""
run_elab accepts "(fun _ _ => True)"
run_elab accepts "(Janus.Contracts.ICall.RtPreserves64 R2)"
-- rejected: a post smuggled into `preserves`
run_elab rejects "(fun _ _ => False)"
run_elab rejects "(fun _ m => m.readLE 0x1000 8 = 7)"
run_elab rejects "(fun s _ => s.regs 0 = s.regs 1)"
run_elab rejects "(fun s m => Janus.Contracts.ICall.RtPreserves64 R2 s m)"
run_elab rejects "(Janus.Contracts.ICall.RtPreserves64 (Janus.Contracts.Toy.toyR [] (fun _ _ => True)))"
run_elab rejects "(fun s m => Janus.Contracts.ICall.RtPreserves64 R2 s m ∧ m.readLE 0 1 = 0)"
-- a separate premise of the same shape is rejected: the contract itself must carry the assumption
run_elab rejects "(Janus.Contracts.ICall.RtPreserves64 R2)" "(hp : ∀ s m, Janus.Contracts.ICall.RtPreserves64 R2 s m) → "

-- U-ICALL-STACK (amd64): the shape of the Format statement (a stack VARIABLE with only a numeral lower bound, nargs 1..5, frame 80,
-- `RtPreserves64 R2`), and the rejected spellings of the sizes
def sstmt (nargs stack above extra : String) : String :=
  "∀ (impl : List Janus.Amd64.Segment) (fn k : Nat) (rt : List (Nat × Nat)) (R : Janus.Contracts.ICall.Res) (R2 : Janus.Contracts.RtInv), " ++ extra ++
  "Janus.Contracts.ICall.ICallContract64 (Extracted.program.link impl) fn (" ++ nargs ++ ") (" ++ stack ++ ") (" ++ above ++
  ") rt (fun _ => []) R (fun _ => True) (Janus.Contracts.ICall.RtPreserves64 R2) → True"
def saccepts (n s a : String) (extra : String := "") : TermElabM Unit := do
  if let some m ← audit (sstmt n s a extra) then throwError "sizes ({n}, {s}, {a}) {extra} rejected: {m}"
def srejects (n s a : String) (extra : String := "") : TermElabM Unit := do
  if (← audit (sstmt n s a extra)).isNone then throwError "sizes ({n}, {s}, {a}) {extra} accepted"
run_elab saccepts "1" "k" "80" "(h : 4568 ≤ k) → "
run_elab saccepts "5" "k" "80" "(h : 4568 ≤ k) → "
run_elab saccepts "4" "k" "80" "(h : 4568 ≤ k) → "
run_elab srejects "5" "k" "47" "(h : 4568 ≤ k) → "
run_elab srejects "4" "2 ^ 48" "80"
run_elab srejects "4" "0" "80"
run_elab srejects "4" "k" "80" "(h : k = 2 ^ 48) → "

end ICallPreservesAudit64
