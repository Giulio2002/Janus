import Janus.Tools.Audit
import Janus.Contracts.ICall
import Janus.Contracts.Live
import Janus.Contracts.LiveToy

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


/-! ### U-ICALL-PRESERVES: the `preserves` argument

`preserves` is exactly `fun _ _ => True` (the default) or `RtPreserves R2` for a variable `R2 : RtInv`; anything else is a post
smuggled into the hypothesis, and the same assumption as a SEPARATE premise is rejected. -/

def pstmt (pres extra : String) : String :=
  "∀ (impl : List Janus.Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Janus.Contracts.ICall.Res) (R2 : Janus.Contracts.RtInv)" ++
  " (st : Janus.Arm64.State) (m : Janus.Arm64.Memory), " ++ extra ++
  "Janus.Contracts.ICall.ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R (fun _ => True) " ++ pres ++ " → True"

def paccepts (pres : String) (extra : String := "") : TermElabM Unit := do
  if let some msg ← audit (pstmt pres extra) then throwError "`{pres}` was rejected: {msg}"

def prejects (pres : String) (extra : String := "") : TermElabM Unit := do
  if (← audit (pstmt pres extra)).isNone then throwError "`{pres}` {extra} was accepted"

-- accepted: the default, an explicit `fun _ _ => True`, the recognised form for a variable runtime model
run_elab paccepts ""
run_elab paccepts "(fun _ _ => True)"
run_elab paccepts "(Janus.Contracts.ICall.RtPreserves R2)"
-- rejected: a post smuggled into `preserves`
run_elab prejects "(fun _ _ => False)"
run_elab prejects "(fun _ m => m.readLE 0x1000 8 = 7)"
run_elab prejects "(fun s _ => s.regs 0 = s.regs 1)"
run_elab prejects "(fun s m => Janus.Contracts.ICall.RtPreserves R2 s m)"
run_elab prejects "(Janus.Contracts.ICall.RtPreserves (Janus.Contracts.Toy.toyR [] (fun _ _ => True)))"
run_elab prejects "(fun s m => Janus.Contracts.ICall.RtPreserves R2 s m ∧ m.readLE 0 1 = 0)"
-- a separate premise of the same shape is rejected: the contract itself must carry the assumption
run_elab prejects "(Janus.Contracts.ICall.RtPreserves R2)" "(hp : ∀ s m, Janus.Contracts.ICall.RtPreserves R2 s m) → "


/-! ### U-ICALL-STACK: the size arguments of an abstract-callee contract (red team B12, B18, B19)

`nargs`, the stack size and the caller-frame size are EITHER a closed term that evaluates to a natural number below 2^47
(nargs: 2^44), whatever its spelling (`2 ^ 48`, `2 ^ 47 * 2`, `Nat.pow 2 48`, a `let`, a def-wrapped constant), OR a variable that no
premise constrains except a numeral lower bound. -/

def bigStack : Nat := 2 ^ 48
def smallStack : Nat := 4096

def sstmt (nargs stack above extra : String) : String :=
  "∀ (impl : List Janus.Segment) (fn k : Nat) (rt : List (Nat × Nat)) (R : Janus.Contracts.ICall.Res), " ++ extra ++
  "Janus.Contracts.ICall.ICallContract (Extracted.program.link impl) fn (" ++ nargs ++ ") (" ++ stack ++ ") (" ++ above ++ ")" ++
  " rt (fun _ => []) R (fun _ => True) → True"

def saccepts (nargs stack above : String) (extra : String := "") : TermElabM Unit := do
  if let some m ← audit (sstmt nargs stack above extra) then throwError "sizes ({nargs}, {stack}, {above}) {extra} rejected: {m}"

def srejects (nargs stack above : String) (extra : String := "") : TermElabM Unit := do
  if (← audit (sstmt nargs stack above extra)).isNone then throwError "sizes ({nargs}, {stack}, {above}) {extra} accepted"

-- accepted
run_elab saccepts "4" "16" "48"
run_elab saccepts "4" "2 ^ 20" "48"
run_elab saccepts "4" "JanusTests.ICallAudit.smallStack" "48"
run_elab saccepts "4" "k" "48"
run_elab saccepts "4" "k" "48" "(hk : 4104 ≤ k) → "
run_elab saccepts "4" "k" "48" "(hk : 4104 < k) → "
-- rejected: the numeral, as an expression, a `Nat.pow`, a product, a `let`, a def-wrapped constant
run_elab srejects "4" "281474976710656" "48"
run_elab srejects "4" "2 ^ 48" "48"
run_elab srejects "4" "2 ^ 47 * 2" "48"
run_elab srejects "4" "Nat.pow 2 48" "48"
run_elab srejects "4" "(let s := 2 ^ 48; s)" "48"
run_elab srejects "4" "JanusTests.ICallAudit.bigStack" "48"
run_elab srejects "4" "2 ^ 47" "48"
-- the frame size and the argument count are covered too
run_elab srejects "4" "16" "2 ^ 48"
run_elab srejects "4" "16" "JanusTests.ICallAudit.bigStack"
run_elab srejects "2 ^ 45" "16" "48"
-- rejected: a variable pinned (B19), bounded above, bounded below by a huge numeral, or tied to another term
run_elab srejects "4" "k" "48" "(hk : k = 281474976710656) → "
run_elab srejects "4" "k" "48" "(hk : k = 2 ^ 48) → "
run_elab srejects "4" "k" "48" "(hk : k ≤ 5) → "
run_elab srejects "4" "k" "48" "(hk : 2 ^ 48 ≤ k) → "
run_elab srejects "4" "k" "48" "(hk : k = JanusTests.ICallAudit.bigStack) → "
run_elab srejects "4" "k" "48" "(j : Nat) → (hj : j = 2 ^ 48) → (hk : k = j) → "
-- the whole satisfiable range, not only the upper bound (red team V09-V14): stack >= 8, nargs <= 64, above >= 8 + 8 nargs
run_elab srejects "4" "0" "48"
run_elab srejects "4" "7" "48"
run_elab saccepts "4" "8" "48"
run_elab srejects "4" "16" "39"
run_elab saccepts "4" "16" "40"
run_elab saccepts "64" "16" "520"
run_elab srejects "64" "16" "519"
run_elab srejects "65" "16" "600"
run_elab srejects "4" "16" "k" "(hk : k < 8) → "
run_elab srejects "n" "16" "48" "(n : Nat) → (hn : n ≥ 2 ^ 46) → "
run_elab saccepts "4" "16" "k" "(hk : 40 ≤ k) → "

-- other contract families (red team F01-F11): the same rule for the `stack` argument of RtContract, RtLiveContract, NewobjectContract, …
def fstmt (stack extra : String) : String :=
  "∀ (impl : List Janus.Segment) (k : Nat) (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady), " ++ extra ++
  "Janus.Contracts.NewobjectContract (Extracted.program.link impl) (Extracted.program.contractAddr \"runtime.newobject\") rt (" ++ stack ++ ") H → True"

def faccepts (stack : String) (extra : String := "") : TermElabM Unit := do
  if let some m ← audit (fstmt stack extra) then throwError "NewobjectContract stack {stack} {extra} rejected: {m}"

def frejects (stack : String) (extra : String := "") : TermElabM Unit := do
  if (← audit (fstmt stack extra)).isNone then throwError "NewobjectContract stack {stack} {extra} accepted"

run_elab faccepts "4096"
run_elab faccepts "k"
run_elab frejects "0"
run_elab frejects "2 ^ 48"
run_elab frejects "k" "(hk : k ≥ 2 ^ 48) → "
run_elab frejects "k" "(hk : k = 0) → "

-- rejected: an expression that is neither a closed numeral nor a variable
run_elab srejects "4" "(k + 1)" "48"
run_elab srejects "4" "(fn + 1)" "48"

-- the `RtLiveContract` / `NewobjectLiveContract` / `MemmoveLive` shapes of the Scan and UnmarshalText statements (literal 4096; the
-- memmove family's `d`)
def lstmt (body : String) : String :=
  "∀ (impl : List Janus.Segment) (R : Janus.Contracts.RtInv) (k : Nat), " ++ body ++ " → True"
def laccepts (b : String) : TermElabM Unit := do
  if let some m ← audit (lstmt b) then throwError "{b} rejected: {m}"
def lrejects (b : String) : TermElabM Unit := do
  if (← audit (lstmt b)).isNone then throwError "{b} accepted"
run_elab laccepts "Janus.Contracts.NewobjectLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr \"runtime.newobject\") 4096 R"
run_elab laccepts "Janus.Contracts.MemmoveLive (Extracted.program.link impl) (Extracted.program.contractAddr \"runtime.memmove\") 4096 R"
run_elab laccepts "Janus.Contracts.MemmoveLive (Extracted.program.link impl) (Extracted.program.contractAddr \"runtime.memmove\") k R"
run_elab lrejects "Janus.Contracts.NewobjectLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr \"runtime.newobject\") 0 R"
run_elab lrejects "Janus.Contracts.MemmoveLive (Extracted.program.link impl) (Extracted.program.contractAddr \"runtime.memmove\") (2 ^ 48) R"

end JanusTests.ICallAudit
