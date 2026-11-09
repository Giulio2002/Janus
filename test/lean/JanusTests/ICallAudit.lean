import Janus.Tools.Audit
import Janus.Contracts.ICall
import Janus.Contracts.Live
import Janus.Contracts.LiveToy
import Janus.Contracts.ICallSat

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
-- a callee bound below a caller bound that only bounds from below (the `d' + F ≤ d` of the memhash/memequal/memmove families:
-- `d` is chosen after `d'`): accepted. A `w` that anything pins from above, or that is itself a size, is not.
run_elab saccepts "4" "k" "48" "(w : Nat) → (hw : k + 48 ≤ w) → "
run_elab saccepts "4" "k" "48" "(w : Nat) → (hk : 8 ≤ k) → (hw : k + 48 ≤ w) → "
run_elab saccepts "4" "k" "48" "(w : Nat) → (hw : k ≤ w) → "
run_elab saccepts "4" "k" "48" "(w : Nat) → (hw : k < w) → "
run_elab saccepts "4" "k" "48" "(w : Nat) → (hw : k + 48 ≤ w) → (hw2 : 4096 ≤ w) → "
run_elab srejects "4" "k" "48" "(w : Nat) → (hw : k + 48 ≤ w) → (hp : w ≤ 5) → "
run_elab srejects "4" "k" "48" "(w : Nat) → (hw : k + 48 ≤ w) → (hp : w = 2 ^ 47) → "
run_elab srejects "4" "k" "48" "(w : Nat) → (hw : k + 48 ≤ w) → (hp : w ≤ 2 ^ 20) → "
run_elab srejects "4" "k" "48" "(w : Nat) → (j : Nat) → (hw : k + 48 ≤ w) → (hp : w + 1 ≤ j) → (hj : j ≤ 5) → "
run_elab srejects "4" "k" "48" "(w : Nat) → (hw : k + 48 ≤ w) → (hp : w + k ≤ 100) → "
run_elab srejects "4" "k" "48" "(w : Nat) → (hw : w ≤ k) → "
run_elab srejects "4" "k" "48" "(w : Nat) → (hw : k + k ≤ w) → "
run_elab srejects "4" "k" "48" "(w : Nat) → (hw : k + 281474976710656 ≤ w) → "
run_elab srejects "4" "k" "48" "(w : Nat) → (hw : k + 48 = w) → "
run_elab srejects "4" "k" "48" "(w : Nat) → (hw : k + 48 ≤ w) → (hp : w = fn) → "
run_elab srejects "4" "k" "w" "(w : Nat) → (hw : k + 48 ≤ w) → "
run_elab srejects "w" "k" "48" "(w : Nat) → (hw : k + 48 ≤ w) → "
run_elab srejects "4" "w" "48" "(w : Nat) → (hw : w + 48 ≤ w) → "
-- ADVERSARIAL rows for the below-bounded-variable relaxation (all must be REJECTED). Controls: the 15 real examples + saccepts above.
-- chain pin: m pinned, m <= k, stack k
run_elab srejects "4" "k" "48" "(m : Nat) → (hm : m = 2 ^ 48) → (hk : m ≤ k) → "
run_elab srejects "4" "k" "48" "(m : Nat) → (hm : m = 281474976710656) → (hk : m + 1 ≤ k) → "
-- pinned through an alias
run_elab srejects "4" "k" "48" "(m a : Nat) → (ha : a = 2 ^ 48) → (hm : m = a) → (hk : m ≤ k) → "
-- pinned through an existential (premise mentioning the pin is not an `X ≤ w` shape)
run_elab srejects "4" "k" "48" "(m : Nat) → (hm : ∃ z, z = 2 ^ 48 ∧ m = z) → (hk : m ≤ k) → "
run_elab srejects "4" "k" "48" "(m : Nat) → (hk : m ≤ k) → (hm : ∃ z, m ≤ z ∧ z ≤ 5) → "
-- two lower-bounding variables, one of them pinned
run_elab srejects "4" "k" "48" "(m n : Nat) → (hn : n = 2 ^ 48) → (hm : m ≤ k) → (hn2 : n ≤ k) → "
-- pinning by two inequalities
run_elab srejects "4" "k" "48" "(m : Nat) → (h1 : m ≤ k) → (h2 : k ≤ m) → "
run_elab srejects "4" "k" "48" "(h : (2 ^ 48 ≤ k ∧ k ≤ 2 ^ 48)) → "
run_elab srejects "4" "k" "48" "(m : Nat) → (h1 : k + 48 ≤ m) → (h2 : m ≤ k + 48) → "
run_elab srejects "4" "k" "48" "(m : Nat) → (h1 : k + 48 ≤ m) → (h2 : m + 1 ≤ k + 49) → "
-- the bounding variable bounded from above through another variable
run_elab srejects "4" "k" "48" "(m j : Nat) → (h1 : k ≤ m) → (h2 : m ≤ j) → (h3 : j = 5) → "
run_elab srejects "4" "k" "48" "(m j : Nat) → (h1 : k ≤ m) → (h2 : j ≤ m) → (h3 : m ≤ j) → "
-- the bounding variable is a size variable of the same or another contract argument
run_elab srejects "k" "k" "48" "(h : k + 1 ≤ k) → "
-- `above` and `nargs` families
run_elab srejects "4" "16" "k" "(m : Nat) → (hm : m = 2 ^ 48) → (hk : m ≤ k) → "
run_elab srejects "4" "16" "k" "(m : Nat) → (h1 : m ≤ k) → (h2 : k ≤ m) → "
run_elab srejects "n" "16" "48" "(n m : Nat) → (hm : m = 2 ^ 46) → (hn : m ≤ n) → "
run_elab srejects "n" "16" "48" "(n m : Nat) → (h1 : m ≤ n) → (h2 : n ≤ m) → "
-- `d` family (NewobjectContract stack)
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

-- adversarial rows for the below-bounded-variable relaxation, `d` family
run_elab frejects "k" "(m : Nat) → (hm : m = 2 ^ 48) → (hk : m ≤ k) → "
run_elab frejects "k" "(m : Nat) → (h1 : m ≤ k) → (h2 : k ≤ m) → "
run_elab frejects "k" "(m n : Nat) → (hn : n = 2 ^ 48) → (hm : m ≤ k) → (hn2 : n ≤ k) → "
run_elab frejects "k" "(m : Nat) → (hm : ∃ z, z = 2 ^ 48 ∧ m = z) → (hk : m ≤ k) → "

end JanusTests.ICallAudit

namespace JanusTests.ICallAudit

/-! ### UP3 (red team n11): a size occurs nowhere else in a main theorem, and the sizes are jointly satisfiable -/

def ustmt (nargs stack above extra pre : String) : String :=
  "∀ (impl : List Janus.Segment) (fn k n : Nat) (rt : List (Nat × Nat)) (R : Janus.Contracts.ICall.Res), " ++ extra ++
  "Janus.Contracts.ICall.ICallContract (Extracted.program.link impl) fn (" ++ nargs ++ ") (" ++ stack ++ ") (" ++ above ++ ")" ++
  " rt (fun _ => []) R (fun _ => True) → Janus.GoABI.Ensures (Extracted.program.link impl) Extracted.entry [] (fun _ => " ++ pre ++ ") (fun _ _ => True)"

def uaccepts (nargs stack above extra pre : String) : TermElabM Unit := do
  if let some m ← audit (ustmt nargs stack above extra pre) then throwError "({nargs}, {stack}, {above}) {extra} pre {pre} rejected: {m}"

def urejects (nargs stack above extra pre : String) : TermElabM Unit := do
  if (← audit (ustmt nargs stack above extra pre)).isNone then throwError "({nargs}, {stack}, {above}) {extra} pre {pre} accepted"

-- control: a harmless pre; sizes in neither
run_elab uaccepts "4" "k" "48" "(hk : 8 ≤ k) → " "True"
run_elab uaccepts "4" "k" "48" "(w : Nat) → (hw : k + 16 ≤ w) → " "True"
-- N11 / N62: the size pinned in the precondition; N10 / N65: its bounding variable; N18: through a `let`
-- the post is an obligation, not an assumption: a size may be mentioned there (N12)
def ustmtPost (extra post : String) : String :=
  "∀ (impl : List Janus.Segment) (fn k n : Nat) (rt : List (Nat × Nat)) (R : Janus.Contracts.ICall.Res), " ++ extra ++
  "Janus.Contracts.ICall.ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => True) → " ++
  "Janus.GoABI.Ensures (Extracted.program.link impl) Extracted.entry [] (fun _ => True) (fun _ _ => " ++ post ++ ")"
run_elab (do if let some m ← audit (ustmtPost "(w : Nat) → (hw : k + 16 ≤ w) → " "w = w ∧ k = k") then throwError "post mention rejected: {m}")
-- N13 / N60 / N64 / N16 / N17: pins through non-Prop binders, whatever the wrapper
run_elab urejects "4" "k" "48" "(p : PLift (k = 7)) → " "True"
run_elab urejects "4" "k" "48" "(w : Nat) → (hw : k ≤ w) → (p : PLift (w < 8)) → " "True"
run_elab urejects "4" "k" "48" "(w : Nat) → (hw : k ≤ w) → (f : Fin w → Fin 0) → " "True"
run_elab urejects "4" "k" "48" "(w : Nat) → (hw : k + 16 ≤ w) → (p : PProd (w < 8) (k ≤ w)) → " "True"
run_elab urejects "4" "k" "48" "(p : { u : Unit // k = 7 }) → " "True"
run_elab urejects "4" "k" "48" "(p : ULift.{0} (PLift (k = 7))) → " "True"
-- N50 / N51 / N52: jointly unsatisfiable nargs and above
run_elab urejects "n" "16" "n" "" "True"
run_elab urejects "n" "16" "8" "(hn : 1 ≤ n) → " "True"
run_elab urejects "n" "16" "48" "(hn : 63 ≤ n) → " "True"
run_elab uaccepts "n" "16" "a" "(a : Nat) → (hn : 1 ≤ n) → (ha : 520 ≤ a) → " "True"
run_elab uaccepts "n" "16" "a" "(a : Nat) → (hn : 60 ≤ n) → (ha : 480 ≤ a) → " "True"
run_elab uaccepts "n" "16" "a" "(a : Nat) → (hn : 60 ≤ n) → (ha : 488 ≤ a) → " "True"
run_elab uaccepts "n" "s" "a" "(s a : Nat) → (hn : 1 ≤ n) → (ha : 16 ≤ a) → " "True"


/-! ### U-ICALL-INHABITED: an author-chosen call-site property needs a kernel-checked inhabitation lemma -/

/-- the lemma for `P := fun _ => 1 = 1` (a non-stock `P`), found by statement -/
theorem inhab_one_eq_one : ∃ s, Janus.Contracts.ICall.ICallPre 4 16 48 Janus.Contracts.ICallSat.rt0 (fun _ => 1 = 1) s :=
  ⟨Janus.Contracts.ICallSat.wstate, Janus.Contracts.ICallSat.wstate_pre.1, Janus.Contracts.ICallSat.wstate_pre.2.1,
    Janus.Contracts.ICallSat.wstate_pre.2.2.1, rfl⟩

def pstmt2 (P : String) : String :=
  "∀ (impl : List Janus.Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Janus.Contracts.ICall.Res), " ++
  "Janus.Contracts.ICall.ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R (" ++ P ++ ") → True"

-- stock: accepted without a lemma; non-stock with a lemma: accepted; without a lemma, or unsatisfiable: rejected
run_elab (do if let some m ← audit (pstmt2 "fun _ => True") then throwError "stock P rejected: {m}")
run_elab (do if let some m ← audit (pstmt2 "fun _ => 1 = 1") then throwError "P with lemma rejected: {m}")
run_elab (do if (← audit (pstmt2 "fun _ => False")).isNone then throwError "P := False accepted")


theorem inhab_wp : ∃ (stack : Nat) (rt : List (Nat × Nat)) (w : BitVec 64) (s : Janus.Arm64.State),
    Janus.Contracts.ICall.ICallPre 4 stack 48 rt (fun sc => sc.regs 0 = w) s :=
  ⟨16, Janus.Contracts.ICallSat.rt0, 0, { Janus.Contracts.ICallSat.wstate with regs := fun i => if i = 30 then 0x200000#64 else 0#64 },
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, by decide,
    by show Janus.Outside 0x17f8 56 Janus.Contracts.ICallSat.rt0; simp [Janus.Contracts.ICallSat.rt0], rfl⟩

def wstmt : String :=
  "∀ (impl : List Janus.Segment) (fn stack : Nat) (rt : List (Nat × Nat)) (R : Janus.Contracts.ICall.Res) (w : BitVec 64), " ++
  "Janus.Contracts.ICall.ICallContract (Extracted.program.link impl) fn 4 stack 48 rt (fun _ => []) R (fun sc => sc.regs 0 = w) → True"
run_elab (do if let some m ← audit wstmt then throwError "variable-bearing P with lemma rejected: {m}")

end JanusTests.ICallAudit
