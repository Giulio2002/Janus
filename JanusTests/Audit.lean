import Janus.Tools.Audit

/-!
# Tests for the auditor's statement-faithfulness checks (round 2, CRITICAL-1)

`JanusAudit.checkInstArgs` (structural: instance-implicit arguments must be registered
instances or local instance binders) and `JanusAudit.printFaithful`/`roundTrip` (semantic: the printed statement
must re-elaborate to a definitionally equal type) are each tested on their own, so either one
alone rejects the inline-instance statements, and both accept honest statements.
-/

open Lean Meta Elab

namespace JanusTests.Audit

/-- Parse and elaborate `src` as a closed proposition, add it as an axiom `n`, and run both checks the
way `cleanEnvAndPrint` does (with `JanusAudit.printOptions`). Returns
`(instance-argument check result, round-trip result)`; `none` means accepted. -/
def checks (n : Name) (src : String) : TermElabM (Option String × Option String) := do
  let stx ← match Parser.runParserCategory (← getEnv) `term src with
    | .ok s => pure s
    | .error e => throwError e
  let ty ← Term.elabType stx
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  addDecl (.axiomDecl { name := n, levelParams := [], type := ty, isUnsafe := false })
  let cx := JanusAudit.mkCtx (← getEnv) #[]
  let inst ← JanusAudit.checkInstArgs cx ty
  withOptions (fun _ => JanusAudit.printOptions) do
    let rt ← JanusAudit.printFaithful n ty
    return (inst, match rt with | .ok _ => none | .error m => some m)

/-- Both checks must reject. -/
def rejects (n : Name) (stx : String) : TermElabM Unit := do
  let (inst, rt) ← checks n stx
  if inst.isNone then throwError "{n}: the instance-argument check accepted an inline instance"
  if rt.isNone then throwError "{n}: the round-trip check accepted a misleading statement"

/-- Both checks must accept. -/
def accepts (n : Name) (stx : String) : TermElabM Unit := do
  let (inst, rt) ← checks n stx
  if let some m := inst then throwError "{n}: the instance-argument check rejected: {m}"
  if let some m := rt then throwError "{n}: the round-trip check rejected: {m}"

-- Inline instances: HMul/HSub literals (printed `x * y` / `x - y`, meaning `x + y`), an OfNat
-- literal instance, a Decidable `dite` in an `if`, an LT meaning `≤`, an inline NatCast
-- coercion, a Coe literal, and a literal behind a beta-redex.
run_elab rejects `t_hmul "∀ x y : BitVec 64, x + y = @HMul.hMul (BitVec 64) (BitVec 64) (BitVec 64) ⟨fun a b => a + b⟩ x y"
run_elab rejects `t_hsub "∀ x y : BitVec 64, x + y = @HSub.hSub (BitVec 64) (BitVec 64) (BitVec 64) ⟨fun a b => a + b⟩ x y"
run_elab rejects `t_ofnat "∀ x y : BitVec 64, x + y = @OfNat.ofNat (BitVec 64) 0 ⟨x + y⟩"
run_elab rejects `t_dite "∀ x y : BitVec 64, x + y = @ite (BitVec 64) (x = y) (if h : x = y then .isTrue h else .isFalse h) (x + y) (x + y)"
run_elab rejects `t_lt "@LT.lt Nat ⟨fun a b => a ≤ b⟩ 0 0"
run_elab rejects `t_natcast "∀ x y : BitVec 64, x + y = @NatCast.natCast (BitVec 64) ⟨fun n => BitVec.ofNat 64 (n + y.toNat)⟩ x.toNat"
run_elab rejects `t_coe "∀ x y : BitVec 64, x + y = @Coe.coe (BitVec 64) (BitVec 64) ⟨fun a => a + y⟩ x"
run_elab rejects `t_beta "∀ x y : BitVec 64, x + y = @HMul.hMul (BitVec 64) (BitVec 64) (BitVec 64) ((fun (_ : Unit) => (⟨fun a b => a + b⟩ : HMul (BitVec 64) (BitVec 64) (BitVec 64))) ()) x y"

-- Honest statements, including canonical instances, numerals, `if`, `<`, coercions and a
-- local instance binder.
run_elab accepts `t_ok1 "∀ x y : BitVec 64, (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 64"
run_elab accepts `t_ok2 "∀ x y : BitVec 64, x * y = y * x ∧ (if x = y then x else y) = y ∨ x < y"
run_elab accepts `t_ok3 "∀ (x : BitVec 64) (n : Nat), (x.toNat : Int) + n ≥ 0 ∧ (5 : BitVec 64) ≠ 7"
run_elab accepts `t_ok4 "∀ (α : Type) [inst : Add α] (a b : α), a + b = @HAdd.hAdd α α α (@instHAdd α inst) a b"
run_elab accepts `t_ok5 "∀ (xs : List Nat) (i : Nat) (h : i < xs.length), xs[i] ∈ xs ∧ decide (xs = []) = false → True"

end JanusTests.Audit
