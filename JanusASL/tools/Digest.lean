import JanusASL.Proofs
import Lean

/-! Digest of every declaration of the generated model (`ArmASL.*` modules) and of the proofs
(`JanusASL.*` modules), for checking that re-splitting modules changed nothing (docs/ASL.md,
"Memory"):

    lake env lean tools/Digest.lean > digest.txt

One line per declaration, sorted by name: kind, name, and the structural hashes of its type and
(for definitions and theorems) its value. Module names are not printed (re-splitting moves
declarations between modules by design). References to auxiliary lemmas (`_auxLemma.N`, which
Lean numbers per module) are hashed by the lemma's type instead of its name, and their own lines
are left out. -/

open Lean

def isAux (n : Name) : Bool :=
  n.components.any fun c => c.toString == "_auxLemma"

def keep (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    (`ArmASL).isPrefixOf m || (`JanusASL).isPrefixOf m
  | none => false

partial def digest (env : Environment) (e : Expr) : UInt64 :=
  if (e.find? fun x => x.isConst && isAux x.constName!).isNone then e.hash
  else
    (e.replace fun x =>
      if x.isConst && isAux x.constName! then
        match env.find? x.constName! with
        | some ci => some (.lit (.natVal (digest env ci.type).toNat))
        | none => some (.lit (.strVal "missing"))
      else none).hash

open Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if keep env n && !isAux n then
      let kind := match ci with
        | .thmInfo _ => "thm" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
        | .recInfo _ => "rec" | .quotInfo _ => "quot"
      let v := match ci.value? (allowOpaque := true) with
        | some v => toString (digest env v)
        | none => "-"
      rows := rows.push s!"{kind} {n} {digest env ci.type} {v}"
  for r in rows.qsort (· < ·) do
    IO.println r
