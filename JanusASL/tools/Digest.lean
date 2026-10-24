import JanusASL.Proofs
import Lean

/-! Digest of every declaration of the generated model (`ArmASL.*` modules) and of the proofs
(`JanusASL.*` modules), for checking that re-splitting modules changed nothing (docs/ASL.md,
"Memory"):

    lake env lean tools/Digest.lean > digest.txt

One line per declaration, sorted by name: kind, name, and the structural hashes of its type and
(for definitions and theorems) its value. Module names are not printed (re-splitting moves
declarations between modules by design). References to auxiliary declarations (`isAux`) are
hashed by their content instead of their name, and their own lines are left out. -/

open Lean

/-- Auxiliary declarations that Lean names per module or shares between declarations of one
module: matchers (`match_N`, `_sparseCasesOn_N`, `splitter`), equation lemmas (`eq_N`, `eq_def`,
`else_eq`, made on first use, in whichever module first uses them), `_proof_N` and `_auxLemma.N`. -/
def isAux (n : Name) : Bool :=
  n.components.any (fun c => c.toString == "_auxLemma") ||
  match n with
  | .str _ s => ["match_", "_sparseCasesOn_", "eq_", "proof_", "_proof_"].any (s.startsWith ·) ||
      s == "splitter" || s == "else_eq"
  | _ => false

def keep (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    (`ArmASL).isPrefixOf m || (`JanusASL).isPrefixOf m
  | none => false

/-- Structural hash of `e`, with every auxiliary constant replaced by the hash of its own
content (type and value), so that renaming or re-sharing auxiliaries changes nothing. -/
partial def digest (env : Environment) (e : Expr) : StateM (Std.HashMap Name UInt64) UInt64 := do
  let auxs := e.getUsedConstants.filter isAux
  if auxs.isEmpty then return e.hash
  let mut m : Std.HashMap Name UInt64 := {}
  for n in auxs do
    m := m.insert n (← auxDigest env n)
  return (e.replace fun x =>
    if x.isConst then (m.get? x.constName!).map (fun h => .lit (.natVal h.toNat)) else none).hash
where
  auxDigest (env : Environment) (n : Name) : StateM (Std.HashMap Name UInt64) UInt64 := do
    if let some h := (← get)[n]? then return h
    modify (·.insert n 0)  -- (no auxiliary refers to itself; guards against a loop)
    let h ← match env.find? n with
      | some ci => do
        let t ← digest env ci.type
        let v ← match ci.value? (allowOpaque := true) with
          | some v => digest env v
          | none => pure 0
        pure (mixHash t v)
      | none => pure 7
    modify (·.insert n h)
    return h

open Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  let mut memo : Std.HashMap Name UInt64 := {}
  for (n, ci) in env.constants.map₁.toList do
    if keep env n && !isAux n then
      let kind := match ci with
        | .thmInfo _ => "thm" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
        | .recInfo _ => "rec" | .quotInfo _ => "quot"
      let (t, memo') := (digest env ci.type).run memo
      memo := memo'
      let (v, memo') := (match ci.value? (allowOpaque := true) with
        | some v => do return toString (← digest env v)
        | none => pure "-").run memo
      memo := memo'
      rows := rows.push s!"{kind} {n} {t} {v}"
  for r in rows.qsort (· < ·) do
    IO.println r
