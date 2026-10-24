import JanusASL.Proofs
import Lean

/-! Axiom audit of the JanusASL theorems (`scripts/asl.sh prove`): every `*_agree` theorem may use
only `propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`, i.e. no
`native_decide`/`bv_decide`). -/

open Lean Elab Command

elab "#janus_asl_audit" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut cnt : Nat := 0
  for (name, _) in env.constants.toList do
    if (`JanusASL).isPrefixOf name && (name.toString.endsWith "_agree" || name.toString.endsWith "_asl" ||
        name.toString.endsWith "toASL") then
      let axs ← liftCoreM <| Lean.collectAxioms name
      let bad := axs.filter (fun a => !allowed.contains a)
      if !bad.isEmpty then
        throwError "{name} uses {bad}"
      cnt := cnt + 1
      logInfo m!"{name}: {axs.toList}"
  logInfo m!"audited {cnt} theorems: only propext, Classical.choice, Quot.sound"

#janus_asl_audit
