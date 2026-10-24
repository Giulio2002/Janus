import JanusASL.Proofs
import JanusASL.Verify
import Lean

/-! Audit of the JanusASL theorems (`scripts/asl.sh prove`).

* The audited theorems are an explicit list. Each must exist and be a theorem; a declaration under
  `JanusASL` named `*_agree`, `*_asl` or `*toASL` that is not on the list fails the audit, so a
  renamed, removed or added headline theorem cannot go unnoticed.
* Each may use only `propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`, no
  `Lean.ofReduceBool`, i.e. no `native_decide`/`bv_decide`).
* Each statement is printed, for a diff against a recorded golden copy. -/

open Lean Elab Command

def janusAslAudited : List Name := [
    `JanusASL.Proofs.addSubCarry_agree,
    `JanusASL.Proofs.addSubExt_agree,
    `JanusASL.Proofs.addSubImm_agree,
    `JanusASL.Proofs.addSubShifted_agree,
    `JanusASL.Proofs.b_agree,
    `JanusASL.Proofs.bcond_agree,
    `JanusASL.Proofs.bitfield_agree,
    `JanusASL.Proofs.blr_agree,
    `JanusASL.Proofs.br_agree,
    `JanusASL.Proofs.cb_agree,
    `JanusASL.Proofs.cls_agree,
    `JanusASL.Proofs.clz_agree,
    `JanusASL.Proofs.condCmpImm_agree,
    `JanusASL.Proofs.condCmpReg_agree,
    `JanusASL.Proofs.condSel_agree,
    `JanusASL.Proofs.div_agree,
    `JanusASL.Proofs.Ensures.toASL,
    `JanusASL.Proofs.extr_agree,
    `JanusASL.Proofs.ldstImm9_agree,
    `JanusASL.Proofs.ldstReg_agree,
    `JanusASL.Proofs.ldrLit_agree,
    `JanusASL.Proofs.ldstPair_agree,
    `JanusASL.Proofs.ldstUImm_agree,
    `JanusASL.Proofs.logicalImm_agree,
    `JanusASL.Proofs.logicalShifted_agree,
    `JanusASL.Proofs.madd_agree,
    `JanusASL.Proofs.maddl_agree,
    `JanusASL.Proofs.moveWide_agree,
    `JanusASL.Proofs.mulh_agree,
    `JanusASL.Proofs.pcrel_agree,
    `JanusASL.Proofs.rbit_agree,
    `JanusASL.Proofs.ret_agree,
    `JanusASL.Proofs.rev16_agree,
    `JanusASL.Proofs.rev32_agree,
    `JanusASL.Proofs.rev64_agree,
    `JanusASL.Proofs.run_agree,
    `JanusASL.Proofs.shiftV_agree,
    `JanusASL.Proofs.step_agree,
    `JanusASL.Proofs.StepOK.of_agree,
    `JanusASL.Proofs.tb_agree]

/-- Theorems that may be provided under one of several names: each group needs at least one present
theorem, and every present one is audited like the rest. The four example transfers are either the
hand-copied `JanusASL.Examples.<X>.correctness_asl` or, once the `janus verify --asl` integration
is merged (it derives them per run as `JanusASLCorollary.correctness_asl` from the artifacts; see
`scripts/asl.sh verify`), its soundness theorem `JanusASL.Verify.classify_sound`. On that merge this
file must also `import JanusASL.Verify`; without it neither name is present and the audit fails. -/
def janusAslAlternatives : List (List Name) := [
    [`JanusASL.Examples.Add128.correctness_asl, `JanusASL.Verify.classify_sound],
    [`JanusASL.Examples.Add.correctness_asl, `JanusASL.Verify.classify_sound],
    [`JanusASL.Examples.Max.correctness_asl, `JanusASL.Verify.classify_sound],
    [`JanusASL.Examples.Mul64.correctness_asl, `JanusASL.Verify.classify_sound]]

elab "#janus_asl_audit" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in env.constants.toList do
    if (`JanusASL).isPrefixOf name && (name.toString.endsWith "_agree" || name.toString.endsWith "_asl" ||
        name.toString.endsWith "toASL") && !janusAslAudited.contains name then
      if !(janusAslAlternatives.any (·.contains name)) then
        throwError "{name} is not on the audit list"
  for name in janusAslAudited do
    match env.find? name with
    | some (.thmInfo info) =>
      let axs ← liftCoreM <| Lean.collectAxioms name
      let bad := axs.filter (fun a => !allowed.contains a)
      if !bad.isEmpty then
        throwError "{name} uses {bad}"
      let stmt ← liftTermElabM <| Meta.ppExpr info.type
      logInfo m!"{name}: {axs.toList}\n  {stmt}"
    | some _ => throwError "{name} is not a theorem"
    | none => throwError "{name} is missing"
  let mut nalt := 0
  for grp in janusAslAlternatives do
    let present := grp.filter (fun n => (env.find? n).isSome)
    if present.isEmpty then throwError "none of {grp} exists"
    for name in present do
      match env.find? name with
      | some (.thmInfo info) =>
        let axs ← liftCoreM <| Lean.collectAxioms name
        let bad := axs.filter (fun a => !allowed.contains a)
        if !bad.isEmpty then throwError "{name} uses {bad}"
        let stmt ← liftTermElabM <| Meta.ppExpr info.type
        logInfo m!"{name}: {axs.toList}\n  {stmt}"
        nalt := nalt + 1
      | _ => throwError "{name} is not a theorem"
  logInfo m!"audited {janusAslAudited.length + nalt} theorems: only propext, Classical.choice, Quot.sound"

#janus_asl_audit
