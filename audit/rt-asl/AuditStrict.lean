import JanusASL.Proofs
import JanusASL.Verify
import Lean

/-! # A stricter audit of the JanusASL theorems (docs/AUDIT-ASL.md, finding A6)

`JanusASL/Audit.lean` selects theorems by name suffix (`_agree`, `_asl`, `toASL`) and checks
only their axioms. It does not fail when a documented theorem is missing or renamed, and it
does not look at what the theorems state, so a weakened statement (an extra hypothesis, a
`True` conclusion) passes. This audit, run by `audit/rt-asl/run.sh`:

* requires every theorem of docs/ASL.md's table by name, as a `theorem` (not an axiom, `opaque`
  or a definition), with only `propext`, `Classical.choice`, `Quot.sound`;
* fails if a further `JanusASL.*` declaration matches the old audit's suffixes without being in
  the list (so the list and the documentation stay in step);
* prints every statement (`STMT name : type`, with full names) for run.sh to compare with the
  reviewed copy `audit/rt-asl/asl-statements.golden`; any change to a statement must be
  re-reviewed. -/

open Lean Elab Command Meta

def expected : List Name := [
  -- 31 data-processing and branch encoding-class theorems
  ``JanusASL.Proofs.addSubImm_agree, ``JanusASL.Proofs.addSubShifted_agree, ``JanusASL.Proofs.addSubExt_agree,
  ``JanusASL.Proofs.addSubCarry_agree, ``JanusASL.Proofs.logicalShifted_agree, ``JanusASL.Proofs.logicalImm_agree,
  ``JanusASL.Proofs.moveWide_agree, ``JanusASL.Proofs.bitfield_agree, ``JanusASL.Proofs.extr_agree,
  ``JanusASL.Proofs.pcrel_agree, ``JanusASL.Proofs.condSel_agree, ``JanusASL.Proofs.condCmpReg_agree,
  ``JanusASL.Proofs.condCmpImm_agree, ``JanusASL.Proofs.madd_agree, ``JanusASL.Proofs.maddl_agree,
  ``JanusASL.Proofs.mulh_agree, ``JanusASL.Proofs.div_agree, ``JanusASL.Proofs.shiftV_agree,
  ``JanusASL.Proofs.rbit_agree, ``JanusASL.Proofs.clz_agree, ``JanusASL.Proofs.cls_agree,
  ``JanusASL.Proofs.rev16_agree, ``JanusASL.Proofs.rev32_agree, ``JanusASL.Proofs.rev64_agree,
  ``JanusASL.Proofs.b_agree, ``JanusASL.Proofs.bcond_agree, ``JanusASL.Proofs.cb_agree, ``JanusASL.Proofs.tb_agree,
  ``JanusASL.Proofs.br_agree, ``JanusASL.Proofs.blr_agree, ``JanusASL.Proofs.ret_agree,
  -- 5 load/store encoding classes
  ``JanusASL.Proofs.ldstUImm_agree, ``JanusASL.Proofs.ldstImm9_agree, ``JanusASL.Proofs.ldstReg_agree,
  ``JanusASL.Proofs.ldrLit_agree, ``JanusASL.Proofs.ldstPair_agree,
  -- assembly and whole runs
  ``JanusASL.Proofs.step_agree, ``JanusASL.Proofs.run_agree, ``JanusASL.Proofs.Ensures.toASL,
  ``JanusASL.Proofs.StepOK.of_agree,
  -- `janus verify --asl` (the four example transfers are derived from the artifacts per run,
  -- `scripts/asl.sh verify`): the soundness of its kernel-evaluated coverage check
  ``JanusASL.Verify.classify_sound]

elab "#janus_asl_audit_strict" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array String := #[]
  for n in expected do
    match env.find? n with
    | none => bad := bad.push s!"missing {n}"
    | some (.thmInfo i) =>
      let axs ← liftCoreM <| Lean.collectAxioms n
      let extra := axs.filter (fun a => !allowed.contains a)
      if !extra.isEmpty then bad := bad.push s!"{n} uses {extra}"
      let fmt ← liftTermElabM <| withOptions (fun o => (o.set `pp.fullNames true).set `pp.width 100000) <|
        ppExpr i.type
      logInfo m!"STMT {n} : {fmt.pretty 100000}"
    | some _ => bad := bad.push s!"{n} is not a theorem"
  for (n, _) in env.constants.toList do
    if (`JanusASL).isPrefixOf n && !n.isInternal && (n.toString.endsWith "_agree" || n.toString.endsWith "_asl" ||
        n.toString.endsWith "toASL") && !expected.contains n then
      bad := bad.push s!"unlisted {n}"
  if bad.isEmpty then
    logInfo m!"strict audit ok: {expected.length} theorems"
  else
    throwError "strict audit FAILED:\n{"\n".intercalate bad.toList}"

#janus_asl_audit_strict
