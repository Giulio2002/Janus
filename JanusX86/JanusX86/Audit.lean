import JanusX86.Proofs
import Lean

/-! Audit of the JanusX86 theorems (`scripts/x86formal.sh prove`).

* The audited theorems are an explicit list. Each must exist and be a theorem; a declaration under
  `JanusX86` named `*_agree` that is not on the list fails the audit, so a renamed, removed or
  added class theorem cannot go unnoticed.
* Each may use only `propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`, no
  `Lean.ofReduceBool`, i.e. no `native_decide`/`bv_decide`).
* Each statement is printed, for review and diffs. -/

open Lean Elab Command

def janusX86Audited : List Name := [
    `JanusX86.Proofs.alu_eg_reg_agree,
    `JanusX86.Proofs.alu_eg_mem_agree,
    `JanusX86.Proofs.alu_ge_agree,
    `JanusX86.Proofs.alu_ai_agree,
    `JanusX86.Proofs.alu_ei_agree,
    `JanusX86.Proofs.unary_agree,
    `JanusX86.Proofs.mov_agree,
    `JanusX86.Proofs.lea_agree,
    `JanusX86.Proofs.movi_agree,
    `JanusX86.Proofs.test_eg_agree,
    `JanusX86.Proofs.movoi_agree,
    `JanusX86.Proofs.jcc8_agree,
    `JanusX86.Proofs.jmp_agree,
    `JanusX86.Proofs.call_agree,
    `JanusX86.Proofs.ret_agree,
    `JanusX86.Proofs.movx_agree,
    `JanusX86.Proofs.setcc_agree,
    `JanusX86.Proofs.cmov_agree,
    `JanusX86.Proofs.jcc32_agree,
    `JanusX86.Proofs.mul_agree,
    `JanusX86.Proofs.imul1_agree,
    `JanusX86.Proofs.push_agree,
    `JanusX86.Proofs.pop_agree,
    `JanusX86.Proofs.shift_agree,
    `JanusX86.Proofs.shift_agree_cf,
    `JanusX86.Proofs.jmp_ind_agree,
    `JanusX86.Proofs.call_ind_agree]

elab "#janus_x86_audit" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in env.constants.toList do
    if (`JanusX86).isPrefixOf name && name.toString.endsWith "_agree" && !janusX86Audited.contains name then
      throwError "{name} is not on the audit list"
  for name in janusX86Audited do
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
  logInfo m!"audited {janusX86Audited.length} theorems: only propext, Classical.choice, Quot.sound"

#janus_x86_audit
