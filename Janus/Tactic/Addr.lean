import Janus.Tactic.Core

/-!
# Evaluating layout-dependent code addresses (arm64)

`segAddr Extracted.program "pkg.F"` is the address of an extracted function. Proofs that mention
code addresses as values (a return address saved in a frame, a closure's code pointer stored in a
funcval) state them this way instead of as literals, so that they survive changes of the binary's
layout. `reduceSegAddr` evaluates such a term on a closed program to its literal, justified by a
kernel-checked `rfl` lemma (as `Janus.Amd64.Tactic.reduceSegAddr` on amd64), so that the
executor sees literal addresses: `simp only [reduceSegAddr, Nat.reduceAdd] at h`.
-/

namespace Janus.Tactic

open Lean Meta

/-- Evaluate the closed address term `e` to a literal. -/
def evalAddrArm (e : Expr) : Simp.SimpM Simp.Step := do
  if e.hasFVar || e.hasMVar then return .continue
  let some v ← evalNat e | return .continue
  let ty ← mkEq e (mkNatLit v)
  let name ← try mkAuxLemma [] ty (← mkEqRefl (mkNatLit v)) catch _ => return .continue
  return .done { expr := mkNatLit v, proof? := mkConst name }

simproc_decl reduceSegAddr (segAddr _ _) := evalAddrArm

end Janus.Tactic
