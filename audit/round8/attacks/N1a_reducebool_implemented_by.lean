import Extracted
/-! ATTACK N1a (expected BLOCKED): kernel native reduction. `f` unfolds to `false` but is
compiled as `g = true` (`@[implemented_by]`), and `Lean.reduceBool f` is reduced by running the
compiled code, so `reduceBool f = true` and `reduceBool f = reduceBool fl = false` give
`true = false`, hence a false theorem ("Add returns x * y"). Lean's `Lean.reduceBool` is an opaque
whose value uses the axiom `Lean.trustCompiler`, so `collectAxioms` reports it and the axiom
allow-list rejects it. Kept as a regression row for the reflective tactics (janus_carry,
janus_ring), which must stay kernel-checked (`Eq.refl true`, never native evaluation). -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
def g : Bool := true
@[implemented_by g] def f0 : Bool := false
def f : Bool := f0
def fl : Bool := false
theorem viaNative : Lean.reduceBool f = true := by rfl
theorem viaNative2 : Lean.reduceBool fl = false := by rfl
theorem cong : Lean.reduceBool f = Lean.reduceBool fl := by unfold f f0 fl; rfl
theorem bad : False := Bool.noConfusion (viaNative.symm.trans (cong.trans viaNative2))
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := bad.elim
end Proof
