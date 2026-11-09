import Janus

/-!
# Regression test: kernel-safe `janus_carry` and no `reduceCtorEq` in the executor simp contexts

Two more shapes of "(kernel) deep recursion detected" (arm64/amd64 `(*uint256.Int).Float64`, U7):

* `janus_carry` proves its goal by `checkLe_sound`/`check_sound`, whose conclusion
  `Tm.eval atoms a ≤ Tm.eval atoms b` is only convertible to the goal by unfolding `Tm.eval`. With a
  big symbolic atom (here a load after a chain of zero-limb stores) the kernel's `Nat` literal
  extension tries to evaluate the atom. The soundness lemma is therefore proved over FRESH variables
  in an auxiliary lemma and applied to the atoms (`Janus.Tactic.Carry.proveEq`).
* the default simproc `reduceCtorEq` proves `(e + 1022) * 2 ^ 52 = 0` false with `Nat.noConfusion`;
  the kernel then unfolds `Nat.mul` along the `2 ^ 52` literal. `withExecSimp` (arm64 and amd64) erases it.

The theorems must elaborate and kernel-check quickly (the kernel check is part of `theorem`); the
meta checks fail if the simprocs of the executor contexts contain `reduceCtorEq`, and the last one
checks that the aux lemma construction produced an ordinary kernel-checked theorem.
-/

namespace JanusTests.KernelSafeCarry
open Janus.Arm64 Lean Meta Elab Tactic

def W (m : Memory) (z : Nat) : Memory :=
  (((((((m.writeLE z 8 0).writeLE (z+8) 8 0).writeLE (z+16) 8 0).writeLE (z+24) 8 0).writeLE (z+32) 8 0).writeLE (z+40) 8 0).writeLE (z+48) 8 0).writeLE (z+56) 8 0
def X (m : Memory) (z p : Nat) : Nat := revContainersNat 8 1 ((W m z).readLE p 8) % 2^64

/-! ## `janus_carry` with big atoms -/

theorem carry_add_big (m : Memory) (z p q : Nat) :
    (X m z p + X m z q) % 2 ^ 64 + 2 ^ 64 * ((X m z p + X m z q) / 2 ^ 64) = X m z p + X m z q := by
  janus_carry

theorem carry_le_big (m : Memory) (z p q : Nat) :
    X m z p * 2 ^ 64 + X m z q ≤ X m z p * 2 ^ 64 + 2 ^ 64 + X m z q := by
  janus_carry

theorem carry_mul_big (m : Memory) (z p q : Nat) :
    X m z p * X m z q / 2 ^ 64 * 2 ^ 64 + X m z p * X m z q % 2 ^ 64 = X m z p * X m z q := by
  janus_carry

/-- A false statement is still rejected. -/
example (m : Memory) (z p q : Nat) (h : False) : X m z p + X m z q ≤ 2 ^ 64 + 5 := by
  fail_if_success janus_carry
  exact h.elim

/-! ## no `reduceCtorEq` in the executor simp contexts -/

example : True := by
  run_tac do
    let ok ← Janus.Tactic.withExecSimp (← Janus.Tactic.Cfg.new) (fun _ sp _ => do
      pure (sp.any fun s => s.simprocNames.contains ``reduceCtorEq))
    if ok then throwError "arm64 executor simp context contains reduceCtorEq (kernel deep recursion hazard, see KernelSafeCarry.lean)"
    let ok ← Janus.Amd64.Tactic.withExecSimp (← Janus.Amd64.Tactic.Cfg.new) (fun _ sp _ => do
      pure (sp.any fun s => s.simprocNames.contains ``reduceCtorEq))
    if ok then throwError "amd64 executor simp context contains reduceCtorEq (kernel deep recursion hazard, see KernelSafeCarry.lean)"

  trivial
end JanusTests.KernelSafeCarry
