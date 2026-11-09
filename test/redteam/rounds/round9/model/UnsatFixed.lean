import Janus
open Janus Janus.Arm64 Janus.Tactic Janus.Contracts

/-! Round 9 C1 regression (must NOT compile): the pre-fix vacuity argument against the fixed
contract. The big call state still satisfies `NewobjectPre`, but the contract now also requires
`H` there, and `H` is the theorem's parameter: nothing forces it (for `H := fun _ _ _ _ => False`
the contract holds), so the statement below is false and no proof exists. -/
theorem newobject_unsat_fixed (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (H : RtReady) :
    ¬ NewobjectContract p addr rt 4096 H := by
  intro h
  exact absurd h (by simp_all [NewobjectContract, Summary])
