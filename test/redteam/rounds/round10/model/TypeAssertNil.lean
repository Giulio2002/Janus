import Janus
/-! Round 10 I1: the `TypeAssert` contract admits only a non-nil type (`X1` / `RBX`). Before the
fix its precondition admitted `t = nil` with `CanFail`, a call on which the real runtime faults
in about one call in 1000. -/
open Janus Janus.Contracts

example (p : Janus.Program) (a : Nat) (R : Janus.Spec.Type.IfaceModel) (H : RtReady) :
    ∃ P Q, Iface.TypeAssert p a R H = Janus.Tactic.Summary p a P Q ∧
      ∀ s, P s → (s.regs 1).toNat ≠ 0 := ⟨_, _, rfl, fun _ h => h.2.2.1⟩

example (p : Janus.Amd64.Program) (a : Nat) (R : Janus.Spec.Type.IfaceModel) (H : RtReady) :
    ∃ P Q, IfaceAmd64.TypeAssert p a R H = Janus.Amd64.Tactic.Summary p a P Q ∧
      ∀ s, P s → (s.regs 3).toNat ≠ 0 := ⟨_, _, rfl, fun _ h => h.2.2.1⟩
