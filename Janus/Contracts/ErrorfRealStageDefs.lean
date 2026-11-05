import Janus.Contracts.ErrorfRealLoops
import Janus.Contracts.ErrorfRealFmt

/-!
# Definitions shared by the stages of the real-format `fmt.errorf` stub (arm64)
-/

namespace Janus.Contracts.ErrorfRealStages

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Errorf Janus.Contracts

/-- The registers the stub keeps through its run: the errorString (`x5 = e`, `x6` its text pointer, `x7`
its length), the constant 10, and the ABI registers `x18`, `x28`, `x29`, `x30`. -/
def Pers (s : State) (R : Nat → W64) (e tp tl : Nat) : Prop :=
  R 5 = BitVec.ofNat 64 e ∧ R 6 = BitVec.ofNat 64 tp ∧ R 7 = BitVec.ofNat 64 tl ∧ R 15 = 10#64 ∧
    R 18 = s.regs 18 ∧ R 28 = s.regs 28 ∧ R 29 = s.regs 29 ∧ R 30 = s.regs 30

end Janus.Contracts.ErrorfRealStages
