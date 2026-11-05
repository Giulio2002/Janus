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

/-- The total advance of the bump pointer for a message of `Lm` bytes. -/
def atot (Lm : Nat) : Nat := (Lm + Lm + 63) / 16 * 16

/-- The memory after the allocation part of the stub: the sign byte of number 2 (at `x13v2 - 1`), the bump
pointer advanced by `A`, the four fields of the `wrapError` object at `p`. -/
def allocMem (m : Memory) (x13v2 n2 p A Lm e : Nat) : Memory :=
  ((((m.writeLE (x13v2 - 1) 1 (48 - 3 * n2)).writeLE 4194304 8 (p + A)).writeLE p 8 (p + 32)).writeLE (p + 8) 8 Lm
    |>.writeLE (p + 16) 8 8738).writeLE (p + 24) 8 e

@[simp] theorem allocMem_accessible (m : Memory) (x n p A Lm e a k : Nat) (w : Bool) :
    (allocMem m x n p A Lm e).accessible a k w = m.accessible a k w := by
  simp [allocMem]

end Janus.Contracts.ErrorfRealStages
