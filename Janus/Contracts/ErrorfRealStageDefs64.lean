import Janus.Contracts.ErrorfRealLoops64
import Janus.Contracts.ErrorfRealFmt
import Janus.Contracts.ErrorfRealStageDefs

/-!
# Definitions shared by the stages of the real-format `fmt.errorf` stub (amd64)
-/

namespace Janus.Contracts.ErrorfRealStages64

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts

/-- The registers the stub keeps through its run: the errorString's text pointer (`r9`) and length (`r10`), and the
ABI registers `rsp`, `rbp`, `r14`, and `r15`, which holds the return address since the prologue. -/
def Pers64 (s : State) (R : Nat → W64) (tp tl : Nat) : Prop :=
  R 9 = BitVec.ofNat 64 tp ∧ R 10 = BitVec.ofNat 64 tl ∧ R 4 = s.regs 4 ∧ R 5 = s.regs 5 ∧ R 14 = s.regs 14 ∧ R 15 = retAddrOf s

end Janus.Contracts.ErrorfRealStages64
