import Janus.Arm64.State

/-!
# One AArch64 step (placeholder; implemented by the ISA model)

`step w s` decodes the 32-bit word `w` fetched at `s.pc` and executes it, returning the
successor state (with `pc` advanced or redirected) or a `Fault`.
-/

namespace Janus.Arm64

def step (w : Nat) (s : State) : Except Fault State :=
  .error (.undecodable s.pc.toNat w)

end Janus.Arm64
