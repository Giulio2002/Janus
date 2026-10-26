import JanusASL.Proofs.FP.Sqrt
import JanusASL.Proofs.FP.Div
import JanusASL.Proofs.FP.Exec
import JanusASL.Proofs.FP.Unpack2

/-! # Scalar FMUL, FDIV, FMADD/FMSUB/FNMADD/FNMSUB and FSQRT: execute functions against Janus -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_FPNegN {N : Nat} (hN : N = 32 ∨ N = 64) {js : Janus.Arm64.State} {s : SState} (hc : LinuxEL0Config s)
    (hf : FPRel js s) (op : BitVec N) :
    (FPNeg op).run s = .ok (BitVec.ofNat N (Janus.Arm64.FP.fpNeg (fmtN N) js.fpcr.toNat op.toNat)) s := by
  rcases hN with rfl | rfl
  · exact run_FPNeg32 hc hf.fpcr hf.fpcrRes0 op
  · exact run_FPNeg64 hc hf.fpcr hf.fpcrRes0 op

theorem fpNeg_lt (N : Nat) (hN : N = 32 ∨ N = 64) (fpcr op : Nat) (h : op < 2 ^ N) :
    Janus.Arm64.FP.fpNeg (fmtN N) fpcr op < 2 ^ N := by
  unfold Janus.Arm64.FP.fpNeg Janus.Float.flipSign
  have hs : (fmtN N).signBit * 2 = 2 ^ N := by
    rcases hN with rfl | rfl <;> decide
  have h1 : op % (fmtN N).signBit < (fmtN N).signBit := Nat.mod_lt _ (by rcases hN with rfl | rfl <;> decide)
  split
  · exact h
  · split <;> omega

theorem processDenorm_lt (fpcr : Nat) (t : Janus.Arm64.FP.FPType) :
    ExcLt (Janus.Arm64.FP.processDenorm fpcr t) := by
  rcases processDenorm_cases fpcr t with h | h <;> rw [h]
  · exact ExcLt.raise (by decide)
  · exact ExcLt.empty

theorem fpDiv_lt (f : Janus.Float.Fmt) (fpcr a b : Nat) : ExcLt (Janus.Arm64.FP.fpDiv f fpcr a b).2 := by
  unfold Janus.Arm64.FP.fpDiv
  dsimp only
  exc_lt

theorem fpSqrt_lt (f : Janus.Float.Fmt) (fpcr a : Nat) : ExcLt (Janus.Arm64.FP.fpSqrt f fpcr a).2 := by
  unfold Janus.Arm64.FP.fpSqrt
  dsimp only
  exc_lt
  all_goals exact processDenorm_lt _ _

end JanusASL.Proofs
