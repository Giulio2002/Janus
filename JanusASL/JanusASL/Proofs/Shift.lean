import JanusASL.Proofs.Ops

/-! `ShiftReg` (and `ROR`, the `Int`-amount shifts of lean-sail) against Janus' `shiftReg`. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem int_shiftLeft_nat {w : Nat} (b : BitVec w) (k : Nat) : b <<< ((k : Nat) : Int) = b <<< k := rfl

theorem int_shiftRight_nat {w : Nat} (b : BitVec w) (k : Nat) : b >>> ((k : Nat) : Int) = b >>> k := by
  cases k with
  | zero =>
    show (b <<< (-((0 : Nat) : Int))) = b >>> 0
    show BitVec.shiftLeft b 0 = b >>> 0
    simp
  | succ k => show (b <<< (-((k + 1 : Nat) : Int))) = _; rfl

theorem ROR_eq {N : Nat} (x : BitVec N) {k : Nat} (hk : k < N) : ROR x k = x.rotateRight k := by
  unfold ROR
  by_cases h0 : k = 0
  · subst h0; simp [BitVec.rotateRight, BitVec.rotateRightAux]
  · have hb : (k == 0) = false := by simp [h0]
    have hm : Nat.mod k N = k := Nat.mod_eq_of_lt hk
    simp only [hb, Bool.false_eq_true, ite_false, Sail.BitVec.length, hm]
    have : ((N : Int) - (k : Int)) = ((N - k : Nat) : Int) := by omega
    rw [this, int_shiftLeft_nat]
    simp [BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt hk]

/-- The sail-arm shift type for a 2-bit `shift` field. -/
def aslShiftType (t : Janus.Arm64.ShiftType) : ArmASL.ShiftType :=
  match t with
  | .lsl => .ShiftType_LSL
  | .lsr => .ShiftType_LSR
  | .asr => .ShiftType_ASR
  | .ror => .ShiftType_ROR

theorem run_ShiftReg {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {m : Nat} (hm : m < 32)
    {N : Nat} (hN : N = 32 ∨ N = 64) (t : Janus.Arm64.ShiftType) {k : Nat} (hk : k < N) :
    (ShiftReg (m : Int) (aslShiftType t) (k : Int) N).run s =
      .ok (Janus.Arm64.shiftReg (js.getX N m) t k) s := by
  have hN0 : 0 < N := by omega
  cases t <;> simp only [ShiftReg, aslShiftType, run_bind, run_X_read_rel h hm hN, run_pure,
    Janus.Arm64.shiftReg, int_shiftLeft_nat, int_shiftRight_nat]
  · rfl
  · rw [run_sail_assert_of (by simp; omega)]
    rw [show ((k : Int).toNat) = k by omega, ROR_eq _ hk]

end JanusASL.Proofs
