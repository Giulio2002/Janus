import JanusASL.Proofs.FP.FCmp
import JanusASL.Proofs.LdStPair

/-! # Floating-point decoding: `__DecodeA64` to `__DecodeA64_DataProcFPSIMD`, and the decode functions -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_DecodeA64_FP {w : Nat} (hw : w < 2 ^ 32) (h25 : (w / 2 ^ 25) % 8 = 7) (pc : Int) (s : SState) :
    (__DecodeA64 pc (BitVec.ofNat 32 w)).run s = (__DecodeA64_DataProcFPSIMD pc (BitVec.ofNat 32 w)).run s := by
  have e : ∀ c : Nat, c < 4 → (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 25 == BitVec.ofNat 4 c) = false := by
    intro c hc
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 26 == (0b100#3 : BitVec 3)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 26 == (0b101#3 : BitVec 3)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 25 25 == (0#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 27 25 == (0b101#3 : BitVec 3)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  rw [__DecodeA64]
  simp only [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e5, e6, e8, e9,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.false_eq_true, ite_false, ite_true]

theorem run_dec_fcmp_0 (opc : BitVec 2) (Rn Rm : BitVec 5) (st : SState) :
    (decode_fcmp_float_aarch64_instrs_float_compare_uncond opc Rn Rm 0#2).run st =
      (execute_aarch64_instrs_float_compare_uncond (Sail.BitVec.access opc 0 == 1#1) 32 Rm.toNat Rn.toNat
        (Sail.BitVec.access opc 1 == 1#1)).run st := by
  unfold decode_fcmp_float_aarch64_instrs_float_compare_uncond
  cfg_simp
  all_goals rfl

theorem run_dec_fcmp_1 (opc : BitVec 2) (Rn Rm : BitVec 5) (st : SState) :
    (decode_fcmp_float_aarch64_instrs_float_compare_uncond opc Rn Rm 1#2).run st =
      (execute_aarch64_instrs_float_compare_uncond (Sail.BitVec.access opc 0 == 1#1) 64 Rm.toNat Rn.toNat
        (Sail.BitVec.access opc 1 == 1#1)).run st := by
  unfold decode_fcmp_float_aarch64_instrs_float_compare_uncond
  cfg_simp
  all_goals rfl

theorem run_dec_fcmpe_0 (opc : BitVec 2) (Rn Rm : BitVec 5) (st : SState) :
    (decode_fcmpe_float_aarch64_instrs_float_compare_uncond opc Rn Rm 0#2).run st =
      (execute_aarch64_instrs_float_compare_uncond (Sail.BitVec.access opc 0 == 1#1) 32 Rm.toNat Rn.toNat
        (Sail.BitVec.access opc 1 == 1#1)).run st := by
  unfold decode_fcmpe_float_aarch64_instrs_float_compare_uncond
  cfg_simp
  all_goals rfl

theorem run_dec_fcmpe_1 (opc : BitVec 2) (Rn Rm : BitVec 5) (st : SState) :
    (decode_fcmpe_float_aarch64_instrs_float_compare_uncond opc Rn Rm 1#2).run st =
      (execute_aarch64_instrs_float_compare_uncond (Sail.BitVec.access opc 0 == 1#1) 64 Rm.toNat Rn.toNat
        (Sail.BitVec.access opc 1 == 1#1)).run st := by
  unfold decode_fcmpe_float_aarch64_instrs_float_compare_uncond
  cfg_simp
  all_goals rfl

end JanusASL.Proofs
