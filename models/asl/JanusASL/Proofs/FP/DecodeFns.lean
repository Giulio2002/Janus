import JanusASL.Proofs.FP.Agree

/-! # The scalar floating-point arithmetic decode functions at `ftype` 0 and 1 -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_dec_fadd_0 (Rd Rn Rm : BitVec 5) (op : BitVec 1) (st : SState) :
    (decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub Rd Rn op Rm 0#2).run st =
      (execute_aarch64_instrs_float_arithmetic_add_sub Rd.toNat 32 Rm.toNat Rn.toNat (op == 1#1)).run st := by
  unfold decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub
  cfg_simp
  all_goals rfl

theorem run_dec_fadd_1 (Rd Rn Rm : BitVec 5) (op : BitVec 1) (st : SState) :
    (decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub Rd Rn op Rm 1#2).run st =
      (execute_aarch64_instrs_float_arithmetic_add_sub Rd.toNat 64 Rm.toNat Rn.toNat (op == 1#1)).run st := by
  unfold decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub
  cfg_simp
  all_goals rfl

theorem run_dec_fsub_0 (Rd Rn Rm : BitVec 5) (op : BitVec 1) (st : SState) :
    (decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub Rd Rn op Rm 0#2).run st =
      (execute_aarch64_instrs_float_arithmetic_add_sub Rd.toNat 32 Rm.toNat Rn.toNat (op == 1#1)).run st := by
  unfold decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub
  cfg_simp
  all_goals rfl

theorem run_dec_fsub_1 (Rd Rn Rm : BitVec 5) (op : BitVec 1) (st : SState) :
    (decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub Rd Rn op Rm 1#2).run st =
      (execute_aarch64_instrs_float_arithmetic_add_sub Rd.toNat 64 Rm.toNat Rn.toNat (op == 1#1)).run st := by
  unfold decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub
  cfg_simp
  all_goals rfl

theorem run_dec_fmul_0 (Rd Rn Rm : BitVec 5) (op : BitVec 1) (st : SState) :
    (decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product Rd Rn op Rm 0#2).run st =
      (execute_aarch64_instrs_float_arithmetic_mul_product Rd.toNat 32 Rm.toNat Rn.toNat (op == 1#1)).run st := by
  unfold decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product
  cfg_simp
  all_goals rfl

theorem run_dec_fmul_1 (Rd Rn Rm : BitVec 5) (op : BitVec 1) (st : SState) :
    (decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product Rd Rn op Rm 1#2).run st =
      (execute_aarch64_instrs_float_arithmetic_mul_product Rd.toNat 64 Rm.toNat Rn.toNat (op == 1#1)).run st := by
  unfold decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product
  cfg_simp
  all_goals rfl

theorem run_dec_fdiv_0 (Rd Rn Rm : BitVec 5) (st : SState) :
    (decode_fdiv_float_aarch64_instrs_float_arithmetic_div Rd Rn Rm 0#2).run st =
      (execute_aarch64_instrs_float_arithmetic_div Rd.toNat 32 Rm.toNat Rn.toNat).run st := by
  unfold decode_fdiv_float_aarch64_instrs_float_arithmetic_div
  cfg_simp
  all_goals rfl

theorem run_dec_fsqrt_0 (Rd Rn : BitVec 5) (opc : BitVec 2) (st : SState) (hop : opc = 3#2) :
    (decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc 0#2).run st =
      (execute_aarch64_instrs_float_arithmetic_unary Rd.toNat 32 FPUnaryOp.FPUnaryOp_SQRT Rn.toNat).run st := by
  subst hop
  unfold decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary
  cfg_simp
  all_goals rfl

theorem run_dec_fdiv_1 (Rd Rn Rm : BitVec 5) (st : SState) :
    (decode_fdiv_float_aarch64_instrs_float_arithmetic_div Rd Rn Rm 1#2).run st =
      (execute_aarch64_instrs_float_arithmetic_div Rd.toNat 64 Rm.toNat Rn.toNat).run st := by
  unfold decode_fdiv_float_aarch64_instrs_float_arithmetic_div
  cfg_simp
  all_goals rfl

theorem run_dec_fsqrt_1 (Rd Rn : BitVec 5) (opc : BitVec 2) (st : SState) (hop : opc = 3#2) :
    (decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc 1#2).run st =
      (execute_aarch64_instrs_float_arithmetic_unary Rd.toNat 64 FPUnaryOp.FPUnaryOp_SQRT Rn.toNat).run st := by
  subst hop
  unfold decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary
  cfg_simp
  all_goals rfl

theorem run_dec_fmadd_0 (Rd Rn Ra Rm : BitVec 5) (o0 o1 : BitVec 1) (st : SState) :
    (decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 0#2).run st =
      (execute_aarch64_instrs_float_arithmetic_mul_add_sub Ra.toNat Rd.toNat 32 Rm.toNat Rn.toNat (o0 != o1) (o1 == 1#1)).run st := by
  unfold decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub
  cfg_simp
  all_goals rfl

theorem run_dec_fmadd_1 (Rd Rn Ra Rm : BitVec 5) (o0 o1 : BitVec 1) (st : SState) :
    (decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 1#2).run st =
      (execute_aarch64_instrs_float_arithmetic_mul_add_sub Ra.toNat Rd.toNat 64 Rm.toNat Rn.toNat (o0 != o1) (o1 == 1#1)).run st := by
  unfold decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub
  cfg_simp
  all_goals rfl

theorem run_dec_fmsub_0 (Rd Rn Ra Rm : BitVec 5) (o0 o1 : BitVec 1) (st : SState) :
    (decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 0#2).run st =
      (execute_aarch64_instrs_float_arithmetic_mul_add_sub Ra.toNat Rd.toNat 32 Rm.toNat Rn.toNat (o0 != o1) (o1 == 1#1)).run st := by
  unfold decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub
  cfg_simp
  all_goals rfl

theorem run_dec_fmsub_1 (Rd Rn Ra Rm : BitVec 5) (o0 o1 : BitVec 1) (st : SState) :
    (decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 1#2).run st =
      (execute_aarch64_instrs_float_arithmetic_mul_add_sub Ra.toNat Rd.toNat 64 Rm.toNat Rn.toNat (o0 != o1) (o1 == 1#1)).run st := by
  unfold decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub
  cfg_simp
  all_goals rfl

theorem run_dec_fnmadd_0 (Rd Rn Ra Rm : BitVec 5) (o0 o1 : BitVec 1) (st : SState) :
    (decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 0#2).run st =
      (execute_aarch64_instrs_float_arithmetic_mul_add_sub Ra.toNat Rd.toNat 32 Rm.toNat Rn.toNat (o0 != o1) (o1 == 1#1)).run st := by
  unfold decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub
  cfg_simp
  all_goals rfl

theorem run_dec_fnmadd_1 (Rd Rn Ra Rm : BitVec 5) (o0 o1 : BitVec 1) (st : SState) :
    (decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 1#2).run st =
      (execute_aarch64_instrs_float_arithmetic_mul_add_sub Ra.toNat Rd.toNat 64 Rm.toNat Rn.toNat (o0 != o1) (o1 == 1#1)).run st := by
  unfold decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub
  cfg_simp
  all_goals rfl

theorem run_dec_fnmsub_0 (Rd Rn Ra Rm : BitVec 5) (o0 o1 : BitVec 1) (st : SState) :
    (decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 0#2).run st =
      (execute_aarch64_instrs_float_arithmetic_mul_add_sub Ra.toNat Rd.toNat 32 Rm.toNat Rn.toNat (o0 != o1) (o1 == 1#1)).run st := by
  unfold decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub
  cfg_simp
  all_goals rfl

theorem run_dec_fnmsub_1 (Rd Rn Ra Rm : BitVec 5) (o0 o1 : BitVec 1) (st : SState) :
    (decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 1#2).run st =
      (execute_aarch64_instrs_float_arithmetic_mul_add_sub Ra.toNat Rd.toNat 64 Rm.toNat Rn.toNat (o0 != o1) (o1 == 1#1)).run st := by
  unfold decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub
  cfg_simp
  all_goals rfl

end JanusASL.Proofs
