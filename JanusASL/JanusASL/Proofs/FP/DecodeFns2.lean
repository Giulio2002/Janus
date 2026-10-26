import JanusASL.Proofs.FP.Conv
import JanusASL.Proofs.FP.Agree

/-! # The scalar integer to floating-point decode functions (SCVTF, UCVTF) -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_dec_scvtf_0 {js : Janus.Arm64.State} {st : SState} (hf : FPRel js st) (Rd Rn : BitVec 5) (sf : BitVec 1) :
    (decode_scvtf_float_int_aarch64_instrs_float_convert_int Rd Rn 2#3 0#2 0#2 sf).run st =
      (execute_aarch64_instrs_float_convert_int Rd.toNat 32 (if (sf == 1#1) = true then 64 else 32) Rn.toNat
        FPConvOp.FPConvOp_CVT_ItoF 0 (aslRM (Janus.Arm64.FP.roundingMode js.fpcr.toNat)) false).run st := by
  unfold decode_scvtf_float_int_aarch64_instrs_float_convert_int
  have hfcr := run_FPCR_read hf
  have hfn := hfn_fpcr js
  cfg_simp [hfcr, run_FPRoundingMode, hfn, run_undefined_bool, undefined_FPConvOp, undefined_FPRounding, run_internal_pick]
  by_cases hs : sf = 1#1 <;> simp [hs] <;> rfl

theorem run_dec_scvtf_1 {js : Janus.Arm64.State} {st : SState} (hf : FPRel js st) (Rd Rn : BitVec 5) (sf : BitVec 1) :
    (decode_scvtf_float_int_aarch64_instrs_float_convert_int Rd Rn 2#3 0#2 1#2 sf).run st =
      (execute_aarch64_instrs_float_convert_int Rd.toNat 64 (if (sf == 1#1) = true then 64 else 32) Rn.toNat
        FPConvOp.FPConvOp_CVT_ItoF 0 (aslRM (Janus.Arm64.FP.roundingMode js.fpcr.toNat)) false).run st := by
  unfold decode_scvtf_float_int_aarch64_instrs_float_convert_int
  have hfcr := run_FPCR_read hf
  have hfn := hfn_fpcr js
  cfg_simp [hfcr, run_FPRoundingMode, hfn, run_undefined_bool, undefined_FPConvOp, undefined_FPRounding, run_internal_pick]
  by_cases hs : sf = 1#1 <;> simp [hs] <;> rfl

theorem run_dec_ucvtf_0 {js : Janus.Arm64.State} {st : SState} (hf : FPRel js st) (Rd Rn : BitVec 5) (sf : BitVec 1) :
    (decode_ucvtf_float_int_aarch64_instrs_float_convert_int Rd Rn 3#3 0#2 0#2 sf).run st =
      (execute_aarch64_instrs_float_convert_int Rd.toNat 32 (if (sf == 1#1) = true then 64 else 32) Rn.toNat
        FPConvOp.FPConvOp_CVT_ItoF 0 (aslRM (Janus.Arm64.FP.roundingMode js.fpcr.toNat)) true).run st := by
  unfold decode_ucvtf_float_int_aarch64_instrs_float_convert_int
  have hfcr := run_FPCR_read hf
  have hfn := hfn_fpcr js
  cfg_simp [hfcr, run_FPRoundingMode, hfn, run_undefined_bool, undefined_FPConvOp, undefined_FPRounding, run_internal_pick]
  by_cases hs : sf = 1#1 <;> simp [hs] <;> rfl

theorem run_dec_ucvtf_1 {js : Janus.Arm64.State} {st : SState} (hf : FPRel js st) (Rd Rn : BitVec 5) (sf : BitVec 1) :
    (decode_ucvtf_float_int_aarch64_instrs_float_convert_int Rd Rn 3#3 0#2 1#2 sf).run st =
      (execute_aarch64_instrs_float_convert_int Rd.toNat 64 (if (sf == 1#1) = true then 64 else 32) Rn.toNat
        FPConvOp.FPConvOp_CVT_ItoF 0 (aslRM (Janus.Arm64.FP.roundingMode js.fpcr.toNat)) true).run st := by
  unfold decode_ucvtf_float_int_aarch64_instrs_float_convert_int
  have hfcr := run_FPCR_read hf
  have hfn := hfn_fpcr js
  cfg_simp [hfcr, run_FPRoundingMode, hfn, run_undefined_bool, undefined_FPConvOp, undefined_FPRounding, run_internal_pick]
  by_cases hs : sf = 1#1 <;> simp [hs] <;> rfl

end JanusASL.Proofs
