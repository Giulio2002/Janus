import JanusX86.Proofs.AluWidth

/-! # `gpr_arith_logic_spec` against Janus' ALU result

The model's ALU operation numbers (`gpr_arith_logic_spec`: 0 ADD, 1 OR, 2 ADC, 3 AND, 4 SUB,
5 XOR, 6 SBB, 7 TEST, 8 CMP) against Janus' `AluOp`, and one lemma that covers every operation
at every width: the result, the output flag vector and the undefined mask are those of Janus'
`addFlags`/`subFlags`/`logicFlags` (`aluRes`, the computation of `execAlu`). -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- The model's operation number of a Janus ALU operation. -/
def sailOp : Janus.Amd64.AluOp → Nat
  | .add => 0
  | .or => 1
  | .adc => 2
  | .sbb => 6
  | .and => 3
  | .sub => 4
  | .xor => 5
  | .cmp => 8

/-- Janus' ALU result for operation `op` with carry-in `c` (`execAlu`). -/
def aluRes {w : Nat} (op : Janus.Amd64.AluOp) (x y : BitVec w) (c : Bool) : BitVec w × Janus.Amd64.Flags :=
  match op with
  | .add => Janus.Amd64.addFlags x y false
  | .adc => Janus.Amd64.addFlags x y c
  | .sub | .cmp => Janus.Amd64.subFlags x y false
  | .sbb => Janus.Amd64.subFlags x y c
  | .and => (x &&& y, Janus.Amd64.logicFlags (x &&& y))
  | .or => (x ||| y, Janus.Amd64.logicFlags (x ||| y))
  | .xor => (x ^^^ y, Janus.Amd64.logicFlags (x ^^^ y))

def isLogic : Janus.Amd64.AluOp → Bool
  | .and | .or | .xor => true
  | _ => false

/-- The output flag vector and undefined mask of the model's spec for `op`. -/
def aluOut (op : Janus.Amd64.AluOp) (rin : BitVec 32) (f : Janus.Amd64.Flags) : BitVec 32 × BitVec 32 :=
  if isLogic op then (outLogic rin f, _update_rflagsbits_af (Mk_rflagsbits 0#32) 1#1)
  else (outArith rin f, Mk_rflagsbits 0#32)

theorem sw_sw {w : Nat} (x : BitVec w) (h : w ≤ 64) : (x.setWidth 64).setWidth w = x := by
  have h1 : x.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt x.isLt]

theorem sw_sw8 (x : BitVec 8) : (x.setWidth 64).setWidth 8 = x := sw_sw x (by decide)
theorem sw_sw16 (x : BitVec 16) : (x.setWidth 64).setWidth 16 = x := sw_sw x (by decide)
theorem sw_sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := sw_sw x (by decide)

set_option maxHeartbeats 1000000 in
theorem run_gpr_arith_logic_spec (op : Janus.Amd64.AluOp) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (x y : BitVec w) (rin : BitVec 32) (c : Bool) (hc : _get_rflagsbits_cf rin = BitVec.ofBool c) (s : SState) :
    (gpr_arith_logic_spec (w / 8) (sailOp op) (x.setWidth 64) (y.setWidth 64) rin).run s =
      .ok ((aluRes op x y c).1.setWidth 64, (aluOut op rin (aluRes op x y c).2).1,
        (aluOut op rin (aluRes op x y c).2).2) s := by
  rcases hw with rfl | rfl | rfl | rfl <;> cases op <;>
    simp only [gpr_arith_logic_spec, gpr_arith_logic_spec_1, gpr_arith_logic_spec_2, gpr_arith_logic_spec_4,
      gpr_arith_logic_spec_8, sailOp, Nat.reduceDiv, run_bind, Sail.BitVec.truncate, BitVec.truncate_eq_setWidth,
      sw_sw8, sw_sw16, sw_sw32, BitVec.setWidth_eq, aluRes, aluOut, isLogic,
      run_gpr_add_spec_1, run_gpr_add_spec_2, run_gpr_add_spec_4, run_gpr_add_spec_8,
      run_gpr_adc_spec_1 _ _ _ c hc, run_gpr_adc_spec_2 _ _ _ c hc, run_gpr_adc_spec_4 _ _ _ c hc,
      run_gpr_adc_spec_8 _ _ _ c hc,
      run_gpr_sub_spec_1, run_gpr_sub_spec_2, run_gpr_sub_spec_4, run_gpr_sub_spec_8,
      run_gpr_sbb_spec_1 _ _ _ c hc, run_gpr_sbb_spec_2 _ _ _ c hc, run_gpr_sbb_spec_4 _ _ _ c hc,
      run_gpr_sbb_spec_8 _ _ _ c hc,
      run_gpr_and_spec_1, run_gpr_and_spec_2, run_gpr_and_spec_4, run_gpr_and_spec_8,
      run_gpr_or_spec_1, run_gpr_or_spec_2, run_gpr_or_spec_4, run_gpr_or_spec_8,
      run_gpr_xor_spec_1, run_gpr_xor_spec_2, run_gpr_xor_spec_4, run_gpr_xor_spec_8,
      run_pure, Bool.false_eq_true, ↓reduceIte, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem flagEq_fbit (o : Option Bool) : FlagEq o (fbit o) := by
  intro v hv; subst hv; rfl

theorem mk0_bits : (_get_rflagsbits_cf (Mk_rflagsbits 0#32) == 1#1) = false ∧
    (_get_rflagsbits_pf (Mk_rflagsbits 0#32) == 1#1) = false ∧
    (_get_rflagsbits_af (Mk_rflagsbits 0#32) == 1#1) = false ∧
    (_get_rflagsbits_zf (Mk_rflagsbits 0#32) == 1#1) = false ∧
    (_get_rflagsbits_sf (Mk_rflagsbits 0#32) == 1#1) = false ∧
    (_get_rflagsbits_of (Mk_rflagsbits 0#32) == 1#1) = false := by decide

theorem af1_bits : (_get_rflagsbits_cf (_update_rflagsbits_af (Mk_rflagsbits 0#32) 1#1) == 1#1) = false ∧
    (_get_rflagsbits_pf (_update_rflagsbits_af (Mk_rflagsbits 0#32) 1#1) == 1#1) = false ∧
    (_get_rflagsbits_zf (_update_rflagsbits_af (Mk_rflagsbits 0#32) 1#1) == 1#1) = false ∧
    (_get_rflagsbits_sf (_update_rflagsbits_af (Mk_rflagsbits 0#32) 1#1) == 1#1) = false ∧
    (_get_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0#32) 1#1) == 1#1) = false := by decide

/-- After the model writes an ALU result's flags (`write_user_rflags` of `aluOut`), `rflags` holds
Janus' new flags (`logicFlags` leaves `AF` undefined: the model draws it from `janus_undef`). -/
theorem flagsRel_aluOut {f0 : Janus.Amd64.Flags} {df : Bool} {r : BitVec 32} (hr : FlagsRel f0 df r)
    (op : Janus.Amd64.AluOp) {w : Nat} (x y : BitVec w) (c : Bool) (u : Nat) :
    FlagsRel (aluRes op x y c).2 df
      (wurf r (aluOut op r (aluRes op x y c).2).1 (aluOut op r (aluRes op x y c).2).2 u) := by
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := mk0_bits
  obtain ⟨a1, a2, a4, a5, a6⟩ := af1_bits
  cases op <;>
  simp only [aluRes, aluOut, isLogic, ↓reduceIte, Bool.false_eq_true, wurf, m1, m2, m3, m4, m5, m6,
    a1, a2, a4, a5, a6, outArith, outLogic] <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [rf_get_cf_upd_cf, rf_get_cf_upd_pf, rf_get_cf_upd_af, rf_get_cf_upd_zf, rf_get_cf_upd_sf, rf_get_cf_upd_of,
    rf_get_pf_upd_cf, rf_get_pf_upd_pf, rf_get_pf_upd_af, rf_get_pf_upd_zf, rf_get_pf_upd_sf, rf_get_pf_upd_of,
    rf_get_af_upd_cf, rf_get_af_upd_pf, rf_get_af_upd_af, rf_get_af_upd_zf, rf_get_af_upd_sf, rf_get_af_upd_of,
    rf_get_zf_upd_cf, rf_get_zf_upd_pf, rf_get_zf_upd_af, rf_get_zf_upd_zf, rf_get_zf_upd_sf, rf_get_zf_upd_of,
    rf_get_sf_upd_cf, rf_get_sf_upd_pf, rf_get_sf_upd_af, rf_get_sf_upd_zf, rf_get_sf_upd_sf, rf_get_sf_upd_of,
    rf_get_of_upd_cf, rf_get_of_upd_pf, rf_get_of_upd_af, rf_get_of_upd_zf, rf_get_of_upd_sf, rf_get_of_upd_of,
    rf_get_df_upd_cf, rf_get_df_upd_pf, rf_get_df_upd_af, rf_get_df_upd_zf, rf_get_df_upd_sf, rf_get_df_upd_of,
    rf_get_ac_upd_cf, rf_get_ac_upd_pf, rf_get_ac_upd_af, rf_get_ac_upd_zf, rf_get_ac_upd_sf, rf_get_ac_upd_of] <;>
  first
    | exact flagEq_fbit _
    | exact hr.df
    | exact hr.ac
    | (simp only [Janus.Amd64.logicFlags]; intro v hv; cases hv)

end JanusX86.Proofs
