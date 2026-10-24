import JanusASL.Proofs.LogicalShifted
import JanusASL.Proofs.Bitmask
import JanusASL.Proofs.MoveWide

/-! # Proved: AND/ORR/EOR/ANDS (immediate), the whole encoding class

Words `sf opc 100100 N immr imms Rn Rd` (bits 28:23 = `100100`) that Janus decodes: `N = 0` when
`sf = 0`, and `DecodeBitMasks(N, imms, immr, TRUE, datasize)` defined (`Bitmask.lean` proves the
two `DecodeBitMasks` equal on all inputs). -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- `execLogicalImm` with the immediate given. -/
def execLogicalImmV (N : Nat) (s : Janus.Arm64.State) (opc : Janus.Arm64.LogicOp) (imm : BitVec N)
    (rn rd : Nat) : Janus.Arm64.State :=
  let r := Janus.Arm64.logicOp opc (s.getX N rn) imm
  match opc with
  | .ands => (s.setX rd r).setFlags (Janus.Arm64.logicFlags r)
  | _ => s.setXSP rd r

set_option maxHeartbeats 4000000 in
theorem run_execute_logical_imm {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d n : Nat} (hd : d < 32) (hn : n < 32)
    (opc : Janus.Arm64.LogicOp) (imm : BitVec N) :
    ∃ s', (execute_aarch64_instrs_integer_logical_immediate d N imm n (aslLogicalOp opc) (opc == .ands)).run s =
        .ok () s' ∧ Rel (execLogicalImmV N js opc imm n d) s' ∧ Frame s s' := by
  obtain ⟨p, hp, hps⟩ := h.pstate
  have hN0 : 0 < N := by omega
  unfold execLogicalImmV
  cases opc
  case ands =>
    simp only [execute_aarch64_instrs_integer_logical_immediate, run_bind, run_undefined_bitvector,
      run_X_read_rel h hn hN, run_pure, aslLogicalOp, Janus.Arm64.logicOp,
      show (Janus.Arm64.LogicOp.ands == Janus.Arm64.LogicOp.ands) = true from rfl, ite_true]
    generalize js.getX N n &&& imm = r
    simp only [run_bind, run_readReg hp, run_writeReg, run_readReg (get?_set_PSTATE _ _), logic_flags_eq hN0,
      nzcv_n, nzcv_z, nzcv_c, nzcv_v, SState.set_set, Bool.not_true, Bool.and_false, Bool.false_eq_true,
      ite_false]
    have hf := h.setFlags hp (Janus.Arm64.logicFlags r)
    obtain ⟨s', hs', hr, hfr⟩ := run_X_set_rel hf hd hN r
    refine ⟨s', hs', ?_, ?_⟩
    · have e : (js.setX d r).setFlags (Janus.Arm64.logicFlags r) =
          (js.setFlags (Janus.Arm64.logicFlags r)).setX d r := by
        simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR, Janus.Arm64.State.setFlags]; split <;> rfl
      rw [e]; exact hr
    · intro x hx h1 h2; rw [hfr x hx h1 h2]; exact get?_set_ne s _ (Ne.symm h2)
  case and =>
    simp only [execute_aarch64_instrs_integer_logical_immediate, run_bind, run_undefined_bitvector,
      run_X_read_rel h hn hN, run_pure, aslLogicalOp, Janus.Arm64.logicOp,
      show (Janus.Arm64.LogicOp.and == .ands) = false from rfl, Bool.false_eq_true, ite_false,
      Bool.not_false, Bool.and_true]
    generalize js.getX N n &&& imm = r
    by_cases hd31 : d = 31
    · subst hd31
      simp only [beq_self_eq_true, ite_true, run_SP_set hp hps.sp]
      refine ⟨_, rfl, ?_, ?_⟩
      · simpa [Janus.Arm64.State.setXSP, Sail.BitVec.zeroExtend] using h.writeSP31 (r.setWidth 64)
      · intro x _ hx _; exact get?_set_ne s _ (Ne.symm hx)
    · have hd' : d < 31 := by omega
      have hdb : ((d : Nat) == 31) = false := by simp; omega
      simp only [hdb, Bool.false_eq_true, ite_false, run_X_set hd' hN]
      refine ⟨_, rfl, ?_, ?_⟩
      · have := h.writeZR hd' (Sail.BitVec.zeroExtend r 64)
        simpa [Janus.Arm64.State.setXSP, Janus.Arm64.State.writeSP, Janus.Arm64.State.writeZR, hd31,
          Sail.BitVec.zeroExtend] using this
      · intro x hx _ _; exact get?_setGpr s _ hd' x hx
  case orr =>
    simp only [execute_aarch64_instrs_integer_logical_immediate, run_bind, run_undefined_bitvector,
      run_X_read_rel h hn hN, run_pure, aslLogicalOp, Janus.Arm64.logicOp,
      show (Janus.Arm64.LogicOp.orr == .ands) = false from rfl, Bool.false_eq_true, ite_false,
      Bool.not_false, Bool.and_true]
    generalize js.getX N n ||| imm = r
    by_cases hd31 : d = 31
    · subst hd31
      simp only [beq_self_eq_true, ite_true, run_SP_set hp hps.sp]
      refine ⟨_, rfl, ?_, ?_⟩
      · simpa [Janus.Arm64.State.setXSP, Sail.BitVec.zeroExtend] using h.writeSP31 (r.setWidth 64)
      · intro x _ hx _; exact get?_set_ne s _ (Ne.symm hx)
    · have hd' : d < 31 := by omega
      have hdb : ((d : Nat) == 31) = false := by simp; omega
      simp only [hdb, Bool.false_eq_true, ite_false, run_X_set hd' hN]
      refine ⟨_, rfl, ?_, ?_⟩
      · have := h.writeZR hd' (Sail.BitVec.zeroExtend r 64)
        simpa [Janus.Arm64.State.setXSP, Janus.Arm64.State.writeSP, Janus.Arm64.State.writeZR, hd31,
          Sail.BitVec.zeroExtend] using this
      · intro x hx _ _; exact get?_setGpr s _ hd' x hx
  case eor =>
    simp only [execute_aarch64_instrs_integer_logical_immediate, run_bind, run_undefined_bitvector,
      run_X_read_rel h hn hN, run_pure, aslLogicalOp, Janus.Arm64.logicOp,
      show (Janus.Arm64.LogicOp.eor == .ands) = false from rfl, Bool.false_eq_true, ite_false,
      Bool.not_false, Bool.and_true]
    generalize js.getX N n ^^^ imm = r
    by_cases hd31 : d = 31
    · subst hd31
      simp only [beq_self_eq_true, ite_true, run_SP_set hp hps.sp]
      refine ⟨_, rfl, ?_, ?_⟩
      · simpa [Janus.Arm64.State.setXSP, Sail.BitVec.zeroExtend] using h.writeSP31 (r.setWidth 64)
      · intro x _ hx _; exact get?_set_ne s _ (Ne.symm hx)
    · have hd' : d < 31 := by omega
      have hdb : ((d : Nat) == 31) = false := by simp; omega
      simp only [hdb, Bool.false_eq_true, ite_false, run_X_set hd' hN]
      refine ⟨_, rfl, ?_, ?_⟩
      · have := h.writeZR hd' (Sail.BitVec.zeroExtend r 64)
        simpa [Janus.Arm64.State.setXSP, Janus.Arm64.State.writeSP, Janus.Arm64.State.writeZR, hd31,
          Sail.BitVec.zeroExtend] using this
      · intro x hx _ _; exact get?_setGpr s _ hd' x hx

theorem width_cases' (sf : BitVec 1) : (if sf == 1#1 then 64 else 32) = 32 ∨ (if sf == 1#1 then 64 else 32) = 64 := by
  split <;> simp

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 40 (`decode_and_log_imm_aarch64_instrs_integer_logical_immediate`). -/
theorem run_DataProcImm_li_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 23) % 64 = 36) (h1 : (w / 2 ^ 29) % 4 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_and_log_imm_aarch64_instrs_integer_logical_immediate (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 6) (fld w 22 1) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 40) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (34#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (98#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (162#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (226#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (582#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t7_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (36#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, t7_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 40) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 43 (`decode_orr_log_imm_aarch64_instrs_integer_logical_immediate`). -/
theorem run_DataProcImm_li_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 23) % 64 = 36) (h1 : (w / 2 ^ 29) % 4 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 6) (fld w 22 1) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 43) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (34#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (98#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (162#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (226#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (582#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (36#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (228#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (164#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t10_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (100#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, t10_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 43) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 42 (`decode_eor_log_imm_aarch64_instrs_integer_logical_immediate`). -/
theorem run_DataProcImm_li_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 23) % 64 = 36) (h1 : (w / 2 ^ 29) % 4 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_eor_log_imm_aarch64_instrs_integer_logical_immediate (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 6) (fld w 22 1) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 42) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (34#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (98#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (162#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (226#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (582#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (36#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (228#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t9_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (164#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, t9_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 42) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 41 (`decode_ands_log_imm_aarch64_instrs_integer_logical_immediate`). -/
theorem run_DataProcImm_li_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 23) % 64 = 36) (h1 : (w / 2 ^ 29) % 4 = 3) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 6) (fld w 22 1) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 41) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (34#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (98#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (162#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (226#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (582#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (36#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t8_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (228#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, t8_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 41) = True from by decide]
  all_goals rfl


theorem run_decode_and_log_imm (Rd Rn : BitVec 5) (imms immr : BitVec 6) (Nb : BitVec 1) (opc : BitVec 2)
    (sf : BitVec 1) (hok : (sf == 0#1 && (Nb != 0#1)) = false) {p : Nat × Nat}
    (hdbm : Janus.Arm64.decodeBitMasks (Nb == 1#1) imms.toNat immr.toNat true (if sf == 1#1 then 64 else 32) = some p)
    (s : SState) :
    (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr Nb opc sf).run s =
      (execute_aarch64_instrs_integer_logical_immediate Rd.toNat (if sf == 1#1 then 64 else 32)
        (BitVec.ofNat _ p.1) Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands)).run s := by
  have hD := run_DBM_janus (a := Nb) (b := imms) (c := immr) (width_cases' sf) hdbm
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_and_log_imm_aarch64_instrs_integer_logical_immediate
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

theorem run_decode_orr_log_imm (Rd Rn : BitVec 5) (imms immr : BitVec 6) (Nb : BitVec 1) (opc : BitVec 2)
    (sf : BitVec 1) (hok : (sf == 0#1 && (Nb != 0#1)) = false) {p : Nat × Nat}
    (hdbm : Janus.Arm64.decodeBitMasks (Nb == 1#1) imms.toNat immr.toNat true (if sf == 1#1 then 64 else 32) = some p)
    (s : SState) :
    (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr Nb opc sf).run s =
      (execute_aarch64_instrs_integer_logical_immediate Rd.toNat (if sf == 1#1 then 64 else 32)
        (BitVec.ofNat _ p.1) Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands)).run s := by
  have hD := run_DBM_janus (a := Nb) (b := imms) (c := immr) (width_cases' sf) hdbm
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_orr_log_imm_aarch64_instrs_integer_logical_immediate
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

theorem run_decode_eor_log_imm (Rd Rn : BitVec 5) (imms immr : BitVec 6) (Nb : BitVec 1) (opc : BitVec 2)
    (sf : BitVec 1) (hok : (sf == 0#1 && (Nb != 0#1)) = false) {p : Nat × Nat}
    (hdbm : Janus.Arm64.decodeBitMasks (Nb == 1#1) imms.toNat immr.toNat true (if sf == 1#1 then 64 else 32) = some p)
    (s : SState) :
    (decode_eor_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr Nb opc sf).run s =
      (execute_aarch64_instrs_integer_logical_immediate Rd.toNat (if sf == 1#1 then 64 else 32)
        (BitVec.ofNat _ p.1) Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands)).run s := by
  have hD := run_DBM_janus (a := Nb) (b := imms) (c := immr) (width_cases' sf) hdbm
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_eor_log_imm_aarch64_instrs_integer_logical_immediate
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

theorem run_decode_ands_log_imm (Rd Rn : BitVec 5) (imms immr : BitVec 6) (Nb : BitVec 1) (opc : BitVec 2)
    (sf : BitVec 1) (hok : (sf == 0#1 && (Nb != 0#1)) = false) {p : Nat × Nat}
    (hdbm : Janus.Arm64.decodeBitMasks (Nb == 1#1) imms.toNat immr.toNat true (if sf == 1#1 then 64 else 32) = some p)
    (s : SState) :
    (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr Nb opc sf).run s =
      (execute_aarch64_instrs_integer_logical_immediate Rd.toNat (if sf == 1#1 then 64 else 32)
        (BitVec.ofNat _ p.1) Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands)).run s := by
  have hD := run_DBM_janus (a := Nb) (b := imms) (c := immr) (width_cases' sf) hdbm
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_ands_log_imm_aarch64_instrs_integer_logical_immediate
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, run_undefined_bitvector, hok, Bool.false_eq_true, ite_false, run_pure, hD]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

theorem decode_logicalImm_class {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100100)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0) {p : Nat × Nat}
    (hd : Janus.Arm64.decodeBitMasks (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 21 16)
      true (if Janus.Arm64.bit w 31 then 64 else 32) = some p) :
    Janus.Arm64.decode w = some (.logicalImm (Janus.Arm64.bit w 31) (Janus.Arm64.LogicOp.ofBits (Janus.Arm64.bits w 30 29))
      (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 21 16) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 9 5)
      (Janus.Arm64.bits w 4 0)) := by
  have h1 : ¬ w ≥ 2 ^ 32 := by omega
  have h2 : Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have h3 : Janus.Arm64.bits w 25 23 = 0b100 := by simp only [bits_def]; omega
  have h5 : (!Janus.Arm64.bit w 31 && Janus.Arm64.bit w 22) = false := by
    simp only [bit_def]; rcases hsf with e | e <;> simp [e]
  simp only [Janus.Arm64.decode, h1, h2, ite_false, ite_true, Janus.Arm64.decodeDPImm, h3, h5, hd]
  simp

theorem logicalImm_spec {N : Nat} (js : Janus.Arm64.State) (opc : Janus.Arm64.LogicOp) (Nbit : Bool)
    (immr imms rn rd : Nat) {p : Nat × Nat} (hd : Janus.Arm64.decodeBitMasks Nbit imms immr true N = some p) :
    Janus.Arm64.execLogicalImm N js opc Nbit immr imms rn rd = execLogicalImmV N js opc (BitVec.ofNat N p.1) rn rd := by
  simp only [Janus.Arm64.execLogicalImm, execLogicalImmV, hd, Option.getD_some]
  rfl

set_option maxHeartbeats 8000000 in
theorem asl_logicalImm {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100100)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0) {p : Nat × Nat}
    (hd : Janus.Arm64.decodeBitMasks (fld w 22 1 == 1#1) (fld w 10 6).toNat (fld w 16 6).toNat
      true (if fld w 31 1 == 1#1 then 64 else 32) = some p)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (execLogicalImmV (if fld w 31 1 == 1#1 then 64 else 32) js
        (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat) (BitVec.ofNat _ p.1) (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      s2.regs.get? .__BranchTaken = some false := by
  rw [run_DecodeA64_DPImm hw (by omega)]
  have hok : (fld w 31 1 == 0#1 && (fld w 22 1 != 0#1)) = false := by
    rcases hsf with e | e
    · rw [fld_eq_of hw (show (w / 2 ^ 31) % 2 ^ 1 = 1 by omega)]; simp
    · rw [fld_eq_of hw (show (w / 2 ^ 22) % 2 ^ 1 = 0 by omega)]; simp
  rcases (show (w / 2 ^ 29) % 4 = 0 ∨ (w / 2 ^ 29) % 4 = 1 ∨ (w / 2 ^ 29) % 4 = 2 ∨ (w / 2 ^ 29) % 4 = 3 by omega)
    with hk | hk | hk | hk
  · rw [run_DataProcImm_li_0 hw hc hk (see_entry _ _), run_decode_and_log_imm _ _ _ _ _ _ _ hok hd]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_imm (h.entry (BitVec.ofNat 32 w) 40) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat) _
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcImm_li_1 hw hc hk (see_entry _ _), run_decode_orr_log_imm _ _ _ _ _ _ _ hok hd]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_imm (h.entry (BitVec.ofNat 32 w) 43) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat) _
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcImm_li_2 hw hc hk (see_entry _ _), run_decode_eor_log_imm _ _ _ _ _ _ _ hok hd]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_imm (h.entry (BitVec.ofNat 32 w) 42) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat) _
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcImm_li_3 hw hc hk (see_entry _ _), run_decode_ands_log_imm _ _ _ _ _ _ _ hok hd]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_imm (h.entry (BitVec.ofNat 32 w) 41) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat) _
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩

/-- **AND/ORR/EOR/ANDS (immediate)**: for every word of the encoding class that Janus decodes
(`N = 0` if `sf = 0`, and `DecodeBitMasks` defined) and every related pair of states, Janus'
`step` and the generated ASL agree. -/
theorem logicalImm_agree {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100100)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0)
    (hdbm : (Janus.Arm64.decodeBitMasks (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 21 16)
      true (if Janus.Arm64.bit w 31 then 64 else 32)).isSome = true)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hdbm
  have hp' : Janus.Arm64.decodeBitMasks (fld w 22 1 == 1#1) (fld w 10 6).toNat (fld w 16 6).toNat
      true (if fld w 31 1 == 1#1 then 64 else 32) = some p := by
    rw [fld_bit w 22 hw, fld_bit w 31 hw, ← bits_eq_fld w 15 10 hw, ← bits_eq_fld w 21 16 hw]; exact hp
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_logicalImm hw hc hsf hp' h (js.pc.toNat : Int)
  have hpc : ∀ N opc (imm : BitVec N) rn rd, (execLogicalImmV N js opc imm rn rd).pc = js.pc := by
    intro N opc imm rn rd
    cases opc <;> simp [execLogicalImmV, Janus.Arm64.State.setX, Janus.Arm64.State.setXSP,
      Janus.Arm64.State.writeZR, Janus.Arm64.State.writeSP, Janus.Arm64.State.setFlags] <;> split <;> rfl
  rcases fld_sf_cases hw with ⟨e1, _⟩ | ⟨e1, _⟩
  · rw [e1] at hrel
    have hrel' : Rel (execLogicalImmV 64 js (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat)
        (BitVec.ofNat 64 p.1) (fld w 5 5).toNat (fld w 0 5).toNat) s2 := hrel
    refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (hpc _ _ _ _ _) ?_
    have hb : Janus.Arm64.bit w 31 = true := by rw [← fld_bit w 31 hw, e1]; rfl
    rw [Janus.Arm64.step_of_decode (decode_logicalImm_class hw hc hsf hp)]
    simp only [hb, ite_true, ite_false, Bool.false_eq_true] at hp
    simp only [Janus.Arm64.exec, hb, ite_true, ite_false, Bool.false_eq_true]
    rw [logicalImm_spec js _ _ _ _ _ _ hp]
    simp only [bits_eq_fld w 30 29 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
    simp [Janus.Arm64.State.next, hpc]
  · rw [e1] at hrel
    have hrel' : Rel (execLogicalImmV 32 js (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat)
        (BitVec.ofNat 32 p.1) (fld w 5 5).toNat (fld w 0 5).toNat) s2 := hrel
    refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (hpc _ _ _ _ _) ?_
    have hb : Janus.Arm64.bit w 31 = false := by rw [← fld_bit w 31 hw, e1]; rfl
    rw [Janus.Arm64.step_of_decode (decode_logicalImm_class hw hc hsf hp)]
    simp only [hb, ite_true, ite_false, Bool.false_eq_true] at hp
    simp only [Janus.Arm64.exec, hb, ite_true, ite_false, Bool.false_eq_true]
    rw [logicalImm_spec js _ _ _ _ _ _ hp]
    simp only [bits_eq_fld w 30 29 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
    simp [Janus.Arm64.State.next, hpc]

end JanusASL.Proofs
