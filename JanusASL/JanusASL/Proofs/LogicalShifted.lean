import JanusASL.Proofs.Step
import JanusASL.Proofs.AddSubImm
import JanusASL.Proofs.AddSubShifted

/-! # Proved: AND/BIC/ORR/ORN/EOR/EON/ANDS/BICS (shifted register), the whole encoding class

Words `sf opc 01010 shift N Rm imm6 Rn Rd` (bits 28:24 = `01010`) with `sf = 1` or `imm6 < 32`:
all words Janus decodes in this class. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

def aslLogicalOp : Janus.Arm64.LogicOp → ArmASL.LogicalOp
  | .and => .LogicalOp_AND
  | .orr => .LogicalOp_ORR
  | .eor => .LogicalOp_EOR
  | .ands => .LogicalOp_AND

theorem logic_flags_eq {N : Nat} (hN : 0 < N) (r : BitVec N) :
    ((Sail.BitVec.access r ((N : Int) - 1).toNat : BitVec 1) +++ IsZeroBit r) +++ 0b00#2 =
      nzcvBits (Janus.Arm64.logicFlags r) := by
  have hm : (Sail.BitVec.access r ((N : Int) - 1).toNat) = BitVec.ofBool r.msb := by
    simp only [Sail.BitVec.access, BitVec.msb_eq_getLsbD_last]
    rw [show ((N : Int) - 1).toNat = N - 1 by omega, BitVec.getLsbD_eq_getElem (by omega)]
    simp [getElem!_pos, show N - 1 < N by omega]
  have hz : IsZeroBit r = BitVec.ofBool (decide (r = 0)) := by
    unfold IsZeroBit IsZero
    by_cases e : r = 0#N <;> simp [e, Sail.BitVec.length]
  rw [hm, hz]
  unfold nzcvBits Janus.Arm64.logicFlags
  cases r.msb <;> cases decide (r = 0) <;> rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 48 (`decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg`). -/
theorem run_DataProcReg_logical_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 10) (h1 : (w / 2 ^ 29) % 4 = 0) (h2 : (w / 2 ^ 21) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 21 1) (fld w 22 2) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 48) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t13_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t13_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, t13_0, t13_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 48) = True from by decide]
  all_goals rfl

theorem run_decode_and_log_shift_logical (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (Nb : BitVec 1) (shift opc : BitVec 2)
    (sf : BitVec 1) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm Nb shift opc sf).run s =
      (execute_aarch64_instrs_integer_logical_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32) (Nb == 1#1)
        Rm.toNat Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands) imm6.toNat
        (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))).run s := by
  have h2 : ((sf == 0#1) && ((Sail.BitVec.access imm6 5 : BitVec 1) == 1#1)) = false := by
    rcases him with e | e
    · subst e; rfl
    · have : (Sail.BitVec.access imm6 5 : BitVec 1) = 0#1 := by
        simp only [Sail.BitVec.access]
        have : imm6[5]! = false := by
          rw [show imm6[5]! = imm6.getLsbD 5 by simp [BitVec.getLsbD_eq_getElem]]
          simp [BitVec.getLsbD, Nat.testBit]; omega
        rw [this]; rfl
      rw [this]; simp
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 50 (`decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg`). -/
theorem run_DataProcReg_logical_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 10) (h1 : (w / 2 ^ 29) % 4 = 0) (h2 : (w / 2 ^ 21) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 21 1) (fld w 22 2) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 50) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t15_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t15_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, t15_0, t15_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 50) = True from by decide]
  all_goals rfl

theorem run_decode_bic_log_shift_logical (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (Nb : BitVec 1) (shift opc : BitVec 2)
    (sf : BitVec 1) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm Nb shift opc sf).run s =
      (execute_aarch64_instrs_integer_logical_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32) (Nb == 1#1)
        Rm.toNat Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands) imm6.toNat
        (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))).run s := by
  have h2 : ((sf == 0#1) && ((Sail.BitVec.access imm6 5 : BitVec 1) == 1#1)) = false := by
    rcases him with e | e
    · subst e; rfl
    · have : (Sail.BitVec.access imm6 5 : BitVec 1) = 0#1 := by
        simp only [Sail.BitVec.access]
        have : imm6[5]! = false := by
          rw [show imm6[5]! = imm6.getLsbD 5 by simp [BitVec.getLsbD_eq_getElem]]
          simp [BitVec.getLsbD, Nat.testBit]; omega
        rw [this]; rfl
      rw [this]; simp
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 55 (`decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg`). -/
theorem run_DataProcReg_logical_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 10) (h1 : (w / 2 ^ 29) % 4 = 1) (h2 : (w / 2 ^ 21) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 21 1) (fld w 22 2) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 55) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t20_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t20_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, t20_0, t20_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 55) = True from by decide]
  all_goals rfl

theorem run_decode_orr_log_shift_logical (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (Nb : BitVec 1) (shift opc : BitVec 2)
    (sf : BitVec 1) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm Nb shift opc sf).run s =
      (execute_aarch64_instrs_integer_logical_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32) (Nb == 1#1)
        Rm.toNat Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands) imm6.toNat
        (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))).run s := by
  have h2 : ((sf == 0#1) && ((Sail.BitVec.access imm6 5 : BitVec 1) == 1#1)) = false := by
    rcases him with e | e
    · subst e; rfl
    · have : (Sail.BitVec.access imm6 5 : BitVec 1) = 0#1 := by
        simp only [Sail.BitVec.access]
        have : imm6[5]! = false := by
          rw [show imm6[5]! = imm6.getLsbD 5 by simp [BitVec.getLsbD_eq_getElem]]
          simp [BitVec.getLsbD, Nat.testBit]; omega
        rw [this]; rfl
      rw [this]; simp
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 54 (`decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg`). -/
theorem run_DataProcReg_logical_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 10) (h1 : (w / 2 ^ 29) % 4 = 1) (h2 : (w / 2 ^ 21) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 21 1) (fld w 22 2) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 54) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t19_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t19_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, t19_0, t19_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 54) = True from by decide]
  all_goals rfl

theorem run_decode_orn_log_shift_logical (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (Nb : BitVec 1) (shift opc : BitVec 2)
    (sf : BitVec 1) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm Nb shift opc sf).run s =
      (execute_aarch64_instrs_integer_logical_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32) (Nb == 1#1)
        Rm.toNat Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands) imm6.toNat
        (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))).run s := by
  have h2 : ((sf == 0#1) && ((Sail.BitVec.access imm6 5 : BitVec 1) == 1#1)) = false := by
    rcases him with e | e
    · subst e; rfl
    · have : (Sail.BitVec.access imm6 5 : BitVec 1) = 0#1 := by
        simp only [Sail.BitVec.access]
        have : imm6[5]! = false := by
          rw [show imm6[5]! = imm6.getLsbD 5 by simp [BitVec.getLsbD_eq_getElem]]
          simp [BitVec.getLsbD, Nat.testBit]; omega
        rw [this]; rfl
      rw [this]; simp
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 53 (`decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg`). -/
theorem run_DataProcReg_logical_4 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 10) (h1 : (w / 2 ^ 29) % 4 = 2) (h2 : (w / 2 ^ 21) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 21 1) (fld w 22 2) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 53) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t18_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t18_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, t18_0, t18_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 53) = True from by decide]
  all_goals rfl

theorem run_decode_eor_log_shift_logical (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (Nb : BitVec 1) (shift opc : BitVec 2)
    (sf : BitVec 1) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm Nb shift opc sf).run s =
      (execute_aarch64_instrs_integer_logical_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32) (Nb == 1#1)
        Rm.toNat Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands) imm6.toNat
        (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))).run s := by
  have h2 : ((sf == 0#1) && ((Sail.BitVec.access imm6 5 : BitVec 1) == 1#1)) = false := by
    rcases him with e | e
    · subst e; rfl
    · have : (Sail.BitVec.access imm6 5 : BitVec 1) = 0#1 := by
        simp only [Sail.BitVec.access]
        have : imm6[5]! = false := by
          rw [show imm6[5]! = imm6.getLsbD 5 by simp [BitVec.getLsbD_eq_getElem]]
          simp [BitVec.getLsbD, Nat.testBit]; omega
        rw [this]; rfl
      rw [this]; simp
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 52 (`decode_eon_aarch64_instrs_integer_logical_shiftedreg`). -/
theorem run_DataProcReg_logical_5 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 10) (h1 : (w / 2 ^ 29) % 4 = 2) (h2 : (w / 2 ^ 21) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_eon_aarch64_instrs_integer_logical_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 21 1) (fld w 22 2) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 52) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t17_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t17_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, t17_0, t17_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 52) = True from by decide]
  all_goals rfl

theorem run_decode_eon_logical (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (Nb : BitVec 1) (shift opc : BitVec 2)
    (sf : BitVec 1) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_eon_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm Nb shift opc sf).run s =
      (execute_aarch64_instrs_integer_logical_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32) (Nb == 1#1)
        Rm.toNat Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands) imm6.toNat
        (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))).run s := by
  have h2 : ((sf == 0#1) && ((Sail.BitVec.access imm6 5 : BitVec 1) == 1#1)) = false := by
    rcases him with e | e
    · subst e; rfl
    · have : (Sail.BitVec.access imm6 5 : BitVec 1) = 0#1 := by
        simp only [Sail.BitVec.access]
        have : imm6[5]! = false := by
          rw [show imm6[5]! = imm6.getLsbD 5 by simp [BitVec.getLsbD_eq_getElem]]
          simp [BitVec.getLsbD, Nat.testBit]; omega
        rw [this]; rfl
      rw [this]; simp
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_eon_aarch64_instrs_integer_logical_shiftedreg
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 49 (`decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg`). -/
theorem run_DataProcReg_logical_6 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 10) (h1 : (w / 2 ^ 29) % 4 = 3) (h2 : (w / 2 ^ 21) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 21 1) (fld w 22 2) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 49) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t14_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t14_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, t14_0, t14_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 49) = True from by decide]
  all_goals rfl

theorem run_decode_ands_log_shift_logical (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (Nb : BitVec 1) (shift opc : BitVec 2)
    (sf : BitVec 1) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm Nb shift opc sf).run s =
      (execute_aarch64_instrs_integer_logical_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32) (Nb == 1#1)
        Rm.toNat Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands) imm6.toNat
        (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))).run s := by
  have h2 : ((sf == 0#1) && ((Sail.BitVec.access imm6 5 : BitVec 1) == 1#1)) = false := by
    rcases him with e | e
    · subst e; rfl
    · have : (Sail.BitVec.access imm6 5 : BitVec 1) = 0#1 := by
        simp only [Sail.BitVec.access]
        have : imm6[5]! = false := by
          rw [show imm6[5]! = imm6.getLsbD 5 by simp [BitVec.getLsbD_eq_getElem]]
          simp [BitVec.getLsbD, Nat.testBit]; omega
        rw [this]; rfl
      rw [this]; simp
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 51 (`decode_bics_aarch64_instrs_integer_logical_shiftedreg`). -/
theorem run_DataProcReg_logical_7 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 10) (h1 : (w / 2 ^ 29) % 4 = 3) (h2 : (w / 2 ^ 21) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_bics_aarch64_instrs_integer_logical_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 21 1) (fld w 22 2) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 51) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t16_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t16_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, t16_0, t16_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 51) = True from by decide]
  all_goals rfl

theorem run_decode_bics_logical (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (Nb : BitVec 1) (shift opc : BitVec 2)
    (sf : BitVec 1) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_bics_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm Nb shift opc sf).run s =
      (execute_aarch64_instrs_integer_logical_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32) (Nb == 1#1)
        Rm.toNat Rn.toNat (aslLogicalOp (Janus.Arm64.LogicOp.ofBits opc.toNat))
        (Janus.Arm64.LogicOp.ofBits opc.toNat == .ands) imm6.toNat
        (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))).run s := by
  have h2 : ((sf == 0#1) && ((Sail.BitVec.access imm6 5 : BitVec 1) == 1#1)) = false := by
    rcases him with e | e
    · subst e; rfl
    · have : (Sail.BitVec.access imm6 5 : BitVec 1) = 0#1 := by
        simp only [Sail.BitVec.access]
        have : imm6[5]! = false := by
          rw [show imm6[5]! = imm6.getLsbD 5 by simp [BitVec.getLsbD_eq_getElem]]
          simp [BitVec.getLsbD, Nat.testBit]; omega
        rw [this]; rfl
      rw [this]; simp
  have e : opc = BitVec.ofNat 2 opc.toNat := by simp
  have hl := opc.isLt
  unfold decode_bics_aarch64_instrs_integer_logical_shiftedreg
  rw [e]; generalize opc.toNat = c at hl
  match c, hl with
  | 0, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 1, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 2, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | 3, _ => simp only [run_bind, run_undefined_bool, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]; rfl
  | _ + 4, hl => exact absurd hl (by omega)

theorem logic_eq {N : Nat} (opc : Janus.Arm64.LogicOp) (x y : BitVec N) :
    (match aslLogicalOp opc with
      | .LogicalOp_AND => x &&& y
      | .LogicalOp_ORR => x ||| y
      | .LogicalOp_EOR => x ^^^ y) = Janus.Arm64.logicOp opc x y := by
  cases opc <;> rfl

set_option maxHeartbeats 4000000 in
theorem run_execute_logical_shifted {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d m n : Nat} (hd : d < 32) (hm : m < 32) (hn : n < 32)
    (opc : Janus.Arm64.LogicOp) (t : Janus.Arm64.ShiftType) {k : Nat} (hk : k < N) (inv : Bool) :
    ∃ s', (execute_aarch64_instrs_integer_logical_shiftedreg d N inv m n (aslLogicalOp opc) (opc == .ands) k
        (aslShiftType t)).run s = .ok () s' ∧
      Rel (Janus.Arm64.execLogicalShifted N js opc t inv m k n d) s' ∧ Frame s s' := by
  obtain ⟨p, hp, hps⟩ := h.pstate
  have hN0 : 0 < N := by omega
  unfold Janus.Arm64.execLogicalShifted
  cases opc
  case ands =>
    simp only [execute_aarch64_instrs_integer_logical_shiftedreg, run_bind, run_undefined_bitvector,
      run_X_read_rel h hn hN, run_ShiftReg h hm hN t hk, run_pure, aslLogicalOp, Janus.Arm64.logicOp,
      show (Janus.Arm64.LogicOp.ands == Janus.Arm64.LogicOp.ands) = true from rfl, ite_true]
    generalize js.getX N n &&&
      (if inv = true then ~~~Janus.Arm64.shiftReg (js.getX N m) t k else Janus.Arm64.shiftReg (js.getX N m) t k) = r
    simp only [run_bind, run_readReg hp, run_writeReg, run_readReg (get?_set_PSTATE _ _), logic_flags_eq hN0,
      nzcv_n, nzcv_z, nzcv_c, nzcv_v, SState.set_set]
    have hf := h.setFlags hp (Janus.Arm64.logicFlags r)
    obtain ⟨s', hs', hr, hfr⟩ := run_X_set_rel hf hd hN r
    refine ⟨s', hs', ?_, ?_⟩
    · have e : (js.setX d r).setFlags (Janus.Arm64.logicFlags r) =
          (js.setFlags (Janus.Arm64.logicFlags r)).setX d r := by
        simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR, Janus.Arm64.State.setFlags]; split <;> rfl
      rw [e]; exact hr
    · intro x hx h1 h2; rw [hfr x hx h1 h2]; exact get?_set_ne s _ (Ne.symm h2)
  all_goals
    simp only [execute_aarch64_instrs_integer_logical_shiftedreg, run_bind, run_undefined_bitvector,
      run_X_read_rel h hn hN, run_ShiftReg h hm hN t hk, run_pure, aslLogicalOp, Janus.Arm64.logicOp,
      show (Janus.Arm64.LogicOp.and == .ands) = false from rfl,
      show (Janus.Arm64.LogicOp.orr == .ands) = false from rfl,
      show (Janus.Arm64.LogicOp.eor == .ands) = false from rfl, Bool.false_eq_true, ite_false]
    exact run_X_set_rel h hd hN _

set_option maxHeartbeats 8000000 in
theorem asl_logical_shifted {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 24) % 32 = 0b01010)
    (h4 : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execLogicalShifted (if fld w 31 1 == 1#1 then 64 else 32) js
        (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat) (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat)
        (fld w 21 1 == 1#1) (fld w 16 5).toNat (fld w 10 6).toNat (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      s2.regs.get? .__BranchTaken = some false := by
  rw [run_DecodeA64_DPReg hw (by omega)]
  have him : fld w 31 1 = 1#1 ∨ (fld w 10 6).toNat < 32 := by
    rcases fld_sf_cases hw with ⟨e, _⟩ | ⟨_, e⟩
    · exact Or.inl e
    · right; rw [fld_toNat w 10 6 hw]; omega
  have hamt : (fld w 10 6).toNat < (if fld w 31 1 == 1#1 then 64 else 32) := by
    rw [fld_toNat w 10 6 hw]
    rcases fld_sf_cases hw with ⟨e, _⟩ | ⟨e, e'⟩
    · rw [e]; simp; omega
    · rw [e]; simp; omega
  rcases (show (w / 2 ^ 29) % 4 = 0 ∨ (w / 2 ^ 29) % 4 = 1 ∨ (w / 2 ^ 29) % 4 = 2 ∨ (w / 2 ^ 29) % 4 = 3 by omega)
    with hk1 | hk1 | hk1 | hk1 <;>
  rcases (show (w / 2 ^ 21) % 2 = 0 ∨ (w / 2 ^ 21) % 2 = 1 by omega) with hk2 | hk2
  · rw [run_DataProcReg_logical_0 hw h1 hk1 hk2 (see_entry _ _), run_decode_and_log_shift_logical _ _ _ _ _ _ _ _ him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_shifted (h.entry (BitVec.ofNat 32 w) 48) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt (fld w 21 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_logical_1 hw h1 hk1 hk2 (see_entry _ _), run_decode_bic_log_shift_logical _ _ _ _ _ _ _ _ him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_shifted (h.entry (BitVec.ofNat 32 w) 50) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt (fld w 21 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_logical_2 hw h1 hk1 hk2 (see_entry _ _), run_decode_orr_log_shift_logical _ _ _ _ _ _ _ _ him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_shifted (h.entry (BitVec.ofNat 32 w) 55) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt (fld w 21 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_logical_3 hw h1 hk1 hk2 (see_entry _ _), run_decode_orn_log_shift_logical _ _ _ _ _ _ _ _ him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_shifted (h.entry (BitVec.ofNat 32 w) 54) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt (fld w 21 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_logical_4 hw h1 hk1 hk2 (see_entry _ _), run_decode_eor_log_shift_logical _ _ _ _ _ _ _ _ him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_shifted (h.entry (BitVec.ofNat 32 w) 53) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt (fld w 21 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_logical_5 hw h1 hk1 hk2 (see_entry _ _), run_decode_eon_logical _ _ _ _ _ _ _ _ him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_shifted (h.entry (BitVec.ofNat 32 w) 52) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt (fld w 21 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_logical_6 hw h1 hk1 hk2 (see_entry _ _), run_decode_ands_log_shift_logical _ _ _ _ _ _ _ _ him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_shifted (h.entry (BitVec.ofNat 32 w) 49) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt (fld w 21 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_logical_7 hw h1 hk1 hk2 (see_entry _ _), run_decode_bics_logical _ _ _ _ _ _ _ _ him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_logical_shifted (h.entry (BitVec.ofNat 32 w) 51) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt (fld w 21 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩

/-- **AND/BIC/ORR/ORN/EOR/EON/ANDS/BICS (shifted register)**: for every word Janus decodes in this
class and every related pair of states, Janus' `step` and the generated ASL agree. -/
theorem logicalShifted_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 24) % 32 = 0b01010)
    (h4 : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' := by
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execLogicalShifted N js
    (Janus.Arm64.LogicOp.ofBits (fld w 29 2).toNat) (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat)
    (fld w 21 1 == 1#1) (fld w 16 5).toNat (fld w 10 6).toNat (fld w 5 5).toNat (fld w 0 5).toNat
  have hspec : ∀ N, (F N).pc = js.pc := by
    intro N; simp only [F, Janus.Arm64.execLogicalShifted]
    split <;> simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR, Janus.Arm64.State.setFlags] <;> split <;> rfl
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_logical_shifted hw h1 h4 h (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_logicalShifted_class hw h1 h4)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, ← fld_bit w 21 hw, bits_eq_fld w 30 29 hw,
    bits_eq_fld w 23 22 hw, bits_eq_fld w 20 16 hw, bits_eq_fld w 15 10 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, F]

end JanusASL.Proofs
