import JanusASL.Proofs.Step
import JanusASL.Proofs.AddSubImm
import JanusASL.Proofs.Shift

/-! # Proved: ADD/ADDS/SUB/SUBS (shifted register), the whole encoding class

Words `sf op S 01011 shift 0 Rm imm6 Rn Rd` (bits 28:24 = `01011`, bit 21 = 0) with
`shift ≠ 11` and (`sf = 1` or `imm6 < 32`): all words Janus decodes in this class; for the others
both reject (Janus `none`, ASL UNDEFINED). -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_DecodeShift (sh : BitVec 2) (s : SState) :
    (DecodeShift sh).run s = .ok (aslShiftType (Janus.Arm64.ShiftType.ofBits sh.toNat)) s := by
  have e : sh = BitVec.ofNat 2 sh.toNat := by simp
  have hl := sh.isLt
  rw [e]; generalize sh.toNat = c at hl
  match c, hl with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | _ + 4, hl => exact absurd hl (by omega)

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 14 (`decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg`). -/
theorem run_DataProcReg_shifted_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 11) (h1 : (w / 2 ^ 21) % 2 = 0) (h2 : (w / 2 ^ 29) % 4 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 22 2) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 14) := by
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
  have t5_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t5_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, t5_0, t5_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 14) = True from by decide]
  all_goals rfl

theorem run_decode_add_addsub_shift (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (shift : BitVec 2) (S op sf : BitVec 1)
    (hsh : shift ≠ 3#2) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32)
        Rm.toNat Rn.toNat (S == 1#1) imm6.toNat (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))
        (op == 1#1)).run s := by
  have h1 : (shift == 3#2) = false := by simpa using hsh
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
  unfold decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  simp only [run_bind, h1, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 15 (`decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg`). -/
theorem run_DataProcReg_shifted_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 11) (h1 : (w / 2 ^ 21) % 2 = 0) (h2 : (w / 2 ^ 29) % 4 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 22 2) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 15) := by
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
  have t6_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t6_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, t6_0, t6_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 15) = True from by decide]
  all_goals rfl

theorem run_decode_adds_addsub_shift (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (shift : BitVec 2) (S op sf : BitVec 1)
    (hsh : shift ≠ 3#2) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32)
        Rm.toNat Rn.toNat (S == 1#1) imm6.toNat (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))
        (op == 1#1)).run s := by
  have h1 : (shift == 3#2) = false := by simpa using hsh
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
  unfold decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  simp only [run_bind, h1, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 16 (`decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg`). -/
theorem run_DataProcReg_shifted_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 11) (h1 : (w / 2 ^ 21) % 2 = 0) (h2 : (w / 2 ^ 29) % 4 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 22 2) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 16) := by
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
  have t7_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t7_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, t7_0, t7_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 16) = True from by decide]
  all_goals rfl

theorem run_decode_sub_addsub_shift (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (shift : BitVec 2) (S op sf : BitVec 1)
    (hsh : shift ≠ 3#2) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32)
        Rm.toNat Rn.toNat (S == 1#1) imm6.toNat (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))
        (op == 1#1)).run s := by
  have h1 : (shift == 3#2) = false := by simpa using hsh
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
  unfold decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  simp only [run_bind, h1, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 17 (`decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg`). -/
theorem run_DataProcReg_shifted_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 11) (h1 : (w / 2 ^ 21) % 2 = 0) (h2 : (w / 2 ^ 29) % 4 = 3) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 22 2) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 17) := by
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
  have t8_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t8_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, t8_0, t8_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 17) = True from by decide]
  all_goals rfl

theorem run_decode_subs_addsub_shift (Rd Rn : BitVec 5) (imm6 : BitVec 6) (Rm : BitVec 5) (shift : BitVec 2) (S op sf : BitVec 1)
    (hsh : shift ≠ 3#2) (him : sf = 1#1 ∨ imm6.toNat < 32) (s : SState) :
    (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd.toNat (if sf == 1#1 then 64 else 32)
        Rm.toNat Rn.toNat (S == 1#1) imm6.toNat (aslShiftType (Janus.Arm64.ShiftType.ofBits shift.toNat))
        (op == 1#1)).run s := by
  have h1 : (shift == 3#2) = false := by simpa using hsh
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
  unfold decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
  simp only [run_bind, h1, h2, Bool.false_eq_true, ite_false, run_pure, run_DecodeShift]

set_option maxHeartbeats 4000000 in
theorem run_execute_addsub_shifted {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d m n : Nat} (hd : d < 32) (hm : m < 32) (hn : n < 32) (S sub : Bool)
    (t : Janus.Arm64.ShiftType) {k : Nat} (hk : k < N) :
    ∃ s', (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg d N m n S k (aslShiftType t) sub).run s =
        .ok () s' ∧ Rel (Janus.Arm64.execAddSubShifted N js sub S t m k n d) s' ∧ Frame s s' := by
  obtain ⟨p, hp, hps⟩ := h.pstate
  have hN0 : 0 < N := by omega
  simp only [execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg, run_bind, run_undefined_bitvector,
    run_X_read_rel h hn hN, run_ShiftReg h hm hN t hk, run_pure, pair_ofBool, AddWithCarry_eq hN0, ← addSub_eq]
  unfold Janus.Arm64.execAddSubShifted
  dsimp only
  generalize Janus.Arm64.addSub (js.getX N n) (Janus.Arm64.shiftReg (js.getX N m) t k) sub = r
  cases S
  · simp only [Bool.false_eq_true, ite_false, run_pure]
    exact run_X_set_rel h hd hN r.1
  · simp only [ite_true, run_bind, run_readReg hp, run_writeReg, run_readReg (get?_set_PSTATE _ _),
      nzcv_n, nzcv_z, nzcv_c, nzcv_v, SState.set_set]
    have hf := h.setFlags hp r.2
    obtain ⟨s', hs', hr, hfr⟩ := run_X_set_rel hf hd hN r.1
    refine ⟨s', hs', ?_, ?_⟩
    · have e : (js.setX d r.1).setFlags r.2 = (js.setFlags r.2).setX d r.1 := by
        simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR, Janus.Arm64.State.setFlags]; split <;> rfl
      rw [e]; exact hr
    · intro x hx h1 h2; rw [hfr x hx h1 h2]; exact get?_set_ne s _ (Ne.symm h2)

theorem fld_sf_cases {w : Nat} (hw : w < 2 ^ 32) :
    (fld w 31 1 = 1#1 ∧ (w / 2 ^ 31) % 2 = 1) ∨ (fld w 31 1 = 0#1 ∧ (w / 2 ^ 31) % 2 = 0) := by
  rcases (show (w / 2 ^ 31) % 2 = 0 ∨ (w / 2 ^ 31) % 2 = 1 by omega) with e | e
  · exact Or.inr ⟨BitVec.eq_of_toNat_eq (by rw [fld_toNat w 31 1 hw, e]; rfl), e⟩
  · exact Or.inl ⟨BitVec.eq_of_toNat_eq (by rw [fld_toNat w 31 1 hw, e]; rfl), e⟩

set_option maxHeartbeats 8000000 in
theorem asl_addsub_shifted {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 24) % 32 = 0b01011)
    (h2 : (w / 2 ^ 21) % 2 = 0) (h3 : (w / 2 ^ 22) % 4 ≠ 3)
    (h4 : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execAddSubShifted (if fld w 31 1 == 1#1 then 64 else 32) js (fld w 30 1 == 1#1)
        (fld w 29 1 == 1#1) (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) (fld w 16 5).toNat
        (fld w 10 6).toNat (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      s2.regs.get? .__BranchTaken = some false := by
  rw [run_DecodeA64_DPReg hw (by omega)]
  have hsh : fld w 22 2 ≠ 3#2 := by
    intro e; have := congrArg BitVec.toNat e; rw [fld_toNat w 22 2 hw] at this; simp at this; omega
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
    with hk | hk | hk | hk
  · rw [run_DataProcReg_shifted_0 hw h1 h2 hk (see_entry _ _), run_decode_add_addsub_shift _ _ _ _ _ _ _ _ hsh him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_shifted (h.entry (BitVec.ofNat 32 w) 14) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_shifted_1 hw h1 h2 hk (see_entry _ _), run_decode_adds_addsub_shift _ _ _ _ _ _ _ _ hsh him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_shifted (h.entry (BitVec.ofNat 32 w) 15) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_shifted_2 hw h1 h2 hk (see_entry _ _), run_decode_sub_addsub_shift _ _ _ _ _ _ _ _ hsh him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_shifted (h.entry (BitVec.ofNat 32 w) 16) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_shifted_3 hw h1 h2 hk (see_entry _ _), run_decode_subs_addsub_shift _ _ _ _ _ _ _ _ hsh him]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_shifted (h.entry (BitVec.ofNat 32 w) 17) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
      (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) hamt
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩

/-- **ADD/ADDS/SUB/SUBS (shifted register)**: for every word Janus decodes in this class and every
related pair of states, Janus' `step` and the generated ASL agree. -/
theorem addSubShifted_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 24) % 32 = 0b01011)
    (h2 : (w / 2 ^ 21) % 2 = 0) (h3 : (w / 2 ^ 22) % 4 ≠ 3)
    (h4 : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' := by
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execAddSubShifted N js (fld w 30 1 == 1#1)
    (fld w 29 1 == 1#1) (Janus.Arm64.ShiftType.ofBits (fld w 22 2).toNat) (fld w 16 5).toNat
    (fld w 10 6).toNat (fld w 5 5).toNat (fld w 0 5).toNat
  have hspec : ∀ N, (F N).pc = js.pc := by
    intro N; simp only [F, Janus.Arm64.execAddSubShifted]
    split <;> simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR, Janus.Arm64.State.setFlags] <;> split <;> rfl
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_addsub_shifted hw h1 h2 h3 h4 h (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_addSubShifted_class hw h1 h2 h3 h4)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, ← fld_bit w 30 hw, ← fld_bit w 29 hw,
    bits_eq_fld w 23 22 hw, bits_eq_fld w 20 16 hw, bits_eq_fld w 15 10 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, F]

end JanusASL.Proofs
