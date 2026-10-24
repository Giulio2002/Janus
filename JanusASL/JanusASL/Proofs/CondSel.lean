import JanusASL.Proofs.Step
import JanusASL.Proofs.AddSubImm
import JanusASL.Proofs.Cond

/-! # Proved: CSEL/CSINC/CSINV/CSNEG, the whole encoding class

Words `sf op 0 11010100 Rm cond 0 o2 Rn Rd` (bits 29:21 = `011010100`, bit 11 = 0; 2^22 words).
Assumes statistical profiling is not sampling (`SPESampleInFlight = false`, its reset value). -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 187 (`decode_csel_aarch64_instrs_integer_conditional_select`). -/
theorem run_DataProcReg_condsel_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 512 = 212) (h1 : (w / 2 ^ 11) % 2 = 0) (h2 : (w / 2 ^ 30) % 2 = 0) (h3 : (w / 2 ^ 10) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_csel_aarch64_instrs_integer_conditional_select (fld w 0 5) (fld w 5 5) (fld w 10 1) (fld w 12 4) (fld w 16 5) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 187) := by
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
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486852#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486855#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t38_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t38_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (0#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, t38_0, t38_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 187) = True from by decide]
  all_goals rfl

theorem run_decode_csel_condsel (Rd Rn : BitVec 5) (o2 : BitVec 1) (cond : BitVec 4) (Rm : BitVec 5) (op sf : BitVec 1)
    (s : SState) :
    (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf).run s =
      (execute_aarch64_instrs_integer_conditional_select cond Rd.toNat (if sf == 1#1 then 64 else 32)
        (o2 == 1#1) (op == 1#1) Rm.toNat Rn.toNat).run s := by
  unfold decode_csel_aarch64_instrs_integer_conditional_select
  rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 188 (`decode_csinc_aarch64_instrs_integer_conditional_select`). -/
theorem run_DataProcReg_condsel_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 512 = 212) (h1 : (w / 2 ^ 11) % 2 = 0) (h2 : (w / 2 ^ 30) % 2 = 0) (h3 : (w / 2 ^ 10) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_csinc_aarch64_instrs_integer_conditional_select (fld w 0 5) (fld w 5 5) (fld w 10 1) (fld w 12 4) (fld w 16 5) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 188) := by
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
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486852#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486855#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (0#2 : BitVec 2)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t39_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t39_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (1#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, t39_0, t39_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 188) = True from by decide]
  all_goals rfl

theorem run_decode_csinc_condsel (Rd Rn : BitVec 5) (o2 : BitVec 1) (cond : BitVec 4) (Rm : BitVec 5) (op sf : BitVec 1)
    (s : SState) :
    (decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf).run s =
      (execute_aarch64_instrs_integer_conditional_select cond Rd.toNat (if sf == 1#1 then 64 else 32)
        (o2 == 1#1) (op == 1#1) Rm.toNat Rn.toNat).run s := by
  unfold decode_csinc_aarch64_instrs_integer_conditional_select
  rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 189 (`decode_csinv_aarch64_instrs_integer_conditional_select`). -/
theorem run_DataProcReg_condsel_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 512 = 212) (h1 : (w / 2 ^ 11) % 2 = 0) (h2 : (w / 2 ^ 30) % 2 = 1) (h3 : (w / 2 ^ 10) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_csinv_aarch64_instrs_integer_conditional_select (fld w 0 5) (fld w 5 5) (fld w 10 1) (fld w 12 4) (fld w 16 5) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 189) := by
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
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486852#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486855#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t40_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t40_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (0#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, t40_0, t40_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 189) = True from by decide]
  all_goals rfl

theorem run_decode_csinv_condsel (Rd Rn : BitVec 5) (o2 : BitVec 1) (cond : BitVec 4) (Rm : BitVec 5) (op sf : BitVec 1)
    (s : SState) :
    (decode_csinv_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf).run s =
      (execute_aarch64_instrs_integer_conditional_select cond Rd.toNat (if sf == 1#1 then 64 else 32)
        (o2 == 1#1) (op == 1#1) Rm.toNat Rn.toNat).run s := by
  unfold decode_csinv_aarch64_instrs_integer_conditional_select
  rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 190 (`decode_csneg_aarch64_instrs_integer_conditional_select`). -/
theorem run_DataProcReg_condsel_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 512 = 212) (h1 : (w / 2 ^ 11) % 2 = 0) (h2 : (w / 2 ^ 30) % 2 = 1) (h3 : (w / 2 ^ 10) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_csneg_aarch64_instrs_integer_conditional_select (fld w 0 5) (fld w 5 5) (fld w 10 1) (fld w 12 4) (fld w 16 5) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 190) := by
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
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486852#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486855#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f40 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (0#2 : BitVec 2)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t41_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t41_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (1#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, t41_0, t41_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 190) = True from by decide]
  all_goals rfl

theorem run_decode_csneg_condsel (Rd Rn : BitVec 5) (o2 : BitVec 1) (cond : BitVec 4) (Rm : BitVec 5) (op sf : BitVec 1)
    (s : SState) :
    (decode_csneg_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf).run s =
      (execute_aarch64_instrs_integer_conditional_select cond Rd.toNat (if sf == 1#1 then 64 else 32)
        (o2 == 1#1) (op == 1#1) Rm.toNat Rn.toNat).run s := by
  unfold decode_csneg_aarch64_instrs_integer_conditional_select
  rfl

set_option maxHeartbeats 4000000 in
theorem run_execute_condsel {js : Janus.Arm64.State} {s : SState} (h : Rel js s)
    (hspe : s.regs.get? .SPESampleInFlight = some false) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d m n : Nat} (hd : d < 32) (hm : m < 32) (hn : n < 32) (cond : BitVec 4)
    (inc inv : Bool) :
    ∃ s', (execute_aarch64_instrs_integer_conditional_select cond d N inc inv m n).run s = .ok () s' ∧
      Rel (Janus.Arm64.execCondSel N js inv m cond.toNat inc n d) s' ∧ Frame s s' := by
  obtain ⟨p, hp, hps⟩ := h.pstate
  unfold Janus.Arm64.execCondSel
  dsimp only
  have hinc : ∀ x : BitVec N, Sail.BitVec.addInt x 1 = x + 1 := by
    intro x; simp [Sail.BitVec.addInt]
  by_cases hc : Janus.Arm64.conditionHolds cond.toNat js.flags = true
  · obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd hN (js.getX N n)
    refine ⟨s', ?_, by simpa [hc] using hr, hf⟩
    simp only [execute_aarch64_instrs_integer_conditional_select, run_bind, run_undefined_bitvector,
      run_ConditionHolds hp hps, hc, ite_true, run_X_read_rel h hn hN, run_pure, hs']
    have hsp' : s'.regs.get? .SPESampleInFlight = some false := by
      rw [hf _ rfl (by decide) (by decide)]; exact hspe
    rw [run_readReg (r := .SPESampleInFlight) hsp']
    rfl
  · have hc' : Janus.Arm64.conditionHolds cond.toNat js.flags = false := by simpa using hc
    let r := (if inc then (if inv then ~~~js.getX N m else js.getX N m) + 1
      else (if inv then ~~~js.getX N m else js.getX N m))
    obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd hN r
    refine ⟨s', ?_, by simpa [hc', r] using hr, hf⟩
    simp only [execute_aarch64_instrs_integer_conditional_select, run_bind, run_undefined_bitvector,
      run_ConditionHolds hp hps, hc', Bool.false_eq_true, ite_false, run_X_read_rel h hm hN, run_pure, hinc]
    have : (if inc = true then (if inv = true then ~~~js.getX N m else js.getX N m) + 1
        else if inv = true then ~~~js.getX N m else js.getX N m) = r := rfl
    rw [this, hs']
    have hsp' : s'.regs.get? .SPESampleInFlight = some false := by
      rw [hf _ rfl (by decide) (by decide)]; exact hspe
    simp only [run_readReg (r := .SPESampleInFlight) hsp']
    rfl

set_option maxHeartbeats 8000000 in
theorem asl_condsel {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 512 = 0b011010100) (h2 : (w / 2 ^ 11) % 2 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hspe : s.regs.get? .SPESampleInFlight = some false)
    (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execCondSel (if fld w 31 1 == 1#1 then 64 else 32) js (fld w 30 1 == 1#1)
        (fld w 16 5).toNat (fld w 12 4).toNat (fld w 10 1 == 1#1) (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      s2.regs.get? .__BranchTaken = some false := by
  rw [run_DecodeA64_DPReg hw (by omega)]
  rcases (show (w / 2 ^ 30) % 2 = 0 ∨ (w / 2 ^ 30) % 2 = 1 by omega) with hk1 | hk1 <;>
  rcases (show (w / 2 ^ 10) % 2 = 0 ∨ (w / 2 ^ 10) % 2 = 1 by omega) with hk2 | hk2
  · rw [run_DataProcReg_condsel_0 hw h1 h2 hk1 hk2 (see_entry _ _), run_decode_csel_condsel]
    have hspe1 : ((stepEntry s (BitVec.ofNat 32 w)).set .SEE 187).regs.get? .SPESampleInFlight = some false := by
      rw [get?_set_ne _ (r := .SEE) _ (by decide)]; simp only [stepEntry]
      repeat rw [get?_set_ne _ _ (by decide)]
      exact hspe
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_condsel (h.entry (BitVec.ofNat 32 w) 187) hspe1 (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 12 4) (fld w 10 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_condsel_1 hw h1 h2 hk1 hk2 (see_entry _ _), run_decode_csinc_condsel]
    have hspe1 : ((stepEntry s (BitVec.ofNat 32 w)).set .SEE 188).regs.get? .SPESampleInFlight = some false := by
      rw [get?_set_ne _ (r := .SEE) _ (by decide)]; simp only [stepEntry]
      repeat rw [get?_set_ne _ _ (by decide)]
      exact hspe
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_condsel (h.entry (BitVec.ofNat 32 w) 188) hspe1 (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 12 4) (fld w 10 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_condsel_2 hw h1 h2 hk1 hk2 (see_entry _ _), run_decode_csinv_condsel]
    have hspe1 : ((stepEntry s (BitVec.ofNat 32 w)).set .SEE 189).regs.get? .SPESampleInFlight = some false := by
      rw [get?_set_ne _ (r := .SEE) _ (by decide)]; simp only [stepEntry]
      repeat rw [get?_set_ne _ _ (by decide)]
      exact hspe
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_condsel (h.entry (BitVec.ofNat 32 w) 189) hspe1 (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 12 4) (fld w 10 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · rw [run_DataProcReg_condsel_3 hw h1 h2 hk1 hk2 (see_entry _ _), run_decode_csneg_condsel]
    have hspe1 : ((stepEntry s (BitVec.ofNat 32 w)).set .SEE 190).regs.get? .SPESampleInFlight = some false := by
      rw [get?_set_ne _ (r := .SEE) _ (by decide)]; simp only [stepEntry]
      repeat rw [get?_set_ne _ _ (by decide)]
      exact hspe
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_condsel (h.entry (BitVec.ofNat 32 w) 190) hspe1 (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 12 4) (fld w 10 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩

/-- **CSEL/CSINC/CSINV/CSNEG**: for every word of the encoding class and every related pair of
states (with statistical profiling not sampling), Janus' `step` and the generated ASL agree. -/
theorem condSel_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 512 = 0b011010100)
    (h2 : (w / 2 ^ 11) % 2 = 0) {js : Janus.Arm64.State} {s : SState} (h : Rel js s)
    (hspe : s.regs.get? .SPESampleInFlight = some false) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' := by
  have hspec : ∀ N, (Janus.Arm64.execCondSel N js (fld w 30 1 == 1#1) (fld w 16 5).toNat (fld w 12 4).toNat
      (fld w 10 1 == 1#1) (fld w 5 5).toNat (fld w 0 5).toNat).pc = js.pc := by
    intro N; unfold Janus.Arm64.execCondSel; dsimp only
    simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR]; split <;> rfl
  refine step_agree h (asl_condsel hw h1 h2 h hspe _) (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_condSel_class hw h1 h2)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, ← fld_bit w 30 hw, ← fld_bit w 10 hw,
    bits_eq_fld w 20 16 hw, bits_eq_fld w 15 12 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next]

end JanusASL.Proofs
