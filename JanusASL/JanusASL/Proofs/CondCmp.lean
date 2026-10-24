import JanusASL.Proofs.Step
import JanusASL.Proofs.AddSubImm
import JanusASL.Proofs.Cond

/-! # Proved: CCMN/CCMP (register and immediate), the whole encoding class

Words `sf op 1 11010010 Rm|imm5 cond i 0 Rn 0 nzcv` (bits 29:21 = `111010010`, bit 10 = 0,
bit 4 = 0; 2^19 words). Assumes statistical profiling is not sampling. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- A 4-bit NZCV immediate as Janus flags (`Exec.execCondCmp`). -/
def flagsOf (nz : Nat) : Janus.Arm64.Flags :=
  { n := Janus.Arm64.bit nz 3, z := Janus.Arm64.bit nz 2, c := Janus.Arm64.bit nz 1, v := Janus.Arm64.bit nz 0 }

theorem extract_flagsOf (nz : BitVec 4) :
    Sail.BitVec.extractLsb nz 3 3 = BitVec.ofBool (flagsOf nz.toNat).n ∧
    Sail.BitVec.extractLsb nz 2 2 = BitVec.ofBool (flagsOf nz.toNat).z ∧
    Sail.BitVec.extractLsb nz 1 1 = BitVec.ofBool (flagsOf nz.toNat).c ∧
    Sail.BitVec.extractLsb nz 0 0 = BitVec.ofBool (flagsOf nz.toNat).v := by
  have e : nz = BitVec.ofNat 4 nz.toNat := by simp
  have hl := nz.isLt
  rw [e]
  generalize nz.toNat = c at hl
  match c, hl with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide
  | 8, _ => decide
  | 9, _ => decide
  | 10, _ => decide
  | 11, _ => decide
  | 12, _ => decide
  | 13, _ => decide
  | 14, _ => decide
  | 15, _ => decide
  | _ + 16, hl => exact absurd hl (by omega)

/-- The four NZCV writes of the generated code, from flag bits `nz`. -/
theorem run_write_nzcv {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {p : ProcState}
    (hp : s.regs.get? .PSTATE = some p) (f : Janus.Arm64.Flags) {nz : BitVec 4}
    (hn : Sail.BitVec.extractLsb nz 3 3 = BitVec.ofBool f.n) (hz : Sail.BitVec.extractLsb nz 2 2 = BitVec.ofBool f.z)
    (hc : Sail.BitVec.extractLsb nz 1 1 = BitVec.ofBool f.c) (hv : Sail.BitVec.extractLsb nz 0 0 = BitVec.ofBool f.v)
    {β} (k : SailM β) :
    (do writeReg Register.PSTATE { (← readReg Register.PSTATE) with N := (Sail.BitVec.extractLsb nz 3 3) }
        writeReg Register.PSTATE { (← readReg Register.PSTATE) with Z := (Sail.BitVec.extractLsb nz 2 2) }
        writeReg Register.PSTATE { (← readReg Register.PSTATE) with C := (Sail.BitVec.extractLsb nz 1 1) }
        writeReg Register.PSTATE { (← readReg Register.PSTATE) with V := (Sail.BitVec.extractLsb nz 0 0) }
        k).run s =
      k.run (s.set .PSTATE
        { p with N := BitVec.ofBool f.n, Z := BitVec.ofBool f.z, C := BitVec.ofBool f.c, V := BitVec.ofBool f.v }) := by
  simp only [run_bind, run_readReg hp, run_writeReg, run_readReg (get?_set_PSTATE _ _), SState.set_set, hn, hz,
    hc, hv]

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 119 (`decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register`). -/
theorem run_DataProcReg_ccmp_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 512 = 466) (h1 : (w / 2 ^ 10) % 2 = 0) (h2 : (w / 2 ^ 4) % 2 = 0) (h3 : (w / 2 ^ 11) % 2 = 0) (h4 : (w / 2 ^ 30) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register (fld w 0 4) (fld w 5 5) (fld w 12 4) (fld w 16 5) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 119) := by
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
  have t29_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t29_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (0#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t29_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 4 4 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, t29_0, t29_1, t29_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 119) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 120 (`decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register`). -/
theorem run_DataProcReg_ccmp_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 512 = 466) (h1 : (w / 2 ^ 10) % 2 = 0) (h2 : (w / 2 ^ 4) % 2 = 0) (h3 : (w / 2 ^ 11) % 2 = 0) (h4 : (w / 2 ^ 30) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register (fld w 0 4) (fld w 5 5) (fld w 12 4) (fld w 16 5) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 120) := by
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
  have t30_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t30_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (0#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t30_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 4 4 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, t30_0, t30_1, t30_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 120) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 121 (`decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate`). -/
theorem run_DataProcReg_ccmp_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 512 = 466) (h1 : (w / 2 ^ 10) % 2 = 0) (h2 : (w / 2 ^ 4) % 2 = 0) (h3 : (w / 2 ^ 11) % 2 = 1) (h4 : (w / 2 ^ 30) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate (fld w 0 4) (fld w 5 5) (fld w 12 4) (fld w 16 5) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 121) := by
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
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (0#2 : BitVec 2)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t31_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t31_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (2#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t31_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 4 4 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, t31_0, t31_1, t31_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 121) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 122 (`decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate`). -/
theorem run_DataProcReg_ccmp_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 512 = 466) (h1 : (w / 2 ^ 10) % 2 = 0) (h2 : (w / 2 ^ 4) % 2 = 0) (h3 : (w / 2 ^ 11) % 2 = 1) (h4 : (w / 2 ^ 30) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate (fld w 0 4) (fld w 5 5) (fld w 12 4) (fld w 16 5) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 122) := by
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
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (0#2 : BitVec 2)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t32_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t32_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (2#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t32_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 4 4 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, t32_0, t32_1, t32_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 122) = True from by decide]
  all_goals rfl

theorem run_decode_ccmn_reg (nzcv : BitVec 4) (Rn : BitVec 5) (cond : BitVec 4) (Rm : BitVec 5) (op sf : BitVec 1)
    (s : SState) :
    (decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op sf).run s =
      (execute_aarch64_instrs_integer_conditional_compare_register cond (if sf == 1#1 then 64 else 32) nzcv
        Rm.toNat Rn.toNat (op == 1#1)).run s := by
  unfold decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register
  rfl

theorem run_decode_ccmp_reg (nzcv : BitVec 4) (Rn : BitVec 5) (cond : BitVec 4) (Rm : BitVec 5) (op sf : BitVec 1)
    (s : SState) :
    (decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op sf).run s =
      (execute_aarch64_instrs_integer_conditional_compare_register cond (if sf == 1#1 then 64 else 32) nzcv
        Rm.toNat Rn.toNat (op == 1#1)).run s := by
  unfold decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register
  rfl

theorem run_decode_ccmn_imm (nzcv : BitVec 4) (Rn : BitVec 5) (cond : BitVec 4) (imm5 : BitVec 5) (op sf : BitVec 1)
    (s : SState) :
    (decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op sf).run s =
      (execute_aarch64_instrs_integer_conditional_compare_immediate cond (if sf == 1#1 then 64 else 32) nzcv
        (Sail.BitVec.zeroExtend imm5 (if sf == 1#1 then 64 else 32)) Rn.toNat (op == 1#1)).run s := by
  unfold decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate
  rfl

theorem run_decode_ccmp_imm (nzcv : BitVec 4) (Rn : BitVec 5) (cond : BitVec 4) (imm5 : BitVec 5) (op sf : BitVec 1)
    (s : SState) :
    (decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op sf).run s =
      (execute_aarch64_instrs_integer_conditional_compare_immediate cond (if sf == 1#1 then 64 else 32) nzcv
        (Sail.BitVec.zeroExtend imm5 (if sf == 1#1 then 64 else 32)) Rn.toNat (op == 1#1)).run s := by
  unfold decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate
  rfl


theorem spe_after {s : SState} (hspe : s.regs.get? .SPESampleInFlight = some false) (q : ProcState) :
    (s.set .PSTATE q).regs.get? .SPESampleInFlight = some false := by
  rw [get?_set_ne _ (r := .PSTATE) _ (by decide)]; exact hspe

set_option maxHeartbeats 4000000 in
theorem run_execute_ccmp_reg {js : Janus.Arm64.State} {s : SState} (h : Rel js s)
    (hspe : s.regs.get? .SPESampleInFlight = some false) {N : Nat} (hN : N = 32 ∨ N = 64)
    (m : Nat) (hm : m < 32) {n : Nat} (hn : n < 32) (cond nz : BitVec 4) (sub : Bool) :
    ∃ s', (execute_aarch64_instrs_integer_conditional_compare_register cond N nz m n sub).run s = .ok () s' ∧
      Rel (Janus.Arm64.execCondCmp js sub (js.getX N n) (js.getX N m) cond.toNat nz.toNat) s' ∧ Frame s s' := by
  obtain ⟨p, hp, hps⟩ := h.pstate
  have hN0 : 0 < N := by omega
  unfold Janus.Arm64.execCondCmp
  by_cases hc : Janus.Arm64.conditionHolds cond.toNat js.flags = true
  · refine ⟨_, ?_, by simpa [hc] using h.setFlags hp (Janus.Arm64.addSub (js.getX N n) (js.getX N m) sub).2,
      fun x _ _ hx => get?_set_ne s _ (Ne.symm hx)⟩
    simp only [execute_aarch64_instrs_integer_conditional_compare_register, run_bind, run_ConditionHolds hp hps, hc,
      ite_true, run_X_read_rel h hn hN, run_X_read_rel h hm hN, run_pure, pair_ofBool, AddWithCarry_eq hN0, ← addSub_eq]
    simp only [run_bind, run_readReg hp, run_writeReg, run_readReg (get?_set_PSTATE _ _), SState.set_set,
      nzcv_n, nzcv_z, nzcv_c, nzcv_v, run_readReg (spe_after hspe _), Bool.false_eq_true, ite_false, run_pure]
  · have hc' : Janus.Arm64.conditionHolds cond.toNat js.flags = false := by simpa using hc
    obtain ⟨e1, e2, e3, e4⟩ := extract_flagsOf nz
    refine ⟨_, ?_, by simpa [hc', flagsOf] using h.setFlags hp (flagsOf nz.toNat),
      fun x _ _ hx => get?_set_ne s _ (Ne.symm hx)⟩
    simp only [execute_aarch64_instrs_integer_conditional_compare_register, run_bind, run_ConditionHolds hp hps, hc',
      Bool.false_eq_true, ite_false, run_pure]
    simp only [run_bind, run_readReg hp, run_writeReg, run_readReg (get?_set_PSTATE _ _), SState.set_set,
      e1, e2, e3, e4, run_readReg (spe_after hspe _), Bool.false_eq_true, ite_false, run_pure]
    all_goals rfl

set_option maxHeartbeats 4000000 in
theorem run_execute_ccmp_imm {js : Janus.Arm64.State} {s : SState} (h : Rel js s)
    (hspe : s.regs.get? .SPESampleInFlight = some false) {N : Nat} (hN : N = 32 ∨ N = 64)
    (imm : BitVec N) {n : Nat} (hn : n < 32) (cond nz : BitVec 4) (sub : Bool) :
    ∃ s', (execute_aarch64_instrs_integer_conditional_compare_immediate cond N nz imm n sub).run s = .ok () s' ∧
      Rel (Janus.Arm64.execCondCmp js sub (js.getX N n) imm cond.toNat nz.toNat) s' ∧ Frame s s' := by
  obtain ⟨p, hp, hps⟩ := h.pstate
  have hN0 : 0 < N := by omega
  unfold Janus.Arm64.execCondCmp
  by_cases hc : Janus.Arm64.conditionHolds cond.toNat js.flags = true
  · refine ⟨_, ?_, by simpa [hc] using h.setFlags hp (Janus.Arm64.addSub (js.getX N n) imm sub).2,
      fun x _ _ hx => get?_set_ne s _ (Ne.symm hx)⟩
    simp only [execute_aarch64_instrs_integer_conditional_compare_immediate, run_bind, run_ConditionHolds hp hps, hc,
      ite_true, run_X_read_rel h hn hN,  run_pure, pair_ofBool, AddWithCarry_eq hN0, ← addSub_eq]
    simp only [run_bind, run_readReg hp, run_writeReg, run_readReg (get?_set_PSTATE _ _), SState.set_set,
      nzcv_n, nzcv_z, nzcv_c, nzcv_v, run_readReg (spe_after hspe _), Bool.false_eq_true, ite_false, run_pure]
  · have hc' : Janus.Arm64.conditionHolds cond.toNat js.flags = false := by simpa using hc
    obtain ⟨e1, e2, e3, e4⟩ := extract_flagsOf nz
    refine ⟨_, ?_, by simpa [hc', flagsOf] using h.setFlags hp (flagsOf nz.toNat),
      fun x _ _ hx => get?_set_ne s _ (Ne.symm hx)⟩
    simp only [execute_aarch64_instrs_integer_conditional_compare_immediate, run_bind, run_ConditionHolds hp hps, hc',
      Bool.false_eq_true, ite_false, run_pure]
    simp only [run_bind, run_readReg hp, run_writeReg, run_readReg (get?_set_PSTATE _ _), SState.set_set,
      e1, e2, e3, e4, run_readReg (spe_after hspe _), Bool.false_eq_true, ite_false, run_pure]
    all_goals rfl

set_option maxHeartbeats 8000000 in
theorem asl_ccmp_reg {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 512 = 0b111010010)
    (h2 : (w / 2 ^ 10) % 2 = 0) (h3 : (w / 2 ^ 4) % 2 = 0) (h4 : (w / 2 ^ 11) % 2 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hspe : s.regs.get? .SPESampleInFlight = some false)
    (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execCondCmp js (fld w 30 1 == 1#1) (js.getX (if fld w 31 1 == 1#1 then 64 else 32) (fld w 5 5).toNat)
        (js.getX (if fld w 31 1 == 1#1 then 64 else 32) (fld w 16 5).toNat) (fld w 12 4).toNat (fld w 0 4).toNat) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  rw [run_DecodeA64_DPReg hw (by omega)]
  rcases (show (w / 2 ^ 30) % 2 = 0 ∨ (w / 2 ^ 30) % 2 = 1 by omega) with hk | hk
  · rw [run_DataProcReg_ccmp_0 hw h1 h2 h3 h4 hk (see_entry _ _), run_decode_ccmn_reg]
    have hspe1 : ((stepEntry s (BitVec.ofNat 32 w)).set .SEE 119).regs.get? .SPESampleInFlight = some false := by
      rw [get?_set_ne _ (r := .SEE) _ (by decide)]; simp only [stepEntry]
      repeat rw [get?_set_ne _ _ (by decide)]
      exact hspe
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_ccmp_reg (h.entry (BitVec.ofNat 32 w) 119) hspe1 (width_cases w)
      (fld w 16 5).toNat (fld_lt w 16 5) (fld_lt w 5 5) (fld w 12 4) (fld w 0 4) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcReg_ccmp_1 hw h1 h2 h3 h4 hk (see_entry _ _), run_decode_ccmp_reg]
    have hspe1 : ((stepEntry s (BitVec.ofNat 32 w)).set .SEE 120).regs.get? .SPESampleInFlight = some false := by
      rw [get?_set_ne _ (r := .SEE) _ (by decide)]; simp only [stepEntry]
      repeat rw [get?_set_ne _ _ (by decide)]
      exact hspe
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_ccmp_reg (h.entry (BitVec.ofNat 32 w) 120) hspe1 (width_cases w)
      (fld w 16 5).toNat (fld_lt w 16 5) (fld_lt w 5 5) (fld w 12 4) (fld w 0 4) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩

/-- **condCmpReg (CCMN/CCMP)**: for every word of the encoding class and every related pair of states
(with statistical profiling not sampling), Janus' `step` and the generated ASL agree. -/
theorem condCmpReg_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 512 = 0b111010010)
    (h2 : (w / 2 ^ 10) % 2 = 0) (h3 : (w / 2 ^ 4) % 2 = 0) (h4 : (w / 2 ^ 11) % 2 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hspe : s.regs.get? .SPESampleInFlight = some false) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  have hspec : ∀ N, (Janus.Arm64.execCondCmp js (fld w 30 1 == 1#1) (js.getX N (fld w 5 5).toNat)
      (js.getX N (fld w 16 5).toNat) (fld w 12 4).toNat (fld w 0 4).toNat).pc = js.pc := by
    intro N; unfold Janus.Arm64.execCondCmp; split <;> simp [Janus.Arm64.State.setFlags]
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execCondCmp js (fld w 30 1 == 1#1)
    (js.getX N (fld w 5 5).toNat) (js.getX N (fld w 16 5).toNat) (fld w 12 4).toNat (fld w 0 4).toNat
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_ccmp_reg hw h1 h2 h3 h4 h hspe (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_condCmpReg_class hw h1 h2 h3 h4)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, ← fld_bit w 30 hw,
    bits_eq_fld w 20 16 hw, bits_eq_fld w 15 12 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 3 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, Sail.BitVec.zeroExtend, F]

set_option maxHeartbeats 8000000 in
theorem asl_ccmp_imm {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 512 = 0b111010010)
    (h2 : (w / 2 ^ 10) % 2 = 0) (h3 : (w / 2 ^ 4) % 2 = 0) (h4 : (w / 2 ^ 11) % 2 = 1)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hspe : s.regs.get? .SPESampleInFlight = some false)
    (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execCondCmp js (fld w 30 1 == 1#1) (js.getX (if fld w 31 1 == 1#1 then 64 else 32) (fld w 5 5).toNat)
        (Sail.BitVec.zeroExtend (fld w 16 5) (if fld w 31 1 == 1#1 then 64 else 32)) (fld w 12 4).toNat (fld w 0 4).toNat) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  rw [run_DecodeA64_DPReg hw (by omega)]
  rcases (show (w / 2 ^ 30) % 2 = 0 ∨ (w / 2 ^ 30) % 2 = 1 by omega) with hk | hk
  · rw [run_DataProcReg_ccmp_2 hw h1 h2 h3 h4 hk (see_entry _ _), run_decode_ccmn_imm]
    have hspe1 : ((stepEntry s (BitVec.ofNat 32 w)).set .SEE 121).regs.get? .SPESampleInFlight = some false := by
      rw [get?_set_ne _ (r := .SEE) _ (by decide)]; simp only [stepEntry]
      repeat rw [get?_set_ne _ _ (by decide)]
      exact hspe
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_ccmp_imm (h.entry (BitVec.ofNat 32 w) 121) hspe1 (width_cases w)
      (Sail.BitVec.zeroExtend (fld w 16 5) (if fld w 31 1 == 1#1 then 64 else 32)) (fld_lt w 5 5) (fld w 12 4)
      (fld w 0 4) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcReg_ccmp_3 hw h1 h2 h3 h4 hk (see_entry _ _), run_decode_ccmp_imm]
    have hspe1 : ((stepEntry s (BitVec.ofNat 32 w)).set .SEE 122).regs.get? .SPESampleInFlight = some false := by
      rw [get?_set_ne _ (r := .SEE) _ (by decide)]; simp only [stepEntry]
      repeat rw [get?_set_ne _ _ (by decide)]
      exact hspe
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_ccmp_imm (h.entry (BitVec.ofNat 32 w) 122) hspe1 (width_cases w)
      (Sail.BitVec.zeroExtend (fld w 16 5) (if fld w 31 1 == 1#1 then 64 else 32)) (fld_lt w 5 5) (fld w 12 4)
      (fld w 0 4) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩

/-- **condCmpImm (CCMN/CCMP)**: for every word of the encoding class and every related pair of states
(with statistical profiling not sampling), Janus' `step` and the generated ASL agree. -/
theorem condCmpImm_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 512 = 0b111010010)
    (h2 : (w / 2 ^ 10) % 2 = 0) (h3 : (w / 2 ^ 4) % 2 = 0) (h4 : (w / 2 ^ 11) % 2 = 1)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hspe : s.regs.get? .SPESampleInFlight = some false) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  have hspec : ∀ N, (Janus.Arm64.execCondCmp js (fld w 30 1 == 1#1) (js.getX N (fld w 5 5).toNat)
      (Sail.BitVec.zeroExtend (fld w 16 5) N) (fld w 12 4).toNat (fld w 0 4).toNat).pc = js.pc := by
    intro N; unfold Janus.Arm64.execCondCmp; split <;> simp [Janus.Arm64.State.setFlags]
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execCondCmp js (fld w 30 1 == 1#1)
    (js.getX N (fld w 5 5).toNat) (Sail.BitVec.zeroExtend (fld w 16 5) N) (fld w 12 4).toNat (fld w 0 4).toNat
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_ccmp_imm hw h1 h2 h3 h4 h hspe (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_condCmpImm_class hw h1 h2 h3 h4)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, ← fld_bit w 30 hw,
    bits_eq_fld w 20 16 hw, bits_eq_fld w 15 12 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 3 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, Sail.BitVec.zeroExtend, F]

end JanusASL.Proofs
