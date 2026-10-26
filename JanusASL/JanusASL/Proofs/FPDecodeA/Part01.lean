-- JanusASL.Proofs.FPDecodeA, part 1 (tools/split_proofs.py)
import JanusASL.Proofs.Step


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcFPSIMD` on its encoding class reaches clause SEE 243 (`decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub`). -/
theorem run_FP_fadd_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 31) % 2 = 0) (h1 : (w / 2 ^ 30) % 2 = 0) (h2 : (w / 2 ^ 29) % 2 = 0) (h3 : (w / 2 ^ 24) % 32 = 30) (h4 : (w / 2 ^ 22) % 4 = 0) (h5 : (w / 2 ^ 21) % 2 = 1) (h6 : (w / 2 ^ 10) % 64 = 10) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcFPSIMD pc (BitVec.ofNat 32 w)).run s =
      (decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub (fld w 0 5) (fld w 5 5) (fld w 12 1) (fld w 16 5) (fld w 22 2)).run (s.set .SEE 243) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (94#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (14#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (126#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (46#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280534#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280530#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280542#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280538#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (113#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (115#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (119#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (117#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1649#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (497872#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (239706#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (61#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (370#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (63#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (374#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (882#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 19 == (1504#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 19 == (480#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 19 == (480#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (375#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (373#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (371#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (369#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f64 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (752#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f65 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (112#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f67 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1648#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f68 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (368#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f69 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1014#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f70 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (253#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f72 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (93#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f73 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2096#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f74 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2064#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f75 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2128#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f76 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2160#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f77 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245310#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f78 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (29#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f79 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769598#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1010#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f82 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (252#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f84 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (92#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f89 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (754#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f90 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (188#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f91 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (114#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f92 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (28#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t105_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (30#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t105_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t105_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (10#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcFPSIMD]
  simp only [run_bind, f0, f1, f2, f3, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f34, f35, f36, f37, f38, f64, f65, f67, f68, f69, f70, f72, f73, f74, f75, f76, f77, f78, f79, f81, f82, f84, f89, f90, f91, f92, t105_0, t105_1, t105_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 243) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcFPSIMD` on its encoding class reaches clause SEE 244 (`decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub`). -/
theorem run_FP_fsub_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 31) % 2 = 0) (h1 : (w / 2 ^ 30) % 2 = 0) (h2 : (w / 2 ^ 29) % 2 = 0) (h3 : (w / 2 ^ 24) % 32 = 30) (h4 : (w / 2 ^ 22) % 4 = 0) (h5 : (w / 2 ^ 21) % 2 = 1) (h6 : (w / 2 ^ 10) % 64 = 14) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcFPSIMD pc (BitVec.ofNat 32 w)).run s =
      (decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub (fld w 0 5) (fld w 5 5) (fld w 12 1) (fld w 16 5) (fld w 22 2)).run (s.set .SEE 244) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (94#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (14#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (126#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (46#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280534#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280530#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280542#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280538#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (113#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (115#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (119#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (117#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1649#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (497872#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (239706#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (61#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (370#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (63#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (374#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (882#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 19 == (1504#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 19 == (480#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 19 == (480#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (375#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (373#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (371#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (369#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f64 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (752#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f65 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (112#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f67 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1648#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f68 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (368#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f69 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1014#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f70 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (253#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f72 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (93#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f73 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2096#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f74 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2064#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f75 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2128#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f76 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2160#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f77 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245310#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f78 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (29#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f79 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769598#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1010#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f82 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (252#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f84 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (92#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f89 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (754#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f90 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (188#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f91 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (114#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f92 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (28#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f105 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (10#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t106_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (30#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t106_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t106_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (14#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcFPSIMD]
  simp only [run_bind, f0, f1, f2, f3, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f34, f35, f36, f37, f38, f64, f65, f67, f68, f69, f70, f72, f73, f74, f75, f76, f77, f78, f79, f81, f82, f84, f89, f90, f91, f92, f105, t106_0, t106_1, t106_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 244) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcFPSIMD` on its encoding class reaches clause SEE 410 (`decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product`). -/
theorem run_FP_fmul_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 31) % 2 = 0) (h1 : (w / 2 ^ 30) % 2 = 0) (h2 : (w / 2 ^ 29) % 2 = 0) (h3 : (w / 2 ^ 24) % 32 = 30) (h4 : (w / 2 ^ 22) % 4 = 0) (h5 : (w / 2 ^ 21) % 2 = 1) (h6 : (w / 2 ^ 10) % 64 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcFPSIMD pc (BitVec.ofNat 32 w)).run s =
      (decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product (fld w 0 5) (fld w 5 5) (fld w 15 1) (fld w 16 5) (fld w 22 2)).run (s.set .SEE 410) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (94#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (14#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (126#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (46#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280534#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280530#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280542#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280538#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (113#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (115#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (119#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (117#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1649#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (497872#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (239706#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (61#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (370#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (63#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (374#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (882#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 19 == (1504#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 19 == (480#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 19 == (480#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (375#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (373#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (371#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (369#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f64 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (752#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f65 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (112#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f67 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1648#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f68 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (368#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f69 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1014#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f70 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (253#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f72 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (93#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f73 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2096#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f74 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2064#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f75 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2128#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f76 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2160#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f77 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245310#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f78 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (29#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f79 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769598#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1010#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f82 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (252#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f84 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (92#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f89 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (754#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f90 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (188#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f91 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (114#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f92 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (28#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f105 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (10#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f106 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (14#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f110 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (1#2 : BitVec 2)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f112 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1556022#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f113 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (189#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f114 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245302#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f116 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2080306#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f118 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769586#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f120 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1556018#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f122 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245298#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f124 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2080310#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f126 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769590#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f129 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (47#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f130 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1556026#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f132 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245306#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f134 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (8#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f136 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (3#2 : BitVec 2)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f137 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 14 10 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f138 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1547890#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f140 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (237170#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f142 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2072178#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f144 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (761458#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f146 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2304#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f147 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2368#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f148 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (3072#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f149 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (3136#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f150 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2048#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f151 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2112#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f152 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2560#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f153 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2624#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f154 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (3584#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f155 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (3648#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f156 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (499584#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f157 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (0#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f158 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2176#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f159 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2240#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f161 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1547886#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f163 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (237166#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f165 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2072174#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f167 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (761454#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f169 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1547882#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f171 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (237162#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f173 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2072170#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f175 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (761450#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f177 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1556074#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f179 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245354#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f181 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2080362#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f183 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769642#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f185 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1556078#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f187 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245358#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f189 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2080366#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f191 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769646#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f196 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 16 == (24#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f197 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 16 == (25#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f198 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 16 == (2#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f199 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 16 == (3#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f200 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (190#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f201 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (30#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f202 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (254#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f203 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (94#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f206 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (6#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f207 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (31#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f211 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (18#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f212 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (26#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f213 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (22#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f214 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (30#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f219 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (118#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f235 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (232498#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f237 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (240690#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f243 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (232510#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f245 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (240702#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f247 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (380#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f248 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (191#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f249 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (60#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f250 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (31#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f259 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (62#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f260 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (190#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f269 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 12 5 == (128#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t272_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (30#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t272_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t272_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (2#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcFPSIMD]
  simp only [run_bind, f0, f1, f2, f3, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f34, f35, f36, f37, f38, f64, f65, f67, f68, f69, f70, f72, f73, f74, f75, f76, f77, f78, f79, f81, f82, f84, f89, f90, f91, f92, f105, f106, f110, f112, f113, f114, f116, f118, f120, f122, f124, f126, f129, f130, f132, f134, f136, f137, f138, f140, f142, f144, f146, f147, f148, f149, f150, f151, f152, f153, f154, f155, f156, f157, f158, f159, f161, f163, f165, f167, f169, f171, f173, f175, f177, f179, f181, f183, f185, f187, f189, f191, f196, f197, f198, f199, f200, f201, f202, f203, f206, f207, f211, f212, f213, f214, f219, f235, f237, f243, f245, f247, f248, f249, f250, f259, f260, f269, t272_0, t272_1, t272_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 410) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcFPSIMD` on its encoding class reaches clause SEE 344 (`decode_fdiv_float_aarch64_instrs_float_arithmetic_div`). -/
theorem run_FP_fdiv_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 31) % 2 = 0) (h1 : (w / 2 ^ 30) % 2 = 0) (h2 : (w / 2 ^ 29) % 2 = 0) (h3 : (w / 2 ^ 24) % 32 = 30) (h4 : (w / 2 ^ 22) % 4 = 0) (h5 : (w / 2 ^ 21) % 2 = 1) (h6 : (w / 2 ^ 10) % 64 = 6) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcFPSIMD pc (BitVec.ofNat 32 w)).run s =
      (decode_fdiv_float_aarch64_instrs_float_arithmetic_div (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 22 2)).run (s.set .SEE 344) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (94#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (14#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (126#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (46#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280534#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280530#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280542#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1280538#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (113#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (115#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (119#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (117#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1649#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (497872#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (239706#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (61#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (370#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (63#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (374#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (882#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 19 == (1504#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 19 == (480#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 19 == (480#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (375#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (373#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (371#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (369#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f64 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (752#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f65 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (112#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f67 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1648#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f68 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (368#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f69 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1014#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f70 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (253#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f72 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (93#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f73 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2096#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f74 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2064#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f75 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2128#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f76 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2160#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f77 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245310#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f78 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (29#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f79 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769598#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1010#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f82 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (252#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f84 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (92#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f89 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (754#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f90 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (188#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f91 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (114#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f92 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (28#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f105 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (10#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f106 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (14#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f110 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (1#2 : BitVec 2)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f112 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1556022#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f113 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (189#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f114 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245302#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f116 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2080306#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f118 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769586#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f120 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1556018#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f122 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245298#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f124 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2080310#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f126 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769590#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f129 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (47#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f130 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1556026#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f132 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245306#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f134 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (8#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f136 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (3#2 : BitVec 2)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f137 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 14 10 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f138 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1547890#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f140 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (237170#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f142 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2072178#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f144 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (761458#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f146 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2304#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f147 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2368#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f148 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (3072#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f149 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (3136#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f150 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2048#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f151 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2112#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f152 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2560#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f153 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2624#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f154 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (3584#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f155 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (3648#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f156 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (499584#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f157 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (0#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f158 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2176#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f159 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 10 == (2240#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f161 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1547886#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f163 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (237166#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f165 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2072174#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f167 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (761454#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f169 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1547882#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f171 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (237162#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f173 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2072170#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f175 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (761450#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f177 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1556074#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f179 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245354#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f181 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2080362#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f183 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769642#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f185 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1556078#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f187 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (245358#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f189 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (2080366#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f191 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (769646#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f196 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 16 == (24#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f197 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 16 == (25#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f198 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 16 == (2#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f199 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 16 == (3#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f200 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (190#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f201 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (30#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f202 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (254#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f203 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (94#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t206_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (30#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t206_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t206_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (6#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcFPSIMD]
  simp only [run_bind, f0, f1, f2, f3, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f34, f35, f36, f37, f38, f64, f65, f67, f68, f69, f70, f72, f73, f74, f75, f76, f77, f78, f79, f81, f82, f84, f89, f90, f91, f92, f105, f106, f110, f112, f113, f114, f116, f118, f120, f122, f124, f126, f129, f130, f132, f134, f136, f137, f138, f140, f142, f144, f146, f147, f148, f149, f150, f151, f152, f153, f154, f155, f156, f157, f158, f159, f161, f163, f165, f167, f169, f171, f173, f175, f177, f179, f181, f183, f185, f187, f189, f191, f196, f197, f198, f199, f200, f201, f202, f203, t206_0, t206_1, t206_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 344) = True from by decide]
  all_goals rfl

end JanusASL.Proofs
