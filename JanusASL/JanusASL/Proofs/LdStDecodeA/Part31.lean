-- JanusASL.Proofs.LdStDecodeA, part 31 (tools/split_proofs.py)
import JanusASL.Proofs.Step


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 547 (`decode_lduminb_aarch64_instrs_memory_atomicops_ld`). -/
theorem run_LS_at_07_10_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 1) (h4 : (w / 2 ^ 10) % 4 = 0) (h5 : (w / 2 ^ 15) % 2 = 0) (h6 : (w / 2 ^ 12) % 8 = 7) (h7 : (w / 2 ^ 23) % 2 = 1) (h8 : (w / 2 ^ 22) % 2 = 0) (h9 : (w / 2 ^ 30) % 4 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_lduminb_aarch64_instrs_memory_atomicops_ld (fld w 0 5) (fld w 5 5) (fld w 12 3) (fld w 16 5) (fld w 22 1) (fld w 23 1) (fld w 30 2)).run (s.set .SEE 547) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (1#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (17#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (145#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (16#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (29#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (25#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557315#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557319#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3392#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (110#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f40 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (54284#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f42 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3424#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (111#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (54796#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (54286#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f52 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (54798#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f54 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3328#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f55 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (108#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f56 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3360#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f57 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (109#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f62 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3136#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f63 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (102#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f64 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (50184#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f66 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (50180#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f68 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (50176#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f70 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3072#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f71 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (100#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f72 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (49160#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f74 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (49156#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f76 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (49152#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f78 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (4067316#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f80 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (0#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (120#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f83 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (4#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f86 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (8#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f89 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (12#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f92 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (16#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f95 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (20#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f98 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (24#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t101_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (56#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t101_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t101_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (28#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f38, f39, f40, f42, f43, f44, f48, f52, f54, f55, f56, f57, f62, f63, f64, f66, f68, f70, f71, f72, f74, f76, f78, f80, f81, f83, f86, f89, f92, f95, f98, t101_0, t101_1, t101_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 547) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 548 (`decode_lduminh_aarch64_instrs_memory_atomicops_ld`). -/
theorem run_LS_at_07_10_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 1) (h4 : (w / 2 ^ 10) % 4 = 0) (h5 : (w / 2 ^ 15) % 2 = 0) (h6 : (w / 2 ^ 12) % 8 = 7) (h7 : (w / 2 ^ 23) % 2 = 1) (h8 : (w / 2 ^ 22) % 2 = 0) (h9 : (w / 2 ^ 30) % 4 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_lduminh_aarch64_instrs_memory_atomicops_ld (fld w 0 5) (fld w 5 5) (fld w 12 3) (fld w 16 5) (fld w 22 1) (fld w 23 1) (fld w 30 2)).run (s.set .SEE 548) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (1#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (17#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (145#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (16#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (29#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (25#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557315#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557319#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3392#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (110#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f40 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (54284#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f42 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3424#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (111#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (54796#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (54286#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f52 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (54798#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f54 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3328#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f55 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (108#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f56 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3360#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f57 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (109#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f62 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3136#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f63 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (102#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f64 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (50184#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f66 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (50180#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f68 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (50176#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f70 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 16 == (3072#14 : BitVec 14)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f71 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (100#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f72 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (49160#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f74 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (49156#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f76 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 12 == (49152#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f78 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (4067316#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f80 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (56#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (0#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f84 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (4#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f87 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (8#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f90 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (12#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f93 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (16#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f96 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (20#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f99 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (24#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t102_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (120#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t102_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t102_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (28#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f38, f39, f40, f42, f43, f44, f48, f52, f54, f55, f56, f57, f62, f63, f64, f66, f68, f70, f71, f72, f74, f76, f78, f80, f81, f84, f87, f90, f93, f96, f99, t102_0, t102_1, t102_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 548) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 546 (`decode_ldumin_aarch64_instrs_memory_atomicops_ld`). -/
theorem run_LS_at_07_10_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 1) (h4 : (w / 2 ^ 10) % 4 = 0) (h5 : (w / 2 ^ 15) % 2 = 0) (h6 : (w / 2 ^ 12) % 8 = 7) (h7 : (w / 2 ^ 23) % 2 = 1) (h8 : (w / 2 ^ 22) % 2 = 0) (h9 : (w / 2 ^ 30) % 4 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_ldumin_aarch64_instrs_memory_atomicops_ld (fld w 0 5) (fld w 5 5) (fld w 12 3) (fld w 16 5) (fld w 22 1) (fld w 23 1) (fld w 30 2)).run (s.set .SEE 546) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (17#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (17#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (145#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (0#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (29#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (25#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557315#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557319#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f78 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (4067316#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f79 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (0#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f80 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (56#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (120#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f82 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (4#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f85 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (8#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f88 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (12#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f91 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (16#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f94 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (20#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f97 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (24#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t100_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t100_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (56#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t100_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t100_3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (28#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f78, f79, f80, f81, f82, f85, f88, f91, f94, f97, t100_0, t100_1, t100_2, t100_3, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 546) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 546 (`decode_ldumin_aarch64_instrs_memory_atomicops_ld`). -/
theorem run_LS_at_07_10_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 1) (h4 : (w / 2 ^ 10) % 4 = 0) (h5 : (w / 2 ^ 15) % 2 = 0) (h6 : (w / 2 ^ 12) % 8 = 7) (h7 : (w / 2 ^ 23) % 2 = 1) (h8 : (w / 2 ^ 22) % 2 = 0) (h9 : (w / 2 ^ 30) % 4 = 3) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_ldumin_aarch64_instrs_memory_atomicops_ld (fld w 0 5) (fld w 5 5) (fld w 12 3) (fld w 16 5) (fld w 22 1) (fld w 23 1) (fld w 30 2)).run (s.set .SEE 546) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 23 == (17#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (17#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (145#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (0#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (29#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (25#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557315#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557319#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f78 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (4067316#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f79 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (0#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f80 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (56#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (120#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f82 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (4#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f85 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (8#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f88 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (12#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f91 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (16#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f94 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (20#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f97 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (24#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t100_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t100_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (56#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t100_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t100_3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (28#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f78, f79, f80, f81, f82, f85, f88, f91, f94, f97, t100_0, t100_1, t100_2, t100_3, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 546) = True from by decide]
  all_goals rfl

end JanusASL.Proofs
