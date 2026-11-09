-- JanusASL.Proofs.LdStDecodeO, part 5 (tools/split_proofs.py)
import JanusASL.Proofs.Step


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 553 (`decode_ldaprb_aarch64_instrs_memory_ordered_rcpc`). -/
theorem run_LS_ldapr_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 23) % 2 = 1) (h4 : (w / 2 ^ 22) % 2 = 0) (h5 : (w / 2 ^ 21) % 2 = 1) (h6 : (w / 2 ^ 16) % 32 = 31) (h7 : (w / 2 ^ 15) % 2 = 1) (h8 : (w / 2 ^ 12) % 8 = 4) (h9 : (w / 2 ^ 10) % 4 = 0) (h10 : (w / 2 ^ 30) % 4 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_ldaprb_aarch64_instrs_memory_ordered_rcpc (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 30 2)).run (s.set .SEE 553) := by
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
  have f101 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (28#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f103 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (217185#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f104 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (213089#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t107_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (929776#22 : BitVec 22)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have s16 : Sail.BitVec.access (BitVec.ofNat 32 w) 16 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s17 : Sail.BitVec.access (BitVec.ofNat 32 w) 17 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s18 : Sail.BitVec.access (BitVec.ofNat 32 w) 18 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s19 : Sail.BitVec.access (BitVec.ofNat 32 w) 19 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s20 : Sail.BitVec.access (BitVec.ofNat 32 w) 20 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f38, f39, f40, f42, f43, f44, f48, f52, f54, f55, f56, f57, f62, f63, f64, f66, f68, f70, f71, f72, f74, f76, f78, f80, f81, f83, f86, f89, f92, f95, f98, f101, f103, f104, t107_0, s16, s17, s18, s19, s20, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg, bne_self_eq_false, Bool.or_false,
    show ((-1 : Int) < 553) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 554 (`decode_ldaprh_aarch64_instrs_memory_ordered_rcpc`). -/
theorem run_LS_ldapr_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 23) % 2 = 1) (h4 : (w / 2 ^ 22) % 2 = 0) (h5 : (w / 2 ^ 21) % 2 = 1) (h6 : (w / 2 ^ 16) % 32 = 31) (h7 : (w / 2 ^ 15) % 2 = 1) (h8 : (w / 2 ^ 12) % 8 = 4) (h9 : (w / 2 ^ 10) % 4 = 0) (h10 : (w / 2 ^ 30) % 4 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_ldaprh_aarch64_instrs_memory_ordered_rcpc (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 30 2)).run (s.set .SEE 554) := by
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
  have f102 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (28#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f103 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (217185#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f104 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (213089#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f107 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (929776#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t108_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1978352#22 : BitVec 22)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have s16 : Sail.BitVec.access (BitVec.ofNat 32 w) 16 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s17 : Sail.BitVec.access (BitVec.ofNat 32 w) 17 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s18 : Sail.BitVec.access (BitVec.ofNat 32 w) 18 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s19 : Sail.BitVec.access (BitVec.ofNat 32 w) 19 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s20 : Sail.BitVec.access (BitVec.ofNat 32 w) 20 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f38, f39, f40, f42, f43, f44, f48, f52, f54, f55, f56, f57, f62, f63, f64, f66, f68, f70, f71, f72, f74, f76, f78, f80, f81, f84, f87, f90, f93, f96, f99, f102, f103, f104, f107, t108_0, s16, s17, s18, s19, s20, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg, bne_self_eq_false, Bool.or_false,
    show ((-1 : Int) < 554) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 551 (`decode_ldapr_aarch64_instrs_memory_ordered_rcpc`). -/
theorem run_LS_ldapr_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 23) % 2 = 1) (h4 : (w / 2 ^ 22) % 2 = 0) (h5 : (w / 2 ^ 21) % 2 = 1) (h6 : (w / 2 ^ 16) % 32 = 31) (h7 : (w / 2 ^ 15) % 2 = 1) (h8 : (w / 2 ^ 12) % 8 = 4) (h9 : (w / 2 ^ 10) % 4 = 0) (h10 : (w / 2 ^ 30) % 4 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_ldapr_aarch64_instrs_memory_ordered_rcpc (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 30 2)).run (s.set .SEE 551) := by
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
  have f100 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (28#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t105_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t105_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (929776#20 : BitVec 20)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have s16 : Sail.BitVec.access (BitVec.ofNat 32 w) 16 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s17 : Sail.BitVec.access (BitVec.ofNat 32 w) 17 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s18 : Sail.BitVec.access (BitVec.ofNat 32 w) 18 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s19 : Sail.BitVec.access (BitVec.ofNat 32 w) 19 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s20 : Sail.BitVec.access (BitVec.ofNat 32 w) 20 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f78, f79, f80, f81, f82, f85, f88, f91, f94, f97, f100, t105_0, t105_1, s16, s17, s18, s19, s20, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg, bne_self_eq_false, Bool.or_false,
    show ((-1 : Int) < 551) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 551 (`decode_ldapr_aarch64_instrs_memory_ordered_rcpc`). -/
theorem run_LS_ldapr_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 23) % 2 = 1) (h4 : (w / 2 ^ 22) % 2 = 0) (h5 : (w / 2 ^ 21) % 2 = 1) (h6 : (w / 2 ^ 16) % 32 = 31) (h7 : (w / 2 ^ 15) % 2 = 1) (h8 : (w / 2 ^ 12) % 8 = 4) (h9 : (w / 2 ^ 10) % 4 = 0) (h10 : (w / 2 ^ 30) % 4 = 3) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_ldapr_aarch64_instrs_memory_ordered_rcpc (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 30 2)).run (s.set .SEE 551) := by
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
  have f100 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (28#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t105_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t105_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (929776#20 : BitVec 20)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have s16 : Sail.BitVec.access (BitVec.ofNat 32 w) 16 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s17 : Sail.BitVec.access (BitVec.ofNat 32 w) 17 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s18 : Sail.BitVec.access (BitVec.ofNat 32 w) 18 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s19 : Sail.BitVec.access (BitVec.ofNat 32 w) 19 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s20 : Sail.BitVec.access (BitVec.ofNat 32 w) 20 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f78, f79, f80, f81, f82, f85, f88, f91, f94, f97, f100, t105_0, t105_1, s16, s17, s18, s19, s20, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg, bne_self_eq_false, Bool.or_false,
    show ((-1 : Int) < 551) = True from by decide]
  all_goals rfl

end JanusASL.Proofs
