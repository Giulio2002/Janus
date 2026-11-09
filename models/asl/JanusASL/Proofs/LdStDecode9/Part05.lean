-- JanusASL.Proofs.LdStDecode9, part 5 (tools/split_proofs.py)
import JanusASL.Proofs.Step


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 637 (`decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx`). -/
theorem run_LS_i9_1_0_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 0) (h4 : (w / 2 ^ 10) % 4 = 1) (h5 : (w / 2 ^ 30) % 4 = 0) (h6 : (w / 2 ^ 22) % 4 = 3) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (fld w 0 5) (fld w 5 5) (fld w 12 9) (fld w 22 2) (fld w 30 2)).run (s.set .SEE 637) := by
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
  have f80 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (120#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f103 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (217185#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f104 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (213089#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f107 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (929776#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f108 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1978352#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f110 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (202#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f111 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (714#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f112 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (51#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f113 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (179#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f114 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1228#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f116 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (200#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f117 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (712#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f121 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145407#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f122 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193983#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f124 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145375#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f125 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193951#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f127 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141279#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f128 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189855#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f131 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141311#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f132 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189887#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f138 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137215#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f139 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185791#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f141 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137183#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f142 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185759#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f144 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (64#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f145 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (576#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f149 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (25#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f150 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1739#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f151 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3569664#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f153 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (161#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f154 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (160#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f155 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (177#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f156 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (176#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f157 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (179#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f158 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (183#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f159 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (181#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f160 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (178#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f161 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (182#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f162 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (180#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f163 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (163#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f164 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (167#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f165 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (165#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f166 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (419#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f167 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (423#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f168 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (421#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f169 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (162#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f170 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (166#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f171 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (164#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f172 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (60#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f174 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (61#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f178 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (24#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f179 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (152#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f180 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (216#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f181 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (28#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f185 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (450#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f187 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (229#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f188 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (962#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f190 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (485#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t191_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (113#9 : BitVec 9)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t191_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t191_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (1#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f38, f39, f40, f42, f43, f44, f48, f52, f54, f55, f56, f57, f62, f63, f64, f66, f68, f70, f71, f72, f74, f76, f78, f80, f81, f103, f104, f107, f108, f110, f111, f112, f113, f114, f116, f117, f121, f122, f124, f125, f127, f128, f131, f132, f138, f139, f141, f142, f144, f145, f149, f150, f151, f153, f154, f155, f156, f157, f158, f159, f160, f161, f162, f163, f164, f165, f166, f167, f168, f169, f170, f171, f172, f174, f178, f179, f180, f181, f185, f187, f188, f190, t191_0, t191_1, t191_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 637) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 652 (`decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx`). -/
theorem run_LS_i9_1_1_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 0) (h4 : (w / 2 ^ 10) % 4 = 1) (h5 : (w / 2 ^ 30) % 4 = 1) (h6 : (w / 2 ^ 22) % 4 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (fld w 0 5) (fld w 5 5) (fld w 12 9) (fld w 22 2) (fld w 30 2)).run (s.set .SEE 652) := by
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
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f103 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (217185#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f104 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (213089#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f107 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (929776#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f108 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1978352#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f110 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (202#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f111 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (714#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f112 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (51#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f113 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (179#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f114 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1228#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f116 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (200#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f117 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (712#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f121 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145407#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f122 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193983#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f124 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145375#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f125 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193951#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f127 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141279#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f128 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189855#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f131 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141311#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f132 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189887#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f138 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137215#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f139 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185791#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f141 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137183#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f142 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185759#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f144 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (64#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f145 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (576#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f149 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (25#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f150 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1739#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f151 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3569664#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f153 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (161#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f154 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (160#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f155 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (177#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f156 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (176#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f157 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (179#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f158 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (183#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f159 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (181#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f160 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (178#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f161 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (182#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f162 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (180#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f163 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (163#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f164 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (167#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f165 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (165#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f166 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (419#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f167 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (423#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f168 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (421#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f169 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (162#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f170 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (166#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f171 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (164#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f172 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (60#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f174 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (61#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f178 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (24#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f179 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (152#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f180 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (216#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f181 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (28#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f185 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (450#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f187 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (229#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f188 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (962#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f190 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (485#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f191 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (113#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f193 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (115#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f194 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (241#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f196 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (243#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f197 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1476#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f199 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (742#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f203 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (448#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f205 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (228#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t206_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (960#11 : BitVec 11)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t206_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (1#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f38, f39, f40, f42, f43, f44, f48, f52, f54, f55, f56, f57, f62, f63, f64, f66, f68, f70, f71, f72, f74, f76, f78, f80, f81, f103, f104, f107, f108, f110, f111, f112, f113, f114, f116, f117, f121, f122, f124, f125, f127, f128, f131, f132, f138, f139, f141, f142, f144, f145, f149, f150, f151, f153, f154, f155, f156, f157, f158, f159, f160, f161, f162, f163, f164, f165, f166, f167, f168, f169, f170, f171, f172, f174, f178, f179, f180, f181, f185, f187, f188, f190, f191, f193, f194, f196, f197, f199, f203, f205, t206_0, t206_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 652) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 634 (`decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx`). -/
theorem run_LS_i9_1_1_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 0) (h4 : (w / 2 ^ 10) % 4 = 1) (h5 : (w / 2 ^ 30) % 4 = 1) (h6 : (w / 2 ^ 22) % 4 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (fld w 0 5) (fld w 5 5) (fld w 12 9) (fld w 22 2) (fld w 30 2)).run (s.set .SEE 634) := by
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
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f103 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (217185#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f104 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (213089#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f107 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (929776#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f108 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1978352#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f110 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (202#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f111 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (714#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f112 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (51#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f113 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (179#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f114 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1228#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f116 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (200#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f117 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (712#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f121 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145407#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f122 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193983#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f124 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145375#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f125 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193951#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f127 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141279#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f128 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189855#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f131 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141311#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f132 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189887#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f138 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137215#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f139 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185791#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f141 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137183#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f142 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185759#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f144 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (64#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f145 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (576#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f149 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (25#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f150 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1739#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f151 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3569664#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f153 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (161#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f154 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (160#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f155 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (177#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f156 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (176#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f157 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (179#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f158 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (183#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f159 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (181#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f160 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (178#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f161 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (182#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f162 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (180#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f163 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (163#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f164 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (167#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f165 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (165#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f166 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (419#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f167 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (423#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f168 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (421#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f169 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (162#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f170 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (166#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f171 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (164#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f172 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (60#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f174 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (61#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f178 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (24#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f179 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (152#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f180 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (216#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f181 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (28#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f185 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (450#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f187 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (229#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t188_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (962#11 : BitVec 11)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t188_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (1#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f38, f39, f40, f42, f43, f44, f48, f52, f54, f55, f56, f57, f62, f63, f64, f66, f68, f70, f71, f72, f74, f76, f78, f80, f81, f103, f104, f107, f108, f110, f111, f112, f113, f114, f116, f117, f121, f122, f124, f125, f127, f128, f131, f132, f138, f139, f141, f142, f144, f145, f149, f150, f151, f153, f154, f155, f156, f157, f158, f159, f160, f161, f162, f163, f164, f165, f166, f167, f168, f169, f170, f171, f172, f174, f178, f179, f180, f181, f185, f187, t188_0, t188_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 634) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 640 (`decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx`). -/
theorem run_LS_i9_1_1_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 0) (h4 : (w / 2 ^ 10) % 4 = 1) (h5 : (w / 2 ^ 30) % 4 = 1) (h6 : (w / 2 ^ 22) % 4 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (fld w 0 5) (fld w 5 5) (fld w 12 9) (fld w 22 2) (fld w 30 2)).run (s.set .SEE 640) := by
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
  have f81 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f103 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (217185#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f104 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (213089#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f107 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (929776#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f108 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1978352#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f110 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (202#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f111 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (714#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f112 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (51#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f113 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (179#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f114 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1228#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f116 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (200#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f117 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (712#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f121 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145407#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f122 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193983#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f124 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145375#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f125 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193951#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f127 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141279#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f128 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189855#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f131 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141311#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f132 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189887#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f138 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137215#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f139 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185791#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f141 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137183#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f142 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185759#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f144 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (64#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f145 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (576#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f149 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (25#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f150 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1739#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f151 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3569664#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f153 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (161#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f154 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (160#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f155 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (177#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f156 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (176#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f157 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (179#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f158 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (183#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f159 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (181#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f160 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (178#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f161 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (182#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f162 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (180#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f163 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (163#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f164 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (167#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f165 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (165#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f166 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (419#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f167 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (423#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f168 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (421#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f169 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (162#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f170 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (166#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f171 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 22 == (164#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f172 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (60#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f174 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (61#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f178 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (24#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f179 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (152#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f180 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (216#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f181 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (28#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f185 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (450#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f187 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (229#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f188 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (962#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f190 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (485#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f191 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (113#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f193 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (115#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t194_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 23 == (241#9 : BitVec 9)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t194_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t194_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (1#2 : BitVec 2)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f38, f39, f40, f42, f43, f44, f48, f52, f54, f55, f56, f57, f62, f63, f64, f66, f68, f70, f71, f72, f74, f76, f78, f80, f81, f103, f104, f107, f108, f110, f111, f112, f113, f114, f116, f117, f121, f122, f124, f125, f127, f128, f131, f132, f138, f139, f141, f142, f144, f145, f149, f150, f151, f153, f154, f155, f156, f157, f158, f159, f160, f161, f162, f163, f164, f165, f166, f167, f168, f169, f170, f171, f172, f174, f178, f179, f180, f181, f185, f187, f188, f190, f191, f193, t194_0, t194_1, t194_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 640) = True from by decide]
  all_goals rfl

end JanusASL.Proofs
