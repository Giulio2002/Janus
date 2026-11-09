-- JanusASL.Proofs.LdStDecodeA, part 35 (tools/split_proofs.py)
import JanusASL.Proofs.Step


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 1001 (`decode_swpb_aarch64_instrs_memory_atomicops_swp`). -/
theorem run_LS_at_10_10_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 1) (h4 : (w / 2 ^ 10) % 4 = 0) (h5 : (w / 2 ^ 15) % 2 = 1) (h6 : (w / 2 ^ 12) % 8 = 0) (h7 : (w / 2 ^ 23) % 2 = 1) (h8 : (w / 2 ^ 22) % 2 = 0) (h9 : (w / 2 ^ 30) % 4 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_swpb_aarch64_instrs_memory_atomicops_swp (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 22 1) (fld w 23 1) (fld w 30 2)).run (s.set .SEE 1001) := by
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
  have f191 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = false := by
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
  have f206 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (960#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f208 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (484#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f210 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (451#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f211 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (963#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f212 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (2#2 : BitVec 2)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f214 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1477#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f215 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1989#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f217 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (449#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f218 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (961#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f221 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (248#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f240 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1988#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f244 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (998#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f247 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (36#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f249 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (89#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f253 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (44#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f259 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (40#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f262 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (206#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f266 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (238#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f270 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1741#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f273 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (4067300#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f274 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1985#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f276 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1737#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f279 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3565568#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f280 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (418#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f281 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (422#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f282 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (420#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f284 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1743#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f290 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557376#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t292_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (56#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t292_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t292_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (32#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f38, f39, f40, f42, f43, f44, f48, f52, f54, f55, f56, f57, f62, f63, f64, f66, f68, f70, f71, f72, f74, f76, f78, f80, f81, f83, f86, f89, f92, f95, f98, f101, f103, f104, f107, f108, f110, f111, f112, f113, f114, f116, f117, f121, f122, f124, f125, f127, f128, f131, f132, f138, f139, f141, f142, f144, f145, f149, f150, f151, f153, f154, f155, f156, f157, f158, f159, f160, f161, f162, f163, f164, f165, f166, f167, f168, f169, f170, f171, f172, f174, f178, f179, f180, f181, f185, f187, f188, f190, f191, f193, f194, f196, f197, f199, f203, f205, f206, f208, f210, f211, f212, f214, f215, f217, f218, f221, f240, f244, f247, f249, f253, f259, f262, f266, f270, f273, f274, f276, f279, f280, f281, f282, f284, f290, t292_0, t292_1, t292_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 1001) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 1002 (`decode_swph_aarch64_instrs_memory_atomicops_swp`). -/
theorem run_LS_at_10_10_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 1) (h4 : (w / 2 ^ 10) % 4 = 0) (h5 : (w / 2 ^ 15) % 2 = 1) (h6 : (w / 2 ^ 12) % 8 = 0) (h7 : (w / 2 ^ 23) % 2 = 1) (h8 : (w / 2 ^ 22) % 2 = 0) (h9 : (w / 2 ^ 30) % 4 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_swph_aarch64_instrs_memory_atomicops_swp (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 22 1) (fld w 23 1) (fld w 30 2)).run (s.set .SEE 1002) := by
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
  have f194 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = false := by
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
  have f206 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (960#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f208 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (484#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f210 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (451#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f211 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (963#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f213 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (2#2 : BitVec 2)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f214 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1477#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f215 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1989#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f217 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (449#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f218 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (961#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f221 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (248#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f240 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1988#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f244 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (998#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f249 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (89#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f251 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (36#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f255 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (44#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f257 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (40#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f262 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (206#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f266 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (238#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f270 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1741#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f273 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (4067300#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f274 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1985#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f276 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1737#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f279 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3565568#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f280 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (418#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f281 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (422#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f282 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (420#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f284 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1743#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f290 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557376#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t293_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (120#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t293_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t293_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (32#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f38, f39, f40, f42, f43, f44, f48, f52, f54, f55, f56, f57, f62, f63, f64, f66, f68, f70, f71, f72, f74, f76, f78, f80, f81, f84, f87, f90, f93, f96, f99, f102, f103, f104, f107, f108, f110, f111, f112, f113, f114, f116, f117, f121, f122, f124, f125, f127, f128, f131, f132, f138, f139, f141, f142, f144, f145, f149, f150, f151, f153, f154, f155, f156, f157, f158, f159, f160, f161, f162, f163, f164, f165, f166, f167, f168, f169, f170, f171, f172, f174, f178, f179, f180, f181, f185, f187, f188, f190, f191, f193, f194, f196, f197, f199, f203, f205, f206, f208, f210, f211, f213, f214, f215, f217, f218, f221, f240, f244, f249, f251, f255, f257, f262, f266, f270, f273, f274, f276, f279, f280, f281, f282, f284, f290, t293_0, t293_1, t293_2, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 1002) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 1000 (`decode_swp_aarch64_instrs_memory_atomicops_swp`). -/
theorem run_LS_at_10_10_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 1) (h4 : (w / 2 ^ 10) % 4 = 0) (h5 : (w / 2 ^ 15) % 2 = 1) (h6 : (w / 2 ^ 12) % 8 = 0) (h7 : (w / 2 ^ 23) % 2 = 1) (h8 : (w / 2 ^ 22) % 2 = 0) (h9 : (w / 2 ^ 30) % 4 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_swp_aarch64_instrs_memory_atomicops_swp (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 22 1) (fld w 23 1) (fld w 30 2)).run (s.set .SEE 1000) := by
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
  have f105 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (929776#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f106 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (421890#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f107 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (929776#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f108 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1978352#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f109 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (202#9 : BitVec 9)) = false := by
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
  have f115 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (200#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f116 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (200#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f117 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (712#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f120 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (145407#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f121 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145407#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f122 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193983#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f123 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (145375#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f124 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145375#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f125 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193951#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f126 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (141279#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f127 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141279#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f128 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189855#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f129 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (141311#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f130 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (417794#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f131 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141311#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f132 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189887#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f133 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 15 == (4351#15 : BitVec 15)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f134 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 15 == (4350#15 : BitVec 15)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f135 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (65#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f137 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (137215#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f138 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137215#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f139 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185791#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f140 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (137183#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f141 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137183#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f142 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185759#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f143 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (64#9 : BitVec 9)) = false := by
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
  have f179 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (152#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f180 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (216#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f181 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (28#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f182 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (450#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f184 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (229#8 : BitVec 8)) = false := by
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
  have f200 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (448#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f202 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (228#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f203 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (448#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f205 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (228#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f206 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (960#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f208 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (484#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f209 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (451#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f210 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (451#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f211 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (963#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f214 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 11 10 == (2#2 : BitVec 2)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f215 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1989#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f216 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (449#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f217 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (449#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f218 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (961#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f221 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (248#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f240 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1988#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f244 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (998#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f249 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (89#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f262 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (206#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f266 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (238#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f270 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1741#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f273 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (4067300#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f274 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1985#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f276 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1737#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f279 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3565568#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f280 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (418#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f281 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (422#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f282 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (420#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f284 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1743#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f290 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557376#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t291_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t291_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (56#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t291_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t291_3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (32#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f78, f79, f80, f81, f82, f85, f88, f91, f94, f97, f100, f105, f106, f107, f108, f109, f110, f111, f112, f113, f114, f115, f116, f117, f120, f121, f122, f123, f124, f125, f126, f127, f128, f129, f130, f131, f132, f133, f134, f135, f137, f138, f139, f140, f141, f142, f143, f144, f145, f149, f150, f151, f153, f154, f155, f156, f157, f158, f159, f160, f161, f162, f163, f164, f165, f166, f167, f168, f169, f170, f171, f172, f174, f179, f180, f181, f182, f184, f185, f187, f188, f190, f191, f193, f194, f196, f197, f199, f200, f202, f203, f205, f206, f208, f209, f210, f211, f214, f215, f216, f217, f218, f221, f240, f244, f249, f262, f266, f270, f273, f274, f276, f279, f280, f281, f282, f284, f290, t291_0, t291_1, t291_2, t291_3, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 1000) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_LoadStore` on its encoding class reaches clause SEE 1000 (`decode_swp_aarch64_instrs_memory_atomicops_swp`). -/
theorem run_LS_at_10_10_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0) (h2 : (w / 2 ^ 24) % 4 = 0) (h3 : (w / 2 ^ 21) % 2 = 1) (h4 : (w / 2 ^ 10) % 4 = 0) (h5 : (w / 2 ^ 15) % 2 = 1) (h6 : (w / 2 ^ 12) % 8 = 0) (h7 : (w / 2 ^ 23) % 2 = 1) (h8 : (w / 2 ^ 22) % 2 = 0) (h9 : (w / 2 ^ 30) % 4 = 3) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s =
      (decode_swp_aarch64_instrs_memory_atomicops_swp (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 22 1) (fld w 23 1) (fld w 30 2)).run (s.set .SEE 1000) := by
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
  have f105 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (929776#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f106 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (421890#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f107 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (929776#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f108 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1978352#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f109 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (202#9 : BitVec 9)) = false := by
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
  have f115 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (200#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f116 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (200#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f117 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (712#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f120 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (145407#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f121 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145407#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f122 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193983#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f123 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (145375#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f124 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (145375#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f125 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1193951#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f126 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (141279#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f127 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141279#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f128 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189855#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f129 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (141311#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f130 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (417794#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f131 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (141311#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f132 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1189887#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f133 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 15 == (4351#15 : BitVec 15)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f134 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 15 == (4350#15 : BitVec 15)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f135 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (65#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f137 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (137215#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f138 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137215#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f139 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185791#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f140 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 10 == (137183#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f141 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (137183#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f142 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (1185759#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f143 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (64#9 : BitVec 9)) = false := by
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
  have f179 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (152#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f180 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (216#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f181 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (28#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f182 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (450#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f184 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (229#8 : BitVec 8)) = false := by
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
  have f200 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (448#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f202 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 22 == (228#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f203 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (448#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f205 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (228#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f206 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (960#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f208 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (484#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f209 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (451#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f210 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (451#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f211 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (963#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f214 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1477#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f215 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 14 14 == (1#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f216 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (449#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f217 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (449#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f218 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (961#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f221 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 10 10 == (1#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f240 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1988#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f244 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (998#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f249 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (89#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f262 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (206#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f266 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 21 == (238#9 : BitVec 9)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f270 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1741#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f273 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (4067300#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f274 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1985#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f276 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1737#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f279 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3565568#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f280 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (418#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f281 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (422#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f282 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (420#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f284 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1743#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f290 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3557376#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t291_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t291_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 29 24 == (56#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t291_2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t291_3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (32#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_LoadStore]
  simp only [run_bind, f0, f1, f2, f3, f4, f20, f36, f37, f78, f79, f80, f81, f82, f85, f88, f91, f94, f97, f100, f105, f106, f107, f108, f109, f110, f111, f112, f113, f114, f115, f116, f117, f120, f121, f122, f123, f124, f125, f126, f127, f128, f129, f130, f131, f132, f133, f134, f135, f137, f138, f139, f140, f141, f142, f143, f144, f145, f149, f150, f151, f153, f154, f155, f156, f157, f158, f159, f160, f161, f162, f163, f164, f165, f166, f167, f168, f169, f170, f171, f172, f174, f179, f180, f181, f182, f184, f185, f187, f188, f190, f191, f193, f194, f196, f197, f199, f200, f202, f203, f205, f206, f208, f209, f210, f211, f214, f215, f216, f217, f218, f221, f240, f244, f249, f262, f266, f270, f273, f274, f276, f279, f280, f281, f282, f284, f290, t291_0, t291_1, t291_2, t291_3, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 1000) = True from by decide]
  all_goals rfl

end JanusASL.Proofs
