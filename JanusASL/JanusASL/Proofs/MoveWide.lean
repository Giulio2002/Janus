import JanusASL.Proofs.Step

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

def jMoveOp : MoveWideOp → Janus.Arm64.MoveWideOp
  | .MoveWideOp_N => .movn
  | .MoveWideOp_Z => .movz
  | .MoveWideOp_K => .movk

theorem updSub_eq {N : Nat} (x : BitVec N) (imm : BitVec 16) (p : Nat) :
    Sail.BitVec.updateSubrange x (((p : Int) + 15).toNat) p
        (BitVec.setWidth ((((p : Int) + 15).toNat - p + 1)) imm) =
      (x &&& ~~~(BitVec.ofNat N 0xFFFF <<< p)) ||| (BitVec.ofNat N imm.toNat <<< p) := by
  simp only [Sail.BitVec.updateSubrange]
  generalize hq : ((p : Int) + 15).toNat = q
  obtain rfl : q = p + 15 := by omega
  rw [show p + 15 - p + 1 = 16 by omega]
  simp only [Sail.BitVec.updateSubrange', BitVec.setWidth_eq]
  have h1 : (BitVec.allOnes 16).zeroExtend N = BitVec.ofNat N 0xFFFF := by
    apply BitVec.eq_of_toNat_eq; simp
  have h2 : imm.zeroExtend N = BitVec.ofNat N imm.toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [h1, h2, BitVec.and_comm]

theorem mw_NK : (MoveWideOp.MoveWideOp_N == MoveWideOp.MoveWideOp_K) = false := rfl
theorem mw_ZK : (MoveWideOp.MoveWideOp_Z == MoveWideOp.MoveWideOp_K) = false := rfl
theorem mw_KK : (MoveWideOp.MoveWideOp_K == MoveWideOp.MoveWideOp_K) = true := rfl
theorem mw_NN : (MoveWideOp.MoveWideOp_N == MoveWideOp.MoveWideOp_N) = true := rfl
theorem mw_ZN : (MoveWideOp.MoveWideOp_Z == MoveWideOp.MoveWideOp_N) = false := rfl
theorem mw_KN : (MoveWideOp.MoveWideOp_K == MoveWideOp.MoveWideOp_N) = false := rfl

set_option maxHeartbeats 4000000 in
theorem run_execute_movewide {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d : Nat} (hd : d < 32) (imm : BitVec 16) (op : MoveWideOp) (hv : Nat)
    (hp : hv * 16 + 15 < N) :
    ∃ s', (execute_aarch64_instrs_integer_ins_ext_insert_movewide d N imm op (hv * 16)).run s = .ok () s' ∧
      Rel (Janus.Arm64.execMoveWide N js (jMoveOp op) hv imm.toNat d) s' ∧ Frame s s' := by
  have ha : ((((hv * 16 : Nat) : Int) + 15) <b (N : Int)) = true := by simp; omega
  cases op
  · obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd hN (~~~(BitVec.ofNat N imm.toNat <<< (hv * 16)))
    refine ⟨s', ?_, by simpa [Janus.Arm64.execMoveWide, jMoveOp] using hr, hf⟩
    unfold execute_aarch64_instrs_integer_ins_ext_insert_movewide
    simp only [run_bind, run_undefined_bitvector, run_pure, run_sail_assert_of ha, updSub_eq, mw_NK, mw_ZK, mw_KK, mw_NN, mw_ZN, mw_KN,
      Bool.false_eq_true, ite_false, ite_true]
    simpa [Zeros, BitVec.zero] using hs'
  · obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd hN (BitVec.ofNat N imm.toNat <<< (hv * 16))
    refine ⟨s', ?_, by simpa [Janus.Arm64.execMoveWide, jMoveOp] using hr, hf⟩
    unfold execute_aarch64_instrs_integer_ins_ext_insert_movewide
    simp only [run_bind, run_undefined_bitvector, run_pure, run_sail_assert_of ha, updSub_eq, mw_NK, mw_ZK, mw_KK, mw_NN, mw_ZN, mw_KN,
      Bool.false_eq_true, ite_false, ite_true]
    simpa [Zeros, BitVec.zero] using hs'
  · obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd hN
      ((js.getX N d &&& ~~~(BitVec.ofNat N 0xFFFF <<< (hv * 16))) ||| (BitVec.ofNat N imm.toNat <<< (hv * 16)))
    refine ⟨s', ?_, by simpa [Janus.Arm64.execMoveWide, jMoveOp] using hr, hf⟩
    unfold execute_aarch64_instrs_integer_ins_ext_insert_movewide
    simp only [run_bind, run_undefined_bitvector, run_pure, run_sail_assert_of ha, updSub_eq, mw_NK, mw_ZK, mw_KK, mw_NN, mw_ZN, mw_KN,
      Bool.false_eq_true, ite_false, ite_true,
      run_X_read_rel h hd hN]
    simpa using hs'

theorem toNat_append_zeros4 (x : BitVec 2) : (x +++ (0b0000#4 : BitVec 4)).toNat = x.toNat * 16 := by
  show (x ++ 0#4).toNat = _
  rw [BitVec.toNat_append]; simp [Nat.shiftLeft_eq]

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 697 (`decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide`). -/
theorem run_DataProcImm_mw_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 23) % 64 = 37) (h1 : (w / 2 ^ 29) % 4 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide (fld w 0 5) (fld w 5 16) (fld w 21 2) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 697) := by
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
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (100#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (102#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (38#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (166#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (39#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (229#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t16_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (37#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, t16_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 697) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 698 (`decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide`). -/
theorem run_DataProcImm_mw_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 23) % 64 = 37) (h1 : (w / 2 ^ 29) % 4 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide (fld w 0 5) (fld w 5 16) (fld w 21 2) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 698) := by
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
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (100#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (102#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (38#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (166#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (39#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (229#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (37#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t17_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (165#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, t17_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 698) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 696 (`decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide`). -/
theorem run_DataProcImm_mw_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 23) % 64 = 37) (h1 : (w / 2 ^ 29) % 4 = 3) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide (fld w 0 5) (fld w 5 16) (fld w 21 2) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 696) := by
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
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (100#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (102#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (38#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (166#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (39#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t15_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (229#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, t15_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 696) = True from by decide]
  all_goals rfl


theorem run_decode_movn_mw (Rd : BitVec 5) (imm16 : BitVec 16) (hw : BitVec 2) (sf : BitVec 1)
    (hok : (sf == 0#1 && (Sail.BitVec.access hw 1 == 1#1)) = false) (s : SState) :
    (decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw 0#2 sf).run s =
      (execute_aarch64_instrs_integer_ins_ext_insert_movewide Rd.toNat (if sf == 1#1 then 64 else 32) imm16
        .MoveWideOp_N (hw.toNat * 16)).run s := by
  unfold decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide
  simp only [run_bind, run_pure, hok, Bool.false_eq_true, ite_false, toNat_append_zeros4]
  rfl

theorem run_decode_movz_mw (Rd : BitVec 5) (imm16 : BitVec 16) (hw : BitVec 2) (sf : BitVec 1)
    (hok : (sf == 0#1 && (Sail.BitVec.access hw 1 == 1#1)) = false) (s : SState) :
    (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw 2#2 sf).run s =
      (execute_aarch64_instrs_integer_ins_ext_insert_movewide Rd.toNat (if sf == 1#1 then 64 else 32) imm16
        .MoveWideOp_Z (hw.toNat * 16)).run s := by
  unfold decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide
  simp only [run_bind, run_pure, hok, Bool.false_eq_true, ite_false, toNat_append_zeros4]
  rfl

theorem run_decode_movk_mw (Rd : BitVec 5) (imm16 : BitVec 16) (hw : BitVec 2) (sf : BitVec 1)
    (hok : (sf == 0#1 && (Sail.BitVec.access hw 1 == 1#1)) = false) (s : SState) :
    (decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw 3#2 sf).run s =
      (execute_aarch64_instrs_integer_ins_ext_insert_movewide Rd.toNat (if sf == 1#1 then 64 else 32) imm16
        .MoveWideOp_K (hw.toNat * 16)).run s := by
  unfold decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide
  simp only [run_bind, run_pure, hok, Bool.false_eq_true, ite_false, toNat_append_zeros4]
  rfl


/-- Janus' operation for the class's `opc` field. -/
def mwOp (w : Nat) : Janus.Arm64.MoveWideOp :=
  if (w / 2 ^ 29) % 4 = 0 then .movn else if (w / 2 ^ 29) % 4 = 2 then .movz else .movk

theorem decode_moveWide_class {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100101)
    (hop : (w / 2 ^ 29) % 4 ≠ 1) (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0) :
    Janus.Arm64.decode w = some (.moveWide (Janus.Arm64.bit w 31) (mwOp w) (Janus.Arm64.bits w 22 21)
      (Janus.Arm64.bits w 20 5) (Janus.Arm64.bits w 4 0)) := by
  have h1 : ¬ w ≥ 2 ^ 32 := by omega
  have h2 : Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have h3 : Janus.Arm64.bits w 25 23 = 0b101 := by simp only [bits_def]; omega
  have h4 : ¬ Janus.Arm64.bits w 30 29 = 1 := by simp only [bits_def]; omega
  have h5 : (!Janus.Arm64.bit w 31 && decide (Janus.Arm64.bits w 22 21 ≥ 2)) = false := by
    simp only [bits_def, bit_def]; rcases hsf with e | e <;> simp [e] <;> omega
  have h6 : mwOp w = if Janus.Arm64.bits w 30 29 = 0 then .movn
      else if Janus.Arm64.bits w 30 29 = 2 then .movz else .movk := by
    simp only [mwOp, bits_def]
  simp only [Janus.Arm64.decode, h1, h2, ite_false, ite_true, Janus.Arm64.decodeDPImm, h3, h4, h5, h6]
  simp

theorem fld_eq_of {w lo len c : Nat} (hw : w < 2 ^ 32) (h : (w / 2 ^ lo) % 2 ^ len = c) :
    fld w lo len = BitVec.ofNat len c := by
  apply BitVec.eq_of_toNat_eq; rw [fld_toNat w lo len hw, ← h]; simp

theorem access1_of_lt (x : BitVec 2) (h : x.toNat < 2) : Sail.BitVec.access x 1 = 0#1 := by
  revert h; revert x; decide

set_option maxHeartbeats 8000000 in
theorem asl_moveWide {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100101)
    (hop : (w / 2 ^ 29) % 4 ≠ 1) (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execMoveWide (if fld w 31 1 == 1#1 then 64 else 32) js (mwOp w)
        (fld w 21 2).toNat (fld w 5 16).toNat (fld w 0 5).toNat) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  rw [run_DecodeA64_DPImm hw (by omega)]
  have hok : (fld w 31 1 == 0#1 && (Sail.BitVec.access (fld w 21 2) 1 == 1#1)) = false := by
    rcases hsf with e | e
    · rw [fld_eq_of hw (show (w / 2 ^ 31) % 2 ^ 1 = 1 by omega)]; simp
    · rw [access1_of_lt _ (by rw [fld_toNat w 21 2 hw]; omega)]; simp
  have hp : (fld w 21 2).toNat * 16 + 15 < (if fld w 31 1 == 1#1 then 64 else 32) := by
    have := fld_lt w 21 2
    rcases hsf with e | e
    · rw [fld_eq_of hw (show (w / 2 ^ 31) % 2 ^ 1 = 1 by omega)]; simp; omega
    · rw [fld_toNat w 21 2 hw]; split <;> omega
  rcases (show (w / 2 ^ 29) % 4 = 0 ∨ (w / 2 ^ 29) % 4 = 2 ∨ (w / 2 ^ 29) % 4 = 3 by omega) with hk | hk | hk
  · rw [run_DataProcImm_mw_0 hw hc hk (see_entry _ _), fld_eq_of hw (show (w / 2 ^ 29) % 2 ^ 2 = 0 by omega),
      run_decode_movn_mw _ _ _ _ hok]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_movewide (h.entry (BitVec.ofNat 32 w) 697) (width_cases w)
      (fld_lt w 0 5) (fld w 5 16) .MoveWideOp_N _ hp
    have e : mwOp w = .movn := by simp [mwOp, hk]
    exact ⟨s2, hrun, e ▸ hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcImm_mw_2 hw hc hk (see_entry _ _), fld_eq_of hw (show (w / 2 ^ 29) % 2 ^ 2 = 2 by omega),
      run_decode_movz_mw _ _ _ _ hok]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_movewide (h.entry (BitVec.ofNat 32 w) 698) (width_cases w)
      (fld_lt w 0 5) (fld w 5 16) .MoveWideOp_Z _ hp
    have e : mwOp w = .movz := by simp [mwOp, hk]
    exact ⟨s2, hrun, e ▸ hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcImm_mw_3 hw hc hk (see_entry _ _), fld_eq_of hw (show (w / 2 ^ 29) % 2 ^ 2 = 3 by omega),
      run_decode_movk_mw _ _ _ _ hok]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_movewide (h.entry (BitVec.ofNat 32 w) 696) (width_cases w)
      (fld_lt w 0 5) (fld w 5 16) .MoveWideOp_K _ hp
    have e : mwOp w = .movk := by simp [mwOp, hk]
    exact ⟨s2, hrun, e ▸ hrel, bt_cfg_after _ _ hfr⟩

/-- **MOVN/MOVZ/MOVK**: for every word of the encoding class (bits 28:23 = `100101`, `opc ≠ 01`,
`hw<1> = 0` when `sf = 0`) and every related pair of states, Janus' `step` and the generated ASL
agree. -/
theorem moveWide_agree {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100101)
    (hop : (w / 2 ^ 29) % 4 ≠ 1) (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execMoveWide N js (mwOp w)
    (fld w 21 2).toNat (fld w 5 16).toNat (fld w 0 5).toNat
  have hspec : ∀ N, (F N).pc = js.pc := by
    intro N; simp only [F, Janus.Arm64.execMoveWide]
    split <;> simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR] <;> split <;> rfl
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_moveWide hw hc hop hsf h (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_moveWide_class hw hc hop hsf)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw,
    bits_eq_fld w 22 21 hw, bits_eq_fld w 20 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, F]

end JanusASL.Proofs
