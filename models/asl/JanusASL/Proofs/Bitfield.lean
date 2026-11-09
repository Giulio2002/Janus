import JanusASL.Proofs.LogicalImm

/-! # Proved: SBFM/BFM/UBFM, the whole encoding class

Words `sf opc 100110 N immr imms Rn Rd` (bits 28:23 = `100110`, `opc ≠ 11`) that Janus decodes:
`N = sf`, `immr, imms < 32` when `sf = 0`, `DecodeBitMasks(N, imms, immr, FALSE, datasize)`
defined. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem ror_eq {N : Nat} (hN : 0 < N) (x : BitVec N) (r : Nat) : ROR x r = x.rotateRight r := by
  rw [BitVec.rotateRight_def]
  unfold ROR
  have hm : r % N < N := Nat.mod_lt _ hN
  by_cases h0 : r = 0
  · subst h0; simp
  · have e : ((Sail.BitVec.length x : Int) - ((r % N : Nat) : Int)) = ((N - r % N : Nat) : Int) := by
      simp [Sail.BitVec.length]; omega
    simp only [show (r == 0) = false by simp [h0], Bool.false_eq_true, ite_false, Sail.BitVec.length] at e ⊢
    rw [show r.mod N = r % N from rfl, e]; rfl

theorem rep_eq {N : Nat} (x : BitVec N) (k : Nat) (hk : k < N) :
    BitVec.setWidth N (Sail.BitVec.replicateBits (Sail.BitVec.access x k) N) =
      if x.getLsbD k then BitVec.allOnes N else 0#N := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hb : (Sail.BitVec.access x k).getLsbD 0 = x.getLsbD k := by
    simp [Sail.BitVec.access, BitVec.getLsbD_eq_getElem hk, getElem!_pos x k hk]
  simp only [Sail.BitVec.replicateBits, BitVec.getLsbD_setWidth, BitVec.getLsbD_replicate, hi, decide_true,
    Bool.true_and, Nat.mod_one]
  rw [hb]
  cases x.getLsbD k <;> simp [hi] <;> omega

def bfInzero : Janus.Arm64.BitfieldOp → Bool
  | .bfm => false
  | _ => true

def bfExtend : Janus.Arm64.BitfieldOp → Bool
  | .sbfm => true
  | _ => false

/-- The result of `execBitfield`, with the masks given. -/
def bfVal (N : Nat) (s : Janus.Arm64.State) (opc : Janus.Arm64.BitfieldOp) (wmask tmask : BitVec N)
    (immr imms rn rd : Nat) : BitVec N :=
  let src := s.getX N rn
  let dst : BitVec N := if bfInzero opc then 0 else s.getX N rd
  let bot := (dst &&& ~~~wmask) ||| (src.rotateRight immr &&& wmask)
  let top : BitVec N := if bfExtend opc then (if src.getLsbD imms then BitVec.allOnes N else 0) else dst
  (top &&& ~~~tmask) ||| (bot &&& tmask)

set_option maxHeartbeats 4000000 in
theorem run_execute_bitfield {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d n r k : Nat} (hd : d < 32) (hn : n < 32) (hk : k < N)
    (opc : Janus.Arm64.BitfieldOp) (wmask tmask : BitVec N) :
    ∃ s', (execute_aarch64_instrs_integer_bitfield d N (bfExtend opc) (bfInzero opc) n r k tmask wmask).run s =
        .ok () s' ∧ Rel (js.setX d (bfVal N js opc wmask tmask r k n d)) s' ∧ Frame s s' := by
  have hN0 : 0 < N := by omega
  have ha : (decide (0 ≤ (k : Int)) && decide ((k : Int) < N)) = true := by simp; omega
  obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd hN (bfVal N js opc wmask tmask r k n d)
  refine ⟨s', ?_, hr, hf⟩
  cases opc <;>
  simp only [execute_aarch64_instrs_integer_bitfield, run_bind, run_X_read_rel h hn hN, run_X_read_rel h hd hN,
    run_pure, bfExtend, bfInzero, ite_true, ite_false, Bool.false_eq_true, run_sail_assert_of ha, ror_eq hN0]
  all_goals first
    | (simpa [bfVal, bfInzero, bfExtend, Zeros, BitVec.zero, rep_eq _ _ hk, run_sail_assert_of ha,
        run_sail_assert_of (show ((k : Int) <b (N : Int)) = true by simp; omega), hk, run_sail_assert_true] using hs')
    | (simp only [run_sail_assert_of ha, rep_eq _ _ hk]; simpa [bfVal, bfInzero, bfExtend, Zeros, BitVec.zero] using hs')

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 77 (`decode_sbfm_aarch64_instrs_integer_bitfield`). -/
theorem run_DataProcImm_bf_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 23) % 64 = 38) (h1 : (w / 2 ^ 29) % 4 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_sbfm_aarch64_instrs_integer_bitfield (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 6) (fld w 22 1) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 77) := by
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
  have t12_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (38#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, t12_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 77) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 76 (`decode_bfm_aarch64_instrs_integer_bitfield`). -/
theorem run_DataProcImm_bf_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 23) % 64 = 38) (h1 : (w / 2 ^ 29) % 4 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_bfm_aarch64_instrs_integer_bitfield (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 6) (fld w 22 1) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 76) := by
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
  have t11_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (102#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, t11_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 76) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 78 (`decode_ubfm_aarch64_instrs_integer_bitfield`). -/
theorem run_DataProcImm_bf_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 23) % 64 = 38) (h1 : (w / 2 ^ 29) % 4 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_ubfm_aarch64_instrs_integer_bitfield (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 6) (fld w 22 1) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 78) := by
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
  have t13_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (166#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, t13_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 78) = True from by decide]
  all_goals rfl


theorem run_decode_sbfm_bf (Rd Rn : BitVec 5) (imms immr : BitVec 6) (Nb sf : BitVec 1)
    (h1 : (sf == 1#1 && (Nb != 1#1)) = false)
    (h2 : (sf == 0#1 && (((Nb != 0#1) || (Sail.BitVec.access immr 5 != 0#1)) || (Sail.BitVec.access imms 5 != 0#1))) = false)
    {p : Nat × Nat}
    (hdbm : Janus.Arm64.decodeBitMasks (Nb == 1#1) imms.toNat immr.toNat false (if sf == 1#1 then 64 else 32) = some p)
    (s : SState) :
    (decode_sbfm_aarch64_instrs_integer_bitfield Rd Rn imms immr Nb 0#2 sf).run s =
      (execute_aarch64_instrs_integer_bitfield Rd.toNat (if sf == 1#1 then 64 else 32) (bfExtend .sbfm)
        (bfInzero .sbfm) Rn.toNat immr.toNat imms.toNat (BitVec.ofNat _ p.2) (BitVec.ofNat _ p.1)).run s := by
  have hD := run_DBM_janus (a := Nb) (b := imms) (c := immr) (width_cases' sf) hdbm
  unfold decode_sbfm_aarch64_instrs_integer_bitfield
  simp only [run_bind, run_undefined_bool, run_undefined_bitvector, h1, h2, Bool.false_eq_true, ite_false,
    run_pure, hD]
  rfl

theorem run_decode_bfm_bf (Rd Rn : BitVec 5) (imms immr : BitVec 6) (Nb sf : BitVec 1)
    (h1 : (sf == 1#1 && (Nb != 1#1)) = false)
    (h2 : (sf == 0#1 && (((Nb != 0#1) || (Sail.BitVec.access immr 5 != 0#1)) || (Sail.BitVec.access imms 5 != 0#1))) = false)
    {p : Nat × Nat}
    (hdbm : Janus.Arm64.decodeBitMasks (Nb == 1#1) imms.toNat immr.toNat false (if sf == 1#1 then 64 else 32) = some p)
    (s : SState) :
    (decode_bfm_aarch64_instrs_integer_bitfield Rd Rn imms immr Nb 1#2 sf).run s =
      (execute_aarch64_instrs_integer_bitfield Rd.toNat (if sf == 1#1 then 64 else 32) (bfExtend .bfm)
        (bfInzero .bfm) Rn.toNat immr.toNat imms.toNat (BitVec.ofNat _ p.2) (BitVec.ofNat _ p.1)).run s := by
  have hD := run_DBM_janus (a := Nb) (b := imms) (c := immr) (width_cases' sf) hdbm
  unfold decode_bfm_aarch64_instrs_integer_bitfield
  simp only [run_bind, run_undefined_bool, run_undefined_bitvector, h1, h2, Bool.false_eq_true, ite_false,
    run_pure, hD]
  rfl

theorem run_decode_ubfm_bf (Rd Rn : BitVec 5) (imms immr : BitVec 6) (Nb sf : BitVec 1)
    (h1 : (sf == 1#1 && (Nb != 1#1)) = false)
    (h2 : (sf == 0#1 && (((Nb != 0#1) || (Sail.BitVec.access immr 5 != 0#1)) || (Sail.BitVec.access imms 5 != 0#1))) = false)
    {p : Nat × Nat}
    (hdbm : Janus.Arm64.decodeBitMasks (Nb == 1#1) imms.toNat immr.toNat false (if sf == 1#1 then 64 else 32) = some p)
    (s : SState) :
    (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn imms immr Nb 2#2 sf).run s =
      (execute_aarch64_instrs_integer_bitfield Rd.toNat (if sf == 1#1 then 64 else 32) (bfExtend .ubfm)
        (bfInzero .ubfm) Rn.toNat immr.toNat imms.toNat (BitVec.ofNat _ p.2) (BitVec.ofNat _ p.1)).run s := by
  have hD := run_DBM_janus (a := Nb) (b := imms) (c := immr) (width_cases' sf) hdbm
  unfold decode_ubfm_aarch64_instrs_integer_bitfield
  simp only [run_bind, run_undefined_bool, run_undefined_bitvector, h1, h2, Bool.false_eq_true, ite_false,
    run_pure, hD]
  rfl

/-- Janus' operation for the class's `opc` field. -/
def bfOp (w : Nat) : Janus.Arm64.BitfieldOp :=
  if (w / 2 ^ 29) % 4 = 0 then .sbfm else if (w / 2 ^ 29) % 4 = 1 then .bfm else .ubfm

theorem decode_bitfield_class {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100110)
    (hop : (w / 2 ^ 29) % 4 ≠ 3) (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ ((w / 2 ^ 16) % 64 < 32 ∧ (w / 2 ^ 10) % 64 < 32)) {p : Nat × Nat}
    (hd : Janus.Arm64.decodeBitMasks (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 21 16)
      false (if Janus.Arm64.bit w 31 then 64 else 32) = some p) :
    Janus.Arm64.decode w = some (.bitfield (Janus.Arm64.bit w 31) (bfOp w) (Janus.Arm64.bit w 22)
      (Janus.Arm64.bits w 21 16) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
  have h1 : ¬ w ≥ 2 ^ 32 := by omega
  have h2 : Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have h3 : Janus.Arm64.bits w 25 23 = 0b110 := by simp only [bits_def]; omega
  have h4 : ¬ Janus.Arm64.bits w 30 29 = 3 := by simp only [bits_def]; omega
  have h5 : (Janus.Arm64.bit w 31 != Janus.Arm64.bit w 22) = false := by
    simp only [bit_def]; rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with e | e <;>
      simp [e] <;> omega
  have h6 : (!Janus.Arm64.bit w 31 && (decide (Janus.Arm64.bits w 21 16 ≥ 32) || decide (Janus.Arm64.bits w 15 10 ≥ 32))) = false := by
    simp only [bits_def, bit_def]; rcases hsf with e | ⟨e1, e2⟩
    · simp [e]
    · simp; omega
  have h7 : bfOp w = if Janus.Arm64.bits w 30 29 = 0 then .sbfm
      else if Janus.Arm64.bits w 30 29 = 1 then .bfm else .ubfm := by
    simp only [bfOp, bits_def]
  simp only [Janus.Arm64.decode, h1, h2, ite_false, ite_true, Janus.Arm64.decodeDPImm, h3, h4, h5, h6, hd, h7]
  simp

theorem bitfield_spec {N : Nat} (js : Janus.Arm64.State) (opc : Janus.Arm64.BitfieldOp) (Nbit : Bool)
    (immr imms rn rd : Nat) {p : Nat × Nat} (hd : Janus.Arm64.decodeBitMasks Nbit imms immr false N = some p) :
    Janus.Arm64.execBitfield N js opc Nbit immr imms rn rd =
      js.setX rd (bfVal N js opc (BitVec.ofNat N p.1) (BitVec.ofNat N p.2) immr imms rn rd) := by
  simp only [Janus.Arm64.execBitfield, bfVal, hd, Option.getD_some]
  cases opc <;> rfl

theorem access5_of_lt (x : BitVec 6) (h : x.toNat < 32) : Sail.BitVec.access x 5 = 0#1 := by
  revert h; revert x; decide

set_option maxHeartbeats 8000000 in
theorem asl_bitfield {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100110)
    (hop : (w / 2 ^ 29) % 4 ≠ 3) (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ ((w / 2 ^ 16) % 64 < 32 ∧ (w / 2 ^ 10) % 64 < 32)) {p : Nat × Nat}
    (hd : Janus.Arm64.decodeBitMasks (fld w 22 1 == 1#1) (fld w 10 6).toNat (fld w 16 6).toNat
      false (if fld w 31 1 == 1#1 then 64 else 32) = some p)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (js.setX (fld w 0 5).toNat (bfVal (if fld w 31 1 == 1#1 then 64 else 32) js (bfOp w)
        (BitVec.ofNat _ p.1) (BitVec.ofNat _ p.2) (fld w 16 6).toNat (fld w 10 6).toNat (fld w 5 5).toNat
        (fld w 0 5).toNat)) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  rw [run_DecodeA64_DPImm hw (by omega)]
  have e22 : fld w 22 1 = fld w 31 1 := by
    apply BitVec.eq_of_toNat_eq; rw [fld_toNat _ _ _ hw, fld_toNat _ _ _ hw]; simpa using hN.symm
  have h1 : (fld w 31 1 == 1#1 && (fld w 22 1 != 1#1)) = false := by
    rw [e22]; rcases fld_sf_cases hw with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> rfl
  have h2 : (fld w 31 1 == 0#1 && (((fld w 22 1 != 0#1) || (Sail.BitVec.access (fld w 16 6) 5 != 0#1)) ||
      (Sail.BitVec.access (fld w 10 6) 5 != 0#1))) = false := by
    rcases fld_sf_cases hw with ⟨e, _⟩ | ⟨e, e'⟩
    · rw [e]; rfl
    · rcases hsf with x | ⟨x1, x2⟩
      · omega
      · rw [e22, e, access5_of_lt _ (by rw [fld_toNat w 16 6 hw]; omega),
          access5_of_lt _ (by rw [fld_toNat w 10 6 hw]; omega)]; rfl
  have hk : (fld w 10 6).toNat < (if fld w 31 1 == 1#1 then 64 else 32) := by
    have := fld_lt w 10 6
    rcases fld_sf_cases hw with ⟨e, _⟩ | ⟨e, e'⟩
    · rw [e]; simp; omega
    · rw [e]; simp; rcases hsf with x | ⟨x1, x2⟩
      · omega
      · rw [fld_toNat w 10 6 hw]; omega
  rcases (show (w / 2 ^ 29) % 4 = 0 ∨ (w / 2 ^ 29) % 4 = 1 ∨ (w / 2 ^ 29) % 4 = 2 by omega) with hk1 | hk1 | hk1
  · rw [run_DataProcImm_bf_0 hw hc hk1 (see_entry _ _), fld_eq_of hw (show (w / 2 ^ 29) % 2 ^ 2 = 0 by omega),
      run_decode_sbfm_bf _ _ _ _ _ _ h1 h2 hd]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_bitfield (h.entry (BitVec.ofNat 32 w) 77) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 5 5) hk .sbfm _ _
    have e : bfOp w = .sbfm := by simp [bfOp, hk1]
    exact ⟨s2, hrun, e ▸ hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcImm_bf_1 hw hc hk1 (see_entry _ _), fld_eq_of hw (show (w / 2 ^ 29) % 2 ^ 2 = 1 by omega),
      run_decode_bfm_bf _ _ _ _ _ _ h1 h2 hd]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_bitfield (h.entry (BitVec.ofNat 32 w) 76) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 5 5) hk .bfm _ _
    have e : bfOp w = .bfm := by simp [bfOp, hk1]
    exact ⟨s2, hrun, e ▸ hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcImm_bf_2 hw hc hk1 (see_entry _ _), fld_eq_of hw (show (w / 2 ^ 29) % 2 ^ 2 = 2 by omega),
      run_decode_ubfm_bf _ _ _ _ _ _ h1 h2 hd]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_bitfield (h.entry (BitVec.ofNat 32 w) 78) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 5 5) hk .ubfm _ _
    have e : bfOp w = .ubfm := by simp [bfOp, hk1]
    exact ⟨s2, hrun, e ▸ hrel, bt_cfg_after _ _ hfr⟩

theorem bitfield_agree_f {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100110)
    (hop : (w / 2 ^ 29) % 4 ≠ 3) (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ ((w / 2 ^ 16) % 64 < 32 ∧ (w / 2 ^ 10) % 64 < 32))
    (hdbm : (Janus.Arm64.decodeBitMasks (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 21 16)
      false (if Janus.Arm64.bit w 31 then 64 else 32)).isSome = true)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') ∧ FPFrame s s' := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hdbm
  have hp' : Janus.Arm64.decodeBitMasks (fld w 22 1 == 1#1) (fld w 10 6).toNat (fld w 16 6).toNat
      false (if fld w 31 1 == 1#1 then 64 else 32) = some p := by
    rw [fld_bit w 22 hw, fld_bit w 31 hw, ← bits_eq_fld w 15 10 hw, ← bits_eq_fld w 21 16 hw]; exact hp
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_bitfield hw hc hop hN hsf hp' h (js.pc.toNat : Int)
  have hpc : ∀ {N : Nat} rd (v : BitVec N), (js.setX rd v).pc = js.pc := by
    intro N rd v; simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR]; split <;> rfl
  rcases fld_sf_cases hw with ⟨e1, _⟩ | ⟨e1, _⟩
  · rw [e1] at hrel
    have hrel' : Rel (js.setX (fld w 0 5).toNat (bfVal 64 js (bfOp w) (BitVec.ofNat 64 p.1) (BitVec.ofNat 64 p.2)
        (fld w 16 6).toNat (fld w 10 6).toNat (fld w 5 5).toNat (fld w 0 5).toNat)) s2 := hrel
    refine step_agree_f h ⟨s2, hrun, hrel', hbt⟩ (hpc _ _) ?_
    have hb : Janus.Arm64.bit w 31 = true := by rw [← fld_bit w 31 hw, e1]; rfl
    rw [Janus.Arm64.step_of_decode (decode_bitfield_class hw hc hop hN hsf hp)]
    simp only [hb, ite_true, ite_false, Bool.false_eq_true] at hp
    simp only [Janus.Arm64.exec, hb, ite_true, ite_false, Bool.false_eq_true]
    rw [bitfield_spec js _ _ _ _ _ _ hp]
    simp only [bits_eq_fld w 21 16 hw, bits_eq_fld w 15 10 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
    simp [Janus.Arm64.State.next, hpc]
  · rw [e1] at hrel
    have hrel' : Rel (js.setX (fld w 0 5).toNat (bfVal 32 js (bfOp w) (BitVec.ofNat 32 p.1) (BitVec.ofNat 32 p.2)
        (fld w 16 6).toNat (fld w 10 6).toNat (fld w 5 5).toNat (fld w 0 5).toNat)) s2 := hrel
    refine step_agree_f h ⟨s2, hrun, hrel', hbt⟩ (hpc _ _) ?_
    have hb : Janus.Arm64.bit w 31 = false := by rw [← fld_bit w 31 hw, e1]; rfl
    rw [Janus.Arm64.step_of_decode (decode_bitfield_class hw hc hop hN hsf hp)]
    simp only [hb, ite_true, ite_false, Bool.false_eq_true] at hp
    simp only [Janus.Arm64.exec, hb, ite_true, ite_false, Bool.false_eq_true]
    rw [bitfield_spec js _ _ _ _ _ _ hp]
    simp only [bits_eq_fld w 21 16 hw, bits_eq_fld w 15 10 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
    simp [Janus.Arm64.State.next, hpc]

/-- **SBFM/BFM/UBFM** (and their aliases: ASR/LSL/LSR imm, SXT*/UXT*, BFI/BFXIL, SBFIZ/UBFX, ...):
for every word of the encoding class that Janus decodes and every related pair of states, Janus'
`step` and the generated ASL agree. -/
theorem bitfield_agree {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100110)
    (hop : (w / 2 ^ 29) % 4 ≠ 3) (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ ((w / 2 ^ 16) % 64 < 32 ∧ (w / 2 ^ 10) % 64 < 32))
    (hdbm : (Janus.Arm64.decodeBitMasks (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 21 16)
      false (if Janus.Arm64.bit w 31 then 64 else 32)).isSome = true)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  obtain ⟨js', s', h1, h2, h3, h4, -⟩ := bitfield_agree_f (w := w) (hw := hw) (hc := hc) (hop := hop) (hN := hN) (hsf := hsf) (hdbm := hdbm) (js := js) (s := s) (h := h)
  exact ⟨js', s', h1, h2, h3, h4⟩

end JanusASL.Proofs
