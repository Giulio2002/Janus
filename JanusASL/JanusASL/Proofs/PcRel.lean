import JanusASL.Proofs.MoveWide

/-! # Proved: ADR/ADRP, the whole encoding class

Words `op immlo 10000 immhi Rd` (bits 28:24 = `10000`; 2^27 words). -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem page_eq (x : BitVec 64) :
    Sail.BitVec.updateSubrange x 11 0 (Zeros (n := 12)) = x &&& ~~~(0xFFF : BitVec 64) := by
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', Zeros, BitVec.zero]
  rw [BitVec.and_comm]
  have : ~~~((BitVec.allOnes (11 - 0 + 1)).zeroExtend 64 <<< 0) = ~~~(0xFFF : BitVec 64) := by decide
  rw [this]; simp

set_option maxHeartbeats 4000000 in
theorem run_execute_pcrel {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {d : Nat} (hd : d < 32)
    (imm : BitVec 64) (page : Bool) :
    ∃ s', (execute_aarch64_instrs_integer_arithmetic_address_pc_rel d imm page).run s = .ok () s' ∧
      Rel (js.writeZR d ((if page then js.pc &&& ~~~(0xFFF : BitVec 64) else js.pc) + imm)) s' ∧ Frame s s' := by
  obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd (Or.inr rfl)
    ((if page then js.pc &&& ~~~(0xFFF : BitVec 64) else js.pc) + imm)
  refine ⟨s', ?_, by simpa [Janus.Arm64.State.setX] using hr, hf⟩
  simp only [execute_aarch64_instrs_integer_arithmetic_address_pc_rel, PC_read, run_bind, run_readReg h.pc]
  cases page
  · simpa using hs'
  · simpa [page_eq] using hs'

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 34 (`decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel`). -/
theorem run_DataProcImm_adr_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 16) (h1 : (w / 2 ^ 31) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel (fld w 0 5) (fld w 5 19) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 34) := by
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
  have t5_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t5_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, t5_0, t5_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 34) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 35 (`decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel`). -/
theorem run_DataProcImm_adr_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 16) (h1 : (w / 2 ^ 31) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel (fld w 0 5) (fld w 5 19) (fld w 29 2) (fld w 31 1)).run (s.set .SEE 35) := by
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
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (0#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t6_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 31 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t6_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, t6_0, t6_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 35) = True from by decide]
  all_goals rfl


theorem run_decode_adr_pcrel (Rd : BitVec 5) (immhi : BitVec 19) (immlo : BitVec 2) (op : BitVec 1) (s : SState) :
    (decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi immlo op).run s =
      (execute_aarch64_instrs_integer_arithmetic_address_pc_rel Rd.toNat
        (if op == 1#1 then ((immhi ++ immlo) ++ 0#12).signExtend 64 else (immhi ++ immlo).signExtend 64)
        (op == 1#1)).run s := by
  unfold decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel
  simp only [run_bind, run_undefined_bitvector]
  rfl

theorem run_decode_adrp_pcrel (Rd : BitVec 5) (immhi : BitVec 19) (immlo : BitVec 2) (op : BitVec 1) (s : SState) :
    (decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi immlo op).run s =
      (execute_aarch64_instrs_integer_arithmetic_address_pc_rel Rd.toNat
        (if op == 1#1 then ((immhi ++ immlo) ++ 0#12).signExtend 64 else (immhi ++ immlo).signExtend 64)
        (op == 1#1)).run s := by
  unfold decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel
  simp only [run_bind, run_undefined_bitvector]
  rfl

theorem decode_pcrel_class {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 24) % 32 = 0b10000) :
    Janus.Arm64.decode w = some (.adr (Janus.Arm64.bit w 31) (Janus.Arm64.bits w 30 29) (Janus.Arm64.bits w 23 5)
      (Janus.Arm64.bits w 4 0)) := by
  have h1 : ¬ w ≥ 2 ^ 32 := by omega
  have h2 : Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have h3 : Janus.Arm64.bits w 25 23 / 2 = 0 := by simp only [bits_def]; omega
  simp only [Janus.Arm64.decode, h1, h2, ite_false, ite_true, Janus.Arm64.decodeDPImm, h3]

theorem imm_eq (w : Nat) (hw : w < 2 ^ 32) :
    (fld w 5 19 ++ fld w 29 2).signExtend 64 =
      Janus.Arm64.sext64 21 (Janus.Arm64.bits w 23 5 * 4 + Janus.Arm64.bits w 30 29) := by
  unfold Janus.Arm64.sext64
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, fld_toNat _ _ _ hw, fld_toNat _ _ _ hw, bits_def, bits_def,
    Nat.shiftLeft_eq]
  have : (w / 2 ^ 5 % 2 ^ 19 * 2 ^ 2 ||| w / 2 ^ 29 % 2 ^ 2) = w / 2 ^ 5 % 2 ^ 19 * 2 ^ 2 + w / 2 ^ 29 % 2 ^ 2 := by
    rw [← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [this]; omega

theorem immp_eq (w : Nat) (hw : w < 2 ^ 32) :
    ((fld w 5 19 ++ fld w 29 2) ++ 0#12).signExtend 64 =
      Janus.Arm64.sext64 33 ((Janus.Arm64.bits w 23 5 * 4 + Janus.Arm64.bits w 30 29) * 2 ^ 12) := by
  unfold Janus.Arm64.sext64
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_ofNat, fld_toNat _ _ _ hw, fld_toNat _ _ _ hw,
    bits_def, bits_def, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have : (w / 2 ^ 5 % 2 ^ 19 * 2 ^ 2 ||| w / 2 ^ 29 % 2 ^ 2) = w / 2 ^ 5 % 2 ^ 19 * 2 ^ 2 + w / 2 ^ 29 % 2 ^ 2 := by
    rw [← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [this, BitVec.toNat_ofNat, Nat.zero_mod, Nat.or_zero]; omega

/-- **ADR/ADRP**: for every word of the encoding class and every related pair of states, Janus'
`step` and the generated ASL agree. -/
theorem pcrel_agree {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 24) % 32 = 0b10000)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  have hpc : ∀ rd (v : BitVec 64), (js.writeZR rd v).pc = js.pc := by
    intro rd v; simp [Janus.Arm64.State.writeZR]; split <;> rfl
  rcases (show (w / 2 ^ 31) % 2 = 0 ∨ (w / 2 ^ 31) % 2 = 1 by omega) with e | e
  · have hb : Janus.Arm64.bit w 31 = false := by simp only [bit_def]; simp; omega
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_pcrel (h.entry (BitVec.ofNat 32 w) 34) (fld_lt w 0 5)
      (if fld w 31 1 == 1#1 then ((fld w 5 19 ++ fld w 29 2) ++ 0#12).signExtend 64 else (fld w 5 19 ++ fld w 29 2).signExtend 64)
      (fld w 31 1 == 1#1)
    have hasl : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 := by
      rw [run_DecodeA64_DPImm hw (by omega), run_DataProcImm_adr_0 hw hc e (see_entry _ _), run_decode_adr_pcrel]
      exact hrun
    refine step_agree h ⟨s2, hasl, hrel, bt_cfg_after _ _ hfr⟩ (hpc _ _) ?_
    · rw [Janus.Arm64.step_of_decode (decode_pcrel_class hw hc)]
      simp only [Janus.Arm64.exec, hb, ← fld_bit w 31 hw, bits_eq_fld w 4 0 hw, Bool.false_eq_true, ite_false]
      rw [← fld_bit w 31 hw] at hb
      simp [hb, ← imm_eq w hw, Janus.Arm64.State.next, hpc]
  · have hb : Janus.Arm64.bit w 31 = true := by simp only [bit_def]; simp; omega
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_pcrel (h.entry (BitVec.ofNat 32 w) 35) (fld_lt w 0 5)
      (if fld w 31 1 == 1#1 then ((fld w 5 19 ++ fld w 29 2) ++ 0#12).signExtend 64 else (fld w 5 19 ++ fld w 29 2).signExtend 64)
      (fld w 31 1 == 1#1)
    have hasl : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 := by
      rw [run_DecodeA64_DPImm hw (by omega), run_DataProcImm_adr_1 hw hc e (see_entry _ _), run_decode_adrp_pcrel]
      exact hrun
    refine step_agree h ⟨s2, hasl, hrel, bt_cfg_after _ _ hfr⟩ (hpc _ _) ?_
    · rw [Janus.Arm64.step_of_decode (decode_pcrel_class hw hc)]
      simp only [Janus.Arm64.exec, hb, bits_eq_fld w 4 0 hw, ite_true]
      rw [← fld_bit w 31 hw] at hb
      simp [hb, ← immp_eq w hw, Janus.Arm64.State.next, hpc]

end JanusASL.Proofs
