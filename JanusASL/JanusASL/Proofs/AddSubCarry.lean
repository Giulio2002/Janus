import JanusASL.Proofs.Step
import JanusASL.Proofs.AddSubImm

/-! # Proved: ADC/ADCS/SBC/SBCS, the whole encoding class

Words `sf op S 11010000 Rm 000000 Rn Rd` (bits 28:21 = `11010000`, bits 15:10 = `000000`; 2^17
words): the generated ASL step and Janus `step` agree on every related pair of states. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 6 (`decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry`). -/
theorem run_DataProcReg_carry_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 256 = 208) (h1 : (w / 2 ^ 10) % 64 = 0) (h2 : (w / 2 ^ 29) % 4 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 6) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t1_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t1_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (0#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, t1_0, t1_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 6) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 7 (`decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry`). -/
theorem run_DataProcReg_carry_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 256 = 208) (h1 : (w / 2 ^ 10) % 64 = 0) (h2 : (w / 2 ^ 29) % 4 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 7) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t2_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t2_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (0#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, t2_0, t2_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 7) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 8 (`decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry`). -/
theorem run_DataProcReg_carry_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 256 = 208) (h1 : (w / 2 ^ 10) % 64 = 0) (h2 : (w / 2 ^ 29) % 4 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 8) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t3_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t3_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (0#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, t3_0, t3_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 8) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 9 (`decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry`). -/
theorem run_DataProcReg_carry_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 256 = 208) (h1 : (w / 2 ^ 10) % 64 = 0) (h2 : (w / 2 ^ 29) % 4 = 3) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry (fld w 0 5) (fld w 5 5) (fld w 16 5) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 9) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t4_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t4_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (0#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, t4_0, t4_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 9) = True from by decide]
  all_goals rfl

theorem run_decode_adc_carry (Rd Rn Rm : BitVec 5) (S op sf : BitVec 1) (s : SState) :
    (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_carry Rd.toNat (if sf == 1#1 then 64 else 32)
        Rm.toNat Rn.toNat (S == 1#1) (op == 1#1)).run s := by
  unfold decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry
  all_goals rfl

theorem run_decode_adcs_carry (Rd Rn Rm : BitVec 5) (S op sf : BitVec 1) (s : SState) :
    (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_carry Rd.toNat (if sf == 1#1 then 64 else 32)
        Rm.toNat Rn.toNat (S == 1#1) (op == 1#1)).run s := by
  unfold decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry
  all_goals rfl

theorem run_decode_sbc_carry (Rd Rn Rm : BitVec 5) (S op sf : BitVec 1) (s : SState) :
    (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_carry Rd.toNat (if sf == 1#1 then 64 else 32)
        Rm.toNat Rn.toNat (S == 1#1) (op == 1#1)).run s := by
  unfold decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry
  all_goals rfl

theorem run_decode_sbcs_carry (Rd Rn Rm : BitVec 5) (S op sf : BitVec 1) (s : SState) :
    (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_carry Rd.toNat (if sf == 1#1 then 64 else 32)
        Rm.toNat Rn.toNat (S == 1#1) (op == 1#1)).run s := by
  unfold decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry
  all_goals rfl

set_option maxHeartbeats 4000000 in
theorem run_execute_carry {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d m n : Nat} (hd : d < 32) (hm : m < 32) (hn : n < 32) (S sub : Bool) :
    ∃ s', (execute_aarch64_instrs_integer_arithmetic_add_sub_carry d N m n S sub).run s = .ok () s' ∧
      Rel (Janus.Arm64.execAddSubCarry N js sub S m n d) s' ∧ Frame s s' := by
  obtain ⟨p, hp, hps⟩ := h.pstate
  have hN0 : 0 < N := by omega
  simp only [execute_aarch64_instrs_integer_arithmetic_add_sub_carry, run_bind, run_undefined_bitvector,
    run_X_read_rel h hn hN, run_X_read_rel h hm hN, run_readReg hp, hps.c, run_pure,
    AddWithCarry_eq hN0]
  unfold Janus.Arm64.execAddSubCarry
  dsimp only
  generalize Janus.Arm64.addWithCarry (js.getX N n) (if sub = true then ~~~js.getX N m else js.getX N m)
    js.flags.c = r
  cases S
  · simp only [Bool.false_eq_true, ite_false, run_pure]
    obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd hN r.1
    exact ⟨s', hs', hr, hf⟩
  · simp only [ite_true, run_bind, run_readReg hp, run_writeReg, run_readReg (get?_set_PSTATE _ _),
      nzcv_n, nzcv_z, nzcv_c, nzcv_v, SState.set_set]
    have hf := h.setFlags hp r.2
    obtain ⟨s', hs', hr, hfr⟩ := run_X_set_rel hf hd hN r.1
    refine ⟨s', hs', ?_, ?_⟩
    · have e : (js.setX d r.1).setFlags r.2 = (js.setFlags r.2).setX d r.1 := by
        simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR, Janus.Arm64.State.setFlags]; split <;> rfl
      rw [e]; exact hr
    · intro x hx h1 h2; rw [hfr x hx h1 h2]; exact get?_set_ne s _ (Ne.symm h2)

set_option maxHeartbeats 8000000 in
theorem asl_carry {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 256 = 0b11010000) (h2 : (w / 2 ^ 10) % 64 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execAddSubCarry (if fld w 31 1 == 1#1 then 64 else 32) js (fld w 30 1 == 1#1)
        (fld w 29 1 == 1#1) (fld w 16 5).toNat (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  rw [run_DecodeA64_DPReg hw (by omega)]
  rcases (show (w / 2 ^ 29) % 4 = 0 ∨ (w / 2 ^ 29) % 4 = 1 ∨ (w / 2 ^ 29) % 4 = 2 ∨ (w / 2 ^ 29) % 4 = 3 by omega)
    with hk | hk | hk | hk
  · rw [run_DataProcReg_carry_0 hw h1 h2 hk (see_entry _ _), run_decode_adc_carry]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_carry (h.entry (BitVec.ofNat 32 w) 6) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcReg_carry_1 hw h1 h2 hk (see_entry _ _), run_decode_adcs_carry]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_carry (h.entry (BitVec.ofNat 32 w) 7) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcReg_carry_2 hw h1 h2 hk (see_entry _ _), run_decode_sbc_carry]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_carry (h.entry (BitVec.ofNat 32 w) 8) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcReg_carry_3 hw h1 h2 hk (see_entry _ _), run_decode_sbcs_carry]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_carry (h.entry (BitVec.ofNat 32 w) 9) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩

/-- **ADC/ADCS/SBC/SBCS**: for every word of the encoding class and every related pair of states,
Janus' `step` and the generated ASL agree. -/
theorem addSubCarry_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 256 = 0b11010000)
    (h2 : (w / 2 ^ 10) % 64 = 0) {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  have hspec : ∀ N, (Janus.Arm64.execAddSubCarry N js (fld w 30 1 == 1#1) (fld w 29 1 == 1#1)
      (fld w 16 5).toNat (fld w 5 5).toNat (fld w 0 5).toNat).pc = js.pc := by
    intro N; unfold Janus.Arm64.execAddSubCarry; dsimp only
    split <;> simp [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR, Janus.Arm64.State.setFlags] <;> split <;> rfl
  refine step_agree h (asl_carry hw h1 h2 h _) (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_addSubCarry_class hw h1 h2)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, ← fld_bit w 30 hw, ← fld_bit w 29 hw,
    bits_eq_fld w 20 16 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next]

end JanusASL.Proofs
