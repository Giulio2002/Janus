import JanusASL.Proofs.Config
import JanusASL.Proofs.Cond
import JanusASL.Proofs.MoveWide

/-! # Proved (under `LinuxEL0Config`): B, BL

`BranchTo` under the Linux EL0 configuration is `run_BranchTo` (Config.lean). -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem toNat_append_add {n m : Nat} (a : BitVec n) (b : BitVec m) :
    (a ++ b).toNat = a.toNat * 2 ^ m + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

theorem run_DecodeA64_BES {w : Nat} (hw : w < 2 ^ 32) (hcls : (w / 2 ^ 26) % 8 = 5) (pc : Int) (s : SState) :
    (__DecodeA64 pc (BitVec.ofNat 32 w)).run s = (__DecodeA64_BranchExcSys pc (BitVec.ofNat 32 w)).run s := by
  have e : ∀ c : Nat, c < 4 → (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 25 == BitVec.ofNat 4 c) = false := by
    intro c hc
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 26 == (0b100#3 : BitVec 3)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 26 == (0b101#3 : BitVec 3)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64]
  simp only [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e5, e6, Bool.and_false,
    Bool.false_eq_true, ite_false, ite_true]

/-- `janus_step` when the instruction branched: the PC is the branch target. -/
theorem run_janus_step_taken {s : SState} (w : BitVec 32) {pc : BitVec 64}
    (hpc : s.regs.get? ._PC = some pc) {s2 : SState}
    (hdec : (__DecodeA64 pc.toNat w).run (stepEntry s w) = .ok () s2)
    (hbt : s2.regs.get? .__BranchTaken = some true) :
    (janus_step w).run s = .ok .Janus_OK s2 := by
  have hpc1 : (stepEntry s w).regs.get? ._PC = some pc := by
    simp only [stepEntry]
    repeat rw [get?_set_ne _ _ (by decide)]
    exact hpc
  unfold janus_step
  have e1 : (__InstrEnc.__A64 == __InstrEnc.__A64 || __InstrEnc.__A64 == __InstrEnc.__A32) = true := by decide
  simp only [run_bind, run_writeReg, __DefaultCond, __SetThisInstrDetails, orM, toBool, run_pure,
    run_undefined_bitvector, e1, ite_true, run_sailTryCatch]
  rw [show (((((((s.set Register.__janus_exc_taken false).set Register.SEE (-1)).set Register.__BranchTaken false).set
            Register.__ExclusiveMonitorSet false).set Register.__ThisInstrEnc __InstrEnc.__A64).set Register.__ThisInstr w).set
            Register.__currentCond 14#4) = stepEntry s w from rfl]
  have e2 : (JanusOutcome.Janus_OK == JanusOutcome.Janus_OK) = true := by decide
  simp only [run_readReg hpc1, hdec, andM, toBool, run_pure, run_bind, e2, run_readReg hbt, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ite_false]

/-- The bookkeeping registers `stepEntry` writes. -/
def entryRegs : List Register :=
  [.__janus_exc_taken, .SEE, .__BranchTaken, .__ExclusiveMonitorSet, .__ThisInstrEnc, .__ThisInstr, .__currentCond]

theorem touches_stepEntry (s : SState) (w : BitVec 32) : Touches s (stepEntry s w) entryRegs := by
  unfold stepEntry
  exact Touches.refl s _ |>.set _ _ (by decide) |>.set _ _ (by decide) |>.set _ _ (by decide)
    |>.set _ _ (by decide) |>.set _ _ (by decide) |>.set _ _ (by decide) |>.set _ _ (by decide)

theorem LinuxEL0Config.stepEntry {s : SState} (h : LinuxEL0Config s) (w : BitVec 32) (n : Int) :
    LinuxEL0Config ((JanusASL.Proofs.stepEntry s w).set .SEE n) :=
  h.of_touches ((touches_stepEntry s w).set _ _ (by decide)) (by decide)

theorem brRegs_ok : ∀ r ∈ brRegs, isGprReg r = false ∧ r ≠ .SP_EL0 ∧ r ≠ .PSTATE := by decide

set_option maxHeartbeats 8000000 in
theorem run_execute_b {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hc : LinuxEL0Config s)
    (call : Bool) (off : BitVec 64) (ht : (js.pc + off).toNat < 2 ^ 56) :
    ∃ s', (execute_aarch64_instrs_branch_unconditional_immediate
        (if call then .BranchType_DIRCALL else .BranchType_DIR) off).run s = .ok () s' ∧
      Rel { (if call then js.writeZR 30 (js.pc + 4) else js) with pc := js.pc + off } s' ∧
      s'.regs.get? .__BranchTaken = some true ∧ LinuxEL0Config s' := by
  cases call
  · obtain ⟨s', hrun, hpc, hbt, htc⟩ := run_BranchTo hc (js.pc + off) ht .BranchType_DIR false
    refine ⟨s', ?_, h.touches htc brRegs_ok hpc, hbt, hc.of_touches htc brRegs_not_cfg⟩
    simp only [execute_aarch64_instrs_branch_unconditional_immediate, Bool.false_eq_true, ite_false, run_bind,
      run_pure, PC_read, run_readReg h.pc]
    simp only [show (BranchType.BranchType_DIR == BranchType.BranchType_DIRCALL) = false from rfl,
      Bool.false_eq_true, ite_false, run_pure, run_bind, run_readReg h.pc]
    exact hrun
  · have h1 := h.writeZR (d := 30) (by decide) (js.pc + 4#64)
    have hc1 := hc.setGpr (js.pc + 4#64) (d := 30) (by decide)
    have hpc1 : (setGpr s (js.pc + 4#64) 30).regs.get? ._PC = some js.pc := h1.pc
    obtain ⟨s', hrun, hpc, hbt, htc⟩ := run_BranchTo hc1 (js.pc + off) ht .BranchType_DIRCALL false
    refine ⟨s', ?_, h1.touches htc brRegs_ok hpc, hbt, hc1.of_touches htc brRegs_not_cfg⟩
    simp only [execute_aarch64_instrs_branch_unconditional_immediate, ite_true, run_bind,
      run_pure, PC_read, run_readReg h.pc]
    simp only [show (BranchType.BranchType_DIRCALL == BranchType.BranchType_DIRCALL) = true from rfl, ite_true,
      run_bind, run_pure, HaveGCS, run_IsFeatureImplemented hc, run_GCSPCREnabled hc]
    obtain ⟨p, hp, he, _, _⟩ := hc.pstate
    have e3 : Sail.BitVec.addInt js.pc 4 = js.pc + 4 := by
      apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.addInt]
    have hx : (X_set (30 : Int) 64 (js.pc + 4#64)).run s = .ok () (setGpr s (js.pc + 4#64) 30) :=
      run_X_set (s := s) (n := 30) (by decide) (Or.inr rfl) (js.pc + 4#64)
    cfg_simp [run_readReg hp, he, run_GCSPCREnabled hc, run_readReg h.pc, e3, run_IsFeatureImplemented hc, hx,
      run_readReg hpc1, hrun]

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_BranchExcSys` on its encoding class reaches clause SEE 67 (`decode_b_uncond_aarch64_instrs_branch_unconditional_immediate`). -/
theorem run_BranchExcSys_b_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 26) % 32 = 5) (h1 : (w / 2 ^ 31) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_BranchExcSys pc (BitVec.ofNat 32 w)).run s =
      (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate (fld w 0 26) (fld w 31 1)).run (s.set .SEE 67) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (BitVec.ofNat 32 w == (3573563487#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have t3_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (5#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_BranchExcSys]
  simp only [run_bind, f0, f1, f2, t3_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 67) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_BranchExcSys` on its encoding class reaches clause SEE 68 (`decode_bl_aarch64_instrs_branch_unconditional_immediate`). -/
theorem run_BranchExcSys_b_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 26) % 32 = 5) (h1 : (w / 2 ^ 31) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_BranchExcSys pc (BitVec.ofNat 32 w)).run s =
      (decode_bl_aarch64_instrs_branch_unconditional_immediate (fld w 0 26) (fld w 31 1)).run (s.set .SEE 68) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (BitVec.ofNat 32 w == (3573563487#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (5#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t4_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (37#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_BranchExcSys]
  simp only [run_bind, f0, f1, f2, f3, t4_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 68) = True from by decide]
  all_goals rfl


theorem run_decode_b (imm26 : BitVec 26) (op : BitVec 1) (s : SState) :
    (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 op).run s =
      (execute_aarch64_instrs_branch_unconditional_immediate
        (if (op == 1#1) then .BranchType_DIRCALL else .BranchType_DIR) ((imm26 ++ 0#2).signExtend 64)).run s := rfl

theorem run_decode_bl (imm26 : BitVec 26) (op : BitVec 1) (s : SState) :
    (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 op).run s =
      (execute_aarch64_instrs_branch_unconditional_immediate
        (if (op == 1#1) then .BranchType_DIRCALL else .BranchType_DIR) ((imm26 ++ 0#2).signExtend 64)).run s := rfl

theorem off26_eq (w : Nat) (hw : w < 2 ^ 32) :
    (fld w 0 26 ++ 0#2).signExtend 64 = Janus.Arm64.sext64 28 (Janus.Arm64.bits w 25 0 * 4) := by
  unfold Janus.Arm64.sext64
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, fld_toNat _ _ _ hw, bits_def, Nat.shiftLeft_eq]
  simp; omega

theorem decode_b_class {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 26) % 32 = 0b00101) :
    Janus.Arm64.decode w = some (.b (Janus.Arm64.bit w 31) (Janus.Arm64.bits w 25 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : Janus.Arm64.bits w 30 26 = 0b00101 := by simp only [bits_def]; omega
  simp only [Janus.Arm64.decode, a1, a2, a3, ite_false, ite_true, Janus.Arm64.decodeBranchSys, a4]
  simp

set_option maxHeartbeats 8000000 in
/-- **B, BL** (under `LinuxEL0Config`, to an untagged target): for every word of the class and
every related pair of states, Janus' `step` and the generated ASL agree, and the configuration is
preserved. -/
theorem b_agree {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 26) % 32 = 0b00101)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hcfg : LinuxEL0Config s)
    (ht : (js.pc + Janus.Arm64.sext64 28 (Janus.Arm64.bits w 25 0 * 4)).toNat < 2 ^ 56) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ LinuxEL0Config s' := by
  rw [← off26_eq w hw] at ht
  have hcall := fld_bit w 31 hw
  rcases (show (w / 2 ^ 31) % 2 = 0 ∨ (w / 2 ^ 31) % 2 = 1 by omega) with e | e
  · obtain ⟨s2, hrun, hrel, hbt, hcf⟩ := run_execute_b (h.entry (BitVec.ofNat 32 w) 67)
      (hcfg.stepEntry (BitVec.ofNat 32 w) 67) (fld w 31 1 == 1#1) _ ht
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        .ok () s2 := by
      rw [run_DecodeA64_BES hw (by omega), run_BranchExcSys_b_0 hw hc e (see_entry _ _), run_decode_b]
      exact hrun
    refine ⟨_, _, ?_, run_janus_step_taken _ h.pc hdec hbt, hrel, hcf⟩
    rw [Janus.Arm64.step_of_decode (decode_b_class hw hc)]
    rw [← hcall]
    simp only [Janus.Arm64.exec, off26_eq w hw]
    split <;> rfl
  · obtain ⟨s2, hrun, hrel, hbt, hcf⟩ := run_execute_b (h.entry (BitVec.ofNat 32 w) 68)
      (hcfg.stepEntry (BitVec.ofNat 32 w) 68) (fld w 31 1 == 1#1) _ ht
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        .ok () s2 := by
      rw [run_DecodeA64_BES hw (by omega), run_BranchExcSys_b_1 hw hc e (see_entry _ _), run_decode_bl]
      exact hrun
    refine ⟨_, _, ?_, run_janus_step_taken _ h.pc hdec hbt, hrel, hcf⟩
    rw [Janus.Arm64.step_of_decode (decode_b_class hw hc)]
    rw [← hcall]
    simp only [Janus.Arm64.exec, off26_eq w hw]
    split <;> rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_BranchExcSys` on its encoding class reaches clause SEE 69 (`decode_b_cond_aarch64_instrs_branch_conditional_cond`). -/
theorem run_BranchExcSys_bcond {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 256 = 84) (h1 : (w / 2 ^ 4) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_BranchExcSys pc (BitVec.ofNat 32 w)).run s =
      (decode_b_cond_aarch64_instrs_branch_conditional_cond (fld w 0 4) (fld w 5 19)).run (s.set .SEE 69) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (BitVec.ofNat 32 w == (3573563487#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (5#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (37#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t5_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t5_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 4 4 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_BranchExcSys]
  simp only [run_bind, f0, f1, f2, f3, f4, t5_0, t5_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 69) = True from by decide]
  all_goals rfl


theorem run_BranchNotTaken {s : SState} (h : LinuxEL0Config s) (bt : BranchType) (c : Bool) :
    (BranchNotTaken bt c).run s = .ok () s := by
  simp only [BranchNotTaken, run_bind, HaveStatisticalProfiling, run_IsFeatureImplemented h, __UNKNOWN_bits,
    run_undefined_bitvector, run_pure]
  simp (config := { decide := true }) only [cfgFeat, num_of_Feature, cfgFeaturesOff, List.contains, List.elem,
    Int.reduceToNat, Bool.not_false, ite_true]
  simp only [run_bind, run_undefined_bitvector]
  rw [run_SPEBranch h]
  rfl

theorem run_decode_bcond (cond : BitVec 4) (imm19 : BitVec 19) (s : SState) :
    (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19).run s =
      (execute_aarch64_instrs_branch_conditional_cond cond ((imm19 ++ 0#2).signExtend 64)).run s := rfl

theorem off19_eq (w : Nat) (hw : w < 2 ^ 32) :
    (fld w 5 19 ++ 0#2).signExtend 64 = Janus.Arm64.sext64 21 (Janus.Arm64.bits w 23 5 * 4) := by
  unfold Janus.Arm64.sext64
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, fld_toNat _ _ _ hw, bits_def, Nat.shiftLeft_eq]
  simp; omega

set_option maxHeartbeats 8000000 in
theorem run_execute_bcond {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hc : LinuxEL0Config s)
    (cond : BitVec 4) (off : BitVec 64)
    (ht : Janus.Arm64.conditionHolds cond.toNat js.flags = true → (js.pc + off).toNat < 2 ^ 56) :
    ∃ s', (execute_aarch64_instrs_branch_conditional_cond cond off).run s = .ok () s' ∧
      (if Janus.Arm64.conditionHolds cond.toNat js.flags then
        Rel { js with pc := js.pc + off } s' ∧ s'.regs.get? .__BranchTaken = some true
       else s' = s) ∧ LinuxEL0Config s' := by
  obtain ⟨p, hp, hps⟩ := h.pstate
  by_cases hcnd : Janus.Arm64.conditionHolds cond.toNat js.flags
  · obtain ⟨s', hrun, hpc, hbt, htc⟩ := run_BranchTo hc (js.pc + off) (ht hcnd) .BranchType_DIR true
    refine ⟨s', ?_, by rw [if_pos hcnd]; exact ⟨h.touches htc brRegs_ok hpc, hbt⟩, hc.of_touches htc brRegs_not_cfg⟩
    simp only [execute_aarch64_instrs_branch_conditional_cond, run_bind, run_ConditionHolds hp hps, hcnd, ite_true,
      PC_read, run_readReg h.pc]
    exact hrun
  · refine ⟨s, ?_, by rw [if_neg hcnd], hc⟩
    simp only [execute_aarch64_instrs_branch_conditional_cond, run_bind, run_ConditionHolds hp hps, hcnd,
      Bool.false_eq_true, ite_false]
    exact run_BranchNotTaken hc _ _

theorem decode_bcond_class {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 24) % 256 = 0b01010100)
    (h4 : (w / 2 ^ 4) % 2 = 0) :
    Janus.Arm64.decode w = some (.bcond (Janus.Arm64.bits w 23 5) (Janus.Arm64.bits w 3 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : ¬ Janus.Arm64.bits w 30 26 = 0b00101 := by simp only [bits_def]; omega
  have a5 : ¬ Janus.Arm64.bits w 30 25 = 0b011010 := by simp only [bits_def]; omega
  have a6 : ¬ Janus.Arm64.bits w 30 25 = 0b011011 := by simp only [bits_def]; omega
  have a7 : Janus.Arm64.bits w 31 24 = 0b01010100 := by simp only [bits_def]; omega
  have a8 : Janus.Arm64.bit w 4 = false := by simp only [bit_def]; simp; omega
  simp only [Janus.Arm64.decode, a1, a2, a3, ite_false, ite_true, Janus.Arm64.decodeBranchSys, a4, a5, a6, a7, a8]
  simp

set_option maxHeartbeats 8000000 in
/-- **B.cond** (under `LinuxEL0Config`, to an untagged target): Janus' `step` and the generated ASL
agree, taken or not, and the configuration is preserved. -/
theorem bcond_agree {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 24) % 256 = 0b01010100)
    (h4 : (w / 2 ^ 4) % 2 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hcfg : LinuxEL0Config s)
    (ht : Janus.Arm64.conditionHolds (Janus.Arm64.bits w 3 0) js.flags = true →
      (js.pc + Janus.Arm64.sext64 21 (Janus.Arm64.bits w 23 5 * 4)).toNat < 2 ^ 56) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ LinuxEL0Config s' := by
  rw [← off19_eq w hw, bits_eq_fld w 3 0 hw] at ht
  obtain ⟨s2, hrun, hres, hcf⟩ := run_execute_bcond (h.entry (BitVec.ofNat 32 w) 69)
    (hcfg.stepEntry (BitVec.ofNat 32 w) 69) (fld w 0 4) _ ht
  have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      .ok () s2 := by
    rw [run_DecodeA64_BES hw (by omega), run_BranchExcSys_bcond hw hc h4 (see_entry _ _), run_decode_bcond]
    exact hrun
  have hcond : (fld w 0 4).toNat = Janus.Arm64.bits w 3 0 := (bits_eq_fld w 3 0 hw).symm
  rw [Janus.Arm64.step_of_decode (decode_bcond_class hw hc h4)]
  simp only [Janus.Arm64.exec, ← hcond, ← off19_eq w hw]
  split
  · next hcnd =>
    rw [if_pos hcnd] at hres
    exact ⟨_, _, rfl, run_janus_step_taken _ h.pc hdec hres.2, hres.1, hcf⟩
  · next hcnd =>
    rw [if_neg hcnd] at hres
    subst hres
    have hR := h.entry (BitVec.ofNat 32 w) 69
    refine ⟨_, _, rfl, run_janus_step _ h.pc hdec ?_ hR.pc, hR.setPC _, ?_⟩
    · rw [get?_set_ne _ (r := .SEE) _ (by decide)]
      simp only [stepEntry]; repeat rw [get?_set_ne _ _ (by decide)]
      exact get?_set_BranchTaken _ _
    · exact hcf.of_touches (Touches.refl _ [._PC] |>.set _ _ (by decide)) (by decide)

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_BranchExcSys` on its encoding class reaches clause SEE 118 (`decode_cbz_aarch64_instrs_branch_conditional_compare`). -/
theorem run_BranchExcSys_cb_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 25) % 64 = 26) (h1 : (w / 2 ^ 24) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_BranchExcSys pc (BitVec.ofNat 32 w)).run s =
      (decode_cbz_aarch64_instrs_branch_conditional_compare (fld w 0 5) (fld w 5 19) (fld w 24 1) (fld w 31 1)).run (s.set .SEE 118) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (BitVec.ofNat 32 w == (3573563487#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (5#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (37#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3510208#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 25 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3508160#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 25 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3512256#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 11 == (1756129#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1697#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 8 == (13959972#24 : BitVec 24)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (BitVec.ofNat 32 w == (3573753119#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f16 : (BitVec.ofNat 32 w == (3573752543#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f17 : (BitVec.ofNat 32 w == (3573752479#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f18 : (BitVec.ofNat 32 w == (3573752031#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f19 : (BitVec.ofNat 32 w == (3573752351#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f20 : (BitVec.ofNat 32 w == (3573752447#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872498#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (BitVec.ofNat 32 w == (3573751839#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f23 : (BitVec.ofNat 32 w == (3573752383#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f24 : (BitVec.ofNat 32 w == (3573751967#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f25 : (BitVec.ofNat 32 w == (3573751999#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f26 : (BitVec.ofNat 32 w == (3573752415#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f27 : (BitVec.ofNat 32 w == (3573751903#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f28 : (BitVec.ofNat 32 w == (3573751935#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f29 : (BitVec.ofNat 32 w == (3573751871#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (53#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t31_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (52#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_BranchExcSys]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, t31_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 118) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_BranchExcSys` on its encoding class reaches clause SEE 117 (`decode_cbnz_aarch64_instrs_branch_conditional_compare`). -/
theorem run_BranchExcSys_cb_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 25) % 64 = 26) (h1 : (w / 2 ^ 24) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_BranchExcSys pc (BitVec.ofNat 32 w)).run s =
      (decode_cbnz_aarch64_instrs_branch_conditional_compare (fld w 0 5) (fld w 5 19) (fld w 24 1) (fld w 31 1)).run (s.set .SEE 117) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (BitVec.ofNat 32 w == (3573563487#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (5#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (37#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3510208#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 25 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3508160#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 25 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3512256#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 11 == (1756129#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1697#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 8 == (13959972#24 : BitVec 24)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (BitVec.ofNat 32 w == (3573753119#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f16 : (BitVec.ofNat 32 w == (3573752543#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f17 : (BitVec.ofNat 32 w == (3573752479#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f18 : (BitVec.ofNat 32 w == (3573752031#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f19 : (BitVec.ofNat 32 w == (3573752351#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f20 : (BitVec.ofNat 32 w == (3573752447#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872498#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (BitVec.ofNat 32 w == (3573751839#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f23 : (BitVec.ofNat 32 w == (3573752383#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f24 : (BitVec.ofNat 32 w == (3573751967#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f25 : (BitVec.ofNat 32 w == (3573751999#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f26 : (BitVec.ofNat 32 w == (3573752415#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f27 : (BitVec.ofNat 32 w == (3573751903#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f28 : (BitVec.ofNat 32 w == (3573751935#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f29 : (BitVec.ofNat 32 w == (3573751871#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have t30_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (53#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_BranchExcSys]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, t30_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 117) = True from by decide]
  all_goals rfl


theorem isZero_eq {N : Nat} (x : BitVec N) : IsZero x = decide (x = 0) := by
  simp only [IsZero, Sail.BitVec.length, BitVec.zero]
  cases x == 0#N <;> rfl

set_option maxHeartbeats 8000000 in
theorem run_execute_cb {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hc : LinuxEL0Config s)
    {N : Nat} (hN : N = 32 ∨ N = 64) {rt : Nat} (hrt : rt < 32) (iszero : Bool) (off : BitVec 64)
    (ht : (decide (js.getX N rt = 0) == iszero) = true → (js.pc + off).toNat < 2 ^ 56) :
    ∃ s', (execute_aarch64_instrs_branch_conditional_compare N iszero off rt).run s = .ok () s' ∧
      (if decide (js.getX N rt = 0) == iszero then
        Rel { js with pc := js.pc + off } s' ∧ s'.regs.get? .__BranchTaken = some true
       else s' = s) ∧ LinuxEL0Config s' := by
  by_cases hcnd : (decide (js.getX N rt = 0) == iszero) = true
  · obtain ⟨s', hrun, hpc, hbt, htc⟩ := run_BranchTo hc (js.pc + off) (ht hcnd) .BranchType_DIR true
    refine ⟨s', ?_, by rw [if_pos hcnd]; exact ⟨h.touches htc brRegs_ok hpc, hbt⟩, hc.of_touches htc brRegs_not_cfg⟩
    simp only [execute_aarch64_instrs_branch_conditional_compare, run_bind, run_X_read_rel h hrt hN, isZero_eq,
      hcnd, ite_true, PC_read, run_readReg h.pc, run_pure]
    exact hrun
  · refine ⟨s, ?_, by rw [if_neg hcnd], hc⟩
    simp only [execute_aarch64_instrs_branch_conditional_compare, run_bind, run_X_read_rel h hrt hN, isZero_eq,
      hcnd, Bool.false_eq_true, ite_false, run_pure]
    exact run_BranchNotTaken hc _ _

theorem run_decode_cbz (Rt : BitVec 5) (imm19 : BitVec 19) (op sf : BitVec 1) (s : SState) :
    (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 op sf).run s =
      (execute_aarch64_instrs_branch_conditional_compare (if sf == 1#1 then 64 else 32) (op == 0#1)
        ((imm19 ++ 0#2).signExtend 64) Rt.toNat).run s := rfl

theorem run_decode_cbnz (Rt : BitVec 5) (imm19 : BitVec 19) (op sf : BitVec 1) (s : SState) :
    (decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 op sf).run s =
      (execute_aarch64_instrs_branch_conditional_compare (if sf == 1#1 then 64 else 32) (op == 0#1)
        ((imm19 ++ 0#2).signExtend 64) Rt.toNat).run s := rfl

theorem decode_cb_class {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 25) % 64 = 0b011010) :
    Janus.Arm64.decode w = some (.cb (Janus.Arm64.bit w 31) (Janus.Arm64.bit w 24) (Janus.Arm64.bits w 23 5)
      (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : ¬ Janus.Arm64.bits w 30 26 = 0b00101 := by simp only [bits_def]; omega
  have a5 : Janus.Arm64.bits w 30 25 = 0b011010 := by simp only [bits_def]; omega
  simp only [Janus.Arm64.decode, a1, a2, a3, ite_false, ite_true, Janus.Arm64.decodeBranchSys, a4, a5]
  simp

set_option maxHeartbeats 8000000 in
/-- **CBZ, CBNZ** (under `LinuxEL0Config`, to an untagged target). -/
theorem cb_agree {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 25) % 64 = 0b011010)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hcfg : LinuxEL0Config s)
    (ht : ((if Janus.Arm64.bit w 31 then decide (js.getX 64 (Janus.Arm64.bits w 4 0) = 0)
        else decide (js.getX 32 (Janus.Arm64.bits w 4 0) = 0)) != Janus.Arm64.bit w 24) = true →
      (js.pc + Janus.Arm64.sext64 21 (Janus.Arm64.bits w 23 5 * 4)).toNat < 2 ^ 56) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ LinuxEL0Config s' := by
  have hsf : (fld w 31 1 == 1#1) = Janus.Arm64.bit w 31 := fld_bit w 31 hw
  have hop : (fld w 24 1 == 0#1) = !Janus.Arm64.bit w 24 := by
    rw [← fld_bit w 24 hw]; have := fld_lt w 24 1; generalize fld w 24 1 = v at this; revert v; decide
  have key : ((if Janus.Arm64.bit w 31 then decide (js.getX 64 (fld w 0 5).toNat = 0)
      else decide (js.getX 32 (fld w 0 5).toNat = 0)) != Janus.Arm64.bit w 24) =
      (decide (js.getX (if fld w 31 1 == 1#1 then 64 else 32) (fld w 0 5).toNat = 0) == (fld w 24 1 == 0#1)) := by
    rw [hop, hsf]
    cases Janus.Arm64.bit w 31 <;> cases Janus.Arm64.bit w 24 <;> simp
  rw [← off19_eq w hw, bits_eq_fld w 4 0 hw, key] at ht
  have hsee : ∃ n : Int, (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      (execute_aarch64_instrs_branch_conditional_compare (if fld w 31 1 == 1#1 then 64 else 32) (fld w 24 1 == 0#1)
        ((fld w 5 19 ++ 0#2).signExtend 64) (fld w 0 5).toNat).run ((stepEntry s (BitVec.ofNat 32 w)).set .SEE n) := by
    rcases (show (w / 2 ^ 24) % 2 = 0 ∨ (w / 2 ^ 24) % 2 = 1 by omega) with e | e
    · exact ⟨118, by rw [run_DecodeA64_BES hw (by omega), run_BranchExcSys_cb_0 hw hc e (see_entry _ _), run_decode_cbz]⟩
    · exact ⟨117, by rw [run_DecodeA64_BES hw (by omega), run_BranchExcSys_cb_1 hw hc e (see_entry _ _), run_decode_cbnz]⟩
  obtain ⟨n, hdec0⟩ := hsee
  obtain ⟨s2, hrun, hres, hcf⟩ := run_execute_cb (h.entry (BitVec.ofNat 32 w) n)
    (hcfg.stepEntry (BitVec.ofNat 32 w) n) (width_cases w) (fld_lt w 0 5) (fld w 24 1 == 0#1) _ ht
  have hdec := hdec0.trans hrun
  rw [Janus.Arm64.step_of_decode (decode_cb_class hw hc)]
  simp only [Janus.Arm64.exec, ← off19_eq w hw, bits_eq_fld w 4 0 hw]
  rw [key]
  by_cases hcnd : (decide (js.getX (if fld w 31 1 == 1#1 then 64 else 32) (fld w 0 5).toNat = 0) ==
      (fld w 24 1 == 0#1)) = true
  · rw [if_pos hcnd] at hres ⊢
    exact ⟨_, _, rfl, run_janus_step_taken _ h.pc hdec hres.2, hres.1, hcf⟩
  · rw [if_neg hcnd] at hres ⊢
    subst hres
    have hR := h.entry (BitVec.ofNat 32 w) n
    refine ⟨_, _, rfl, run_janus_step _ h.pc hdec ?_ hR.pc, hR.setPC _, ?_⟩
    · rw [get?_set_ne _ (r := .SEE) _ (by decide)]
      simp only [stepEntry]; repeat rw [get?_set_ne _ _ (by decide)]
      exact get?_set_BranchTaken _ _
    · exact hcf.of_touches (Touches.refl _ [._PC] |>.set _ _ (by decide)) (by decide)

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_BranchExcSys` on its encoding class reaches clause SEE 1010 (`decode_tbz_aarch64_instrs_branch_conditional_test`). -/
theorem run_BranchExcSys_tb_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 25) % 64 = 27) (h1 : (w / 2 ^ 24) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_BranchExcSys pc (BitVec.ofNat 32 w)).run s =
      (decode_tbz_aarch64_instrs_branch_conditional_test (fld w 0 5) (fld w 5 14) (fld w 19 5) (fld w 24 1) (fld w 31 1)).run (s.set .SEE 1010) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (BitVec.ofNat 32 w == (3573563487#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (5#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (37#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3510208#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 25 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3508160#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 25 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3512256#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 11 == (1756129#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1697#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 8 == (13959972#24 : BitVec 24)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (BitVec.ofNat 32 w == (3573753119#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f16 : (BitVec.ofNat 32 w == (3573752543#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f17 : (BitVec.ofNat 32 w == (3573752479#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f18 : (BitVec.ofNat 32 w == (3573752031#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f19 : (BitVec.ofNat 32 w == (3573752351#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f20 : (BitVec.ofNat 32 w == (3573752447#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872498#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (BitVec.ofNat 32 w == (3573751839#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f23 : (BitVec.ofNat 32 w == (3573752383#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f24 : (BitVec.ofNat 32 w == (3573751967#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f25 : (BitVec.ofNat 32 w == (3573751999#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f26 : (BitVec.ofNat 32 w == (3573752415#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f27 : (BitVec.ofNat 32 w == (3573751903#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f28 : (BitVec.ofNat 32 w == (3573751935#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f29 : (BitVec.ofNat 32 w == (3573751871#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (53#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (52#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (BitVec.ofNat 32 w == (3573563423#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872499#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1701#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1701#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1701#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872499#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (BitVec.ofNat 32 w == (3602842592#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872499#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f40 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872499#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f41 : (BitVec.ofNat 32 w == (3600745440#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f42 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 11 == (1758177#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1698#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1696#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f45 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872499#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f46 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 20 == (3415#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f47 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 20 == (3413#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 20 == (3411#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f49 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 20 == (3409#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f50 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 19 == (6816#13 : BitVec 13)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f51 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f52 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f53 : (BitVec.ofNat 32 w == (3573756159#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f54 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1696#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f55 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1696#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f56 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 19 == (6817#13 : BitVec 13)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f57 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 19 == (6821#13 : BitVec 13)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f58 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 19 == (6825#13 : BitVec 13)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f59 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (55#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t60_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (54#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_BranchExcSys]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, t60_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 1010) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_BranchExcSys` on its encoding class reaches clause SEE 1009 (`decode_tbnz_aarch64_instrs_branch_conditional_test`). -/
theorem run_BranchExcSys_tb_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 25) % 64 = 27) (h1 : (w / 2 ^ 24) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_BranchExcSys pc (BitVec.ofNat 32 w)).run s =
      (decode_tbnz_aarch64_instrs_branch_conditional_test (fld w 0 5) (fld w 5 14) (fld w 19 5) (fld w 24 1) (fld w 31 1)).run (s.set .SEE 1009) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (BitVec.ofNat 32 w == (3573563487#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (5#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (37#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3510208#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 25 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3508160#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 25 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3512256#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 11 == (1756129#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1697#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 8 == (13959972#24 : BitVec 24)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (BitVec.ofNat 32 w == (3573753119#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f16 : (BitVec.ofNat 32 w == (3573752543#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f17 : (BitVec.ofNat 32 w == (3573752479#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f18 : (BitVec.ofNat 32 w == (3573752031#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f19 : (BitVec.ofNat 32 w == (3573752351#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f20 : (BitVec.ofNat 32 w == (3573752447#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872498#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (BitVec.ofNat 32 w == (3573751839#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f23 : (BitVec.ofNat 32 w == (3573752383#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f24 : (BitVec.ofNat 32 w == (3573751967#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f25 : (BitVec.ofNat 32 w == (3573751999#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f26 : (BitVec.ofNat 32 w == (3573752415#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f27 : (BitVec.ofNat 32 w == (3573751903#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f28 : (BitVec.ofNat 32 w == (3573751935#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f29 : (BitVec.ofNat 32 w == (3573751871#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (53#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (52#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (BitVec.ofNat 32 w == (3573563423#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872499#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1701#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1701#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1701#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872499#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (BitVec.ofNat 32 w == (3602842592#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872499#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f40 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872499#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f41 : (BitVec.ofNat 32 w == (3600745440#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f42 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 11 == (1758177#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1698#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1696#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f45 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 12 == (872499#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f46 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 20 == (3415#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f47 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 20 == (3413#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 20 == (3411#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f49 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 20 == (3409#12 : BitVec 12)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f50 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 19 == (6816#13 : BitVec 13)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f51 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f52 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f53 : (BitVec.ofNat 32 w == (3573756159#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f54 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1696#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f55 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1696#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f56 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 19 == (6817#13 : BitVec 13)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f57 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 19 == (6821#13 : BitVec 13)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f58 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 19 == (6825#13 : BitVec 13)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t59_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (55#7 : BitVec 7)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_BranchExcSys]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, t59_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 1009) = True from by decide]
  all_goals rfl


set_option maxHeartbeats 8000000 in
theorem run_execute_tb {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hc : LinuxEL0Config s)
    {N : Nat} (hN : N = 32 ∨ N = 64) {rt : Nat} (hrt : rt < 32) {pos : Nat} (hpos : pos < N) (bv : BitVec 1)
    (off : BitVec 64)
    (ht : (Sail.BitVec.access (js.getX N rt) pos == bv) = true → (js.pc + off).toNat < 2 ^ 56) :
    ∃ s', (execute_aarch64_instrs_branch_conditional_test pos bv N off rt).run s = .ok () s' ∧
      (if (Sail.BitVec.access (js.getX N rt) pos == bv) then
        Rel { js with pc := js.pc + off } s' ∧ s'.regs.get? .__BranchTaken = some true
       else s' = s) ∧ LinuxEL0Config s' := by
  have ha : (pos <b N) = true := by simp; omega
  by_cases hcnd : (Sail.BitVec.access (js.getX N rt) pos == bv) = true
  · obtain ⟨s', hrun, hpc, hbt, htc⟩ := run_BranchTo hc (js.pc + off) (ht hcnd) .BranchType_DIR true
    refine ⟨s', ?_, by rw [if_pos hcnd]; exact ⟨h.touches htc brRegs_ok hpc, hbt⟩, hc.of_touches htc brRegs_not_cfg⟩
    simp only [execute_aarch64_instrs_branch_conditional_test, run_bind, run_X_read_rel h hrt hN,
      run_sail_assert_of ha, hcnd, ite_true, PC_read, run_readReg h.pc, run_pure]
    exact hrun
  · refine ⟨s, ?_, by rw [if_neg hcnd], hc⟩
    simp only [execute_aarch64_instrs_branch_conditional_test, run_bind, run_X_read_rel h hrt hN,
      run_sail_assert_of ha, hcnd, Bool.false_eq_true, ite_false, run_pure]
    exact run_BranchNotTaken hc _ _

theorem run_decode_tbz (Rt : BitVec 5) (imm14 : BitVec 14) (b40 : BitVec 5) (op b5 : BitVec 1) (s : SState) :
    (decode_tbz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b5).run s =
      (execute_aarch64_instrs_branch_conditional_test (b5 ++ b40).toNat op (if b5 == 1#1 then 64 else 32)
        ((imm14 ++ 0#2).signExtend 64) Rt.toNat).run s := rfl

theorem run_decode_tbnz (Rt : BitVec 5) (imm14 : BitVec 14) (b40 : BitVec 5) (op b5 : BitVec 1) (s : SState) :
    (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b5).run s =
      (execute_aarch64_instrs_branch_conditional_test (b5 ++ b40).toNat op (if b5 == 1#1 then 64 else 32)
        ((imm14 ++ 0#2).signExtend 64) Rt.toNat).run s := rfl

theorem off14_eq (w : Nat) (hw : w < 2 ^ 32) :
    (fld w 5 14 ++ 0#2).signExtend 64 = Janus.Arm64.sext64 16 (Janus.Arm64.bits w 18 5 * 4) := by
  unfold Janus.Arm64.sext64
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, fld_toNat _ _ _ hw, bits_def, Nat.shiftLeft_eq]
  simp; omega

theorem decode_tb_class {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 25) % 64 = 0b011011) :
    Janus.Arm64.decode w = some (.tb (Janus.Arm64.bit w 31) (Janus.Arm64.bit w 24) (Janus.Arm64.bits w 23 19)
      (Janus.Arm64.bits w 18 5) (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : ¬ Janus.Arm64.bits w 30 26 = 0b00101 := by simp only [bits_def]; omega
  have a5 : ¬ Janus.Arm64.bits w 30 25 = 0b011010 := by simp only [bits_def]; omega
  have a6 : Janus.Arm64.bits w 30 25 = 0b011011 := by simp only [bits_def]; omega
  simp only [Janus.Arm64.decode, a1, a2, a3, ite_false, ite_true, Janus.Arm64.decodeBranchSys, a4, a5, a6]
  simp

set_option maxHeartbeats 8000000 in
/-- **TBZ, TBNZ** (under `LinuxEL0Config`, to an untagged target). -/
theorem tb_agree {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 25) % 64 = 0b011011)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hcfg : LinuxEL0Config s)
    (ht : ((js.readZR (Janus.Arm64.bits w 4 0)).getLsbD ((Janus.Arm64.bit w 31).toNat * 32 +
        Janus.Arm64.bits w 23 19) == Janus.Arm64.bit w 24) = true →
      (js.pc + Janus.Arm64.sext64 16 (Janus.Arm64.bits w 18 5 * 4)).toNat < 2 ^ 56) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ LinuxEL0Config s' := by
  rw [← off14_eq w hw, bits_eq_fld w 4 0 hw] at ht
  have hsee : ∃ n : Int, (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      (execute_aarch64_instrs_branch_conditional_test (fld w 31 1 ++ fld w 19 5).toNat (fld w 24 1)
        (if fld w 31 1 == 1#1 then 64 else 32) ((fld w 5 14 ++ 0#2).signExtend 64) (fld w 0 5).toNat).run
        ((stepEntry s (BitVec.ofNat 32 w)).set .SEE n) := by
    rcases (show (w / 2 ^ 24) % 2 = 0 ∨ (w / 2 ^ 24) % 2 = 1 by omega) with e | e
    · exact ⟨1010, by rw [run_DecodeA64_BES hw (by omega), run_BranchExcSys_tb_0 hw hc e (see_entry _ _), run_decode_tbz]⟩
    · exact ⟨1009, by rw [run_DecodeA64_BES hw (by omega), run_BranchExcSys_tb_1 hw hc e (see_entry _ _), run_decode_tbnz]⟩
  obtain ⟨n, hdec0⟩ := hsee
  have hpos : (fld w 31 1 ++ fld w 19 5).toNat < (if fld w 31 1 == 1#1 then 64 else 32) := by
    have := fld_lt w 19 5
    rw [toNat_append_add]
    rcases (show (w / 2 ^ 31) % 2 = 0 ∨ (w / 2 ^ 31) % 2 = 1 by omega) with e | e
    · rw [fld_eq_of hw (show (w / 2 ^ 31) % 2 ^ 1 = 0 by omega)]; simp; omega
    · rw [fld_eq_of hw (show (w / 2 ^ 31) % 2 ^ 1 = 1 by omega)]; simp
      omega
  have key : ((js.readZR (fld w 0 5).toNat).getLsbD ((Janus.Arm64.bit w 31).toNat * 32 + Janus.Arm64.bits w 23 19) ==
      Janus.Arm64.bit w 24) =
      (Sail.BitVec.access (js.getX (if fld w 31 1 == 1#1 then 64 else 32) (fld w 0 5).toNat)
        (fld w 31 1 ++ fld w 19 5).toNat == fld w 24 1) := by
    have hpos' := hpos
    rw [← fld_bit w 24 hw, ← fld_bit w 31 hw, bits_eq_fld w 23 19 hw]
    have e1 : (fld w 31 1 ++ fld w 19 5).toNat = (fld w 31 1 == 1#1).toNat * 32 + (fld w 19 5).toNat := by
      rw [toNat_append_add]
      have hb : fld w 31 1 = 0#1 ∨ fld w 31 1 = 1#1 := by generalize fld w 31 1 = b; revert b; decide
      rcases hb with hb | hb <;> rw [hb] <;> simp
    rw [e1] at hpos' ⊢
    rw [show 23 + 1 - 19 = 5 from rfl]
    generalize ((fld w 31 1 == 1#1).toNat * 32 + (fld w 19 5).toNat) = q at hpos' ⊢
    simp only [Janus.Arm64.State.getX]
    generalize js.readZR (fld w 0 5).toNat = x
    have ha : ∀ {N : Nat}, q < N → Sail.BitVec.access (x.setWidth N) q = BitVec.ofBool (x.getLsbD q) := by
      intro N hq
      simp [Sail.BitVec.access, getElem!_pos (x.setWidth N) q hq, BitVec.getElem_setWidth, hq,
        BitVec.getLsbD_eq_getElem]
    rw [ha hpos']
    have hb : fld w 24 1 = 0#1 ∨ fld w 24 1 = 1#1 := by generalize fld w 24 1 = b; revert b; decide
    rcases hb with hb | hb <;> rw [hb] <;> cases x.getLsbD q <;> rfl
  rw [key] at ht
  obtain ⟨s2, hrun, hres, hcf⟩ := run_execute_tb (h.entry (BitVec.ofNat 32 w) n)
    (hcfg.stepEntry (BitVec.ofNat 32 w) n) (width_cases w) (fld_lt w 0 5) hpos (fld w 24 1) _ ht
  have hdec := hdec0.trans hrun
  rw [Janus.Arm64.step_of_decode (decode_tb_class hw hc)]
  simp only [Janus.Arm64.exec, ← off14_eq w hw, bits_eq_fld w 4 0 hw]
  rw [key]
  by_cases hcnd : (Sail.BitVec.access (js.getX (if fld w 31 1 == 1#1 then 64 else 32) (fld w 0 5).toNat)
        (fld w 31 1 ++ fld w 19 5).toNat == fld w 24 1) = true
  · rw [if_pos hcnd] at hres ⊢
    exact ⟨_, _, rfl, run_janus_step_taken _ h.pc hdec hres.2, hres.1, hcf⟩
  · rw [if_neg hcnd] at hres ⊢
    subst hres
    have hR := h.entry (BitVec.ofNat 32 w) n
    refine ⟨_, _, rfl, run_janus_step _ h.pc hdec ?_ hR.pc, hR.setPC _, ?_⟩
    · rw [get?_set_ne _ (r := .SEE) _ (by decide)]
      simp only [stepEntry]; repeat rw [get?_set_ne _ _ (by decide)]
      exact get?_set_BranchTaken _ _
    · exact hcf.of_touches (Touches.refl _ [._PC] |>.set _ _ (by decide)) (by decide)

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_BranchExcSys` on its encoding class reaches clause SEE 92 (`decode_br_aarch64_instrs_branch_unconditional_register`). -/
theorem run_BranchExcSys_br {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 10) % 4194304 = 3508160) (h1 : (w / 2 ^ 0) % 32 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_BranchExcSys pc (BitVec.ofNat 32 w)).run s =
      (decode_br_aarch64_instrs_branch_unconditional_register (fld w 0 5) (fld w 5 5) (fld w 10 1) (fld w 11 1) (fld w 21 2) (fld w 24 1)).run (s.set .SEE 92) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (BitVec.ofNat 32 w == (3573563487#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (5#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (37#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3510208#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 23 11 == (2017#13 : BitVec 13)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t9_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3508160#22 : BitVec 22)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t9_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 4 0 == (0#5 : BitVec 5)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_BranchExcSys]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, t9_0, t9_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 92) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_BranchExcSys` on its encoding class reaches clause SEE 90 (`decode_blr_aarch64_instrs_branch_unconditional_register`). -/
theorem run_BranchExcSys_blr {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 10) % 4194304 = 3510208) (h1 : (w / 2 ^ 0) % 32 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_BranchExcSys pc (BitVec.ofNat 32 w)).run s =
      (decode_blr_aarch64_instrs_branch_unconditional_register (fld w 0 5) (fld w 5 5) (fld w 10 1) (fld w 11 1) (fld w 21 2) (fld w 24 1)).run (s.set .SEE 90) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (BitVec.ofNat 32 w == (3573563487#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (5#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (37#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t7_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3510208#22 : BitVec 22)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t7_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 4 0 == (0#5 : BitVec 5)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_BranchExcSys]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, t7_0, t7_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 90) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_BranchExcSys` on its encoding class reaches clause SEE 94 (`decode_ret_aarch64_instrs_branch_unconditional_register`). -/
theorem run_BranchExcSys_ret {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 10) % 4194304 = 3512256) (h1 : (w / 2 ^ 0) % 32 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_BranchExcSys pc (BitVec.ofNat 32 w)).run s =
      (decode_ret_aarch64_instrs_branch_unconditional_register (fld w 0 5) (fld w 5 5) (fld w 10 1) (fld w 11 1) (fld w 21 2) (fld w 24 1)).run (s.set .SEE 94) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3489992#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (BitVec.ofNat 32 w == (3573563487#32 : BitVec 32)) = false := by
    exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (5#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 26 == (37#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 24 == (84#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3510208#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 23 11 == (2017#13 : BitVec 13)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3508160#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 23 11 == (993#13 : BitVec 13)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t11_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3512256#22 : BitVec 22)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t11_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 4 0 == (0#5 : BitVec 5)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_BranchExcSys]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, t11_0, t11_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 94) = True from by decide]
  all_goals rfl


/-- `BranchType` equalities, as the generated `BEq` computes them. -/
@[local simp] theorem bt_beq_BranchType_DIR_BranchType_DIR : (BranchType.BranchType_DIR == BranchType.BranchType_DIR) = true := rfl
@[local simp] theorem bt_beq_BranchType_DIR_BranchType_DIRCALL : (BranchType.BranchType_DIR == BranchType.BranchType_DIRCALL) = false := rfl
@[local simp] theorem bt_beq_BranchType_DIR_BranchType_INDIR : (BranchType.BranchType_DIR == BranchType.BranchType_INDIR) = false := rfl
@[local simp] theorem bt_beq_BranchType_DIR_BranchType_INDCALL : (BranchType.BranchType_DIR == BranchType.BranchType_INDCALL) = false := rfl
@[local simp] theorem bt_beq_BranchType_DIR_BranchType_RET : (BranchType.BranchType_DIR == BranchType.BranchType_RET) = false := rfl
@[local simp] theorem bt_beq_BranchType_DIRCALL_BranchType_DIR : (BranchType.BranchType_DIRCALL == BranchType.BranchType_DIR) = false := rfl
@[local simp] theorem bt_beq_BranchType_DIRCALL_BranchType_DIRCALL : (BranchType.BranchType_DIRCALL == BranchType.BranchType_DIRCALL) = true := rfl
@[local simp] theorem bt_beq_BranchType_DIRCALL_BranchType_INDIR : (BranchType.BranchType_DIRCALL == BranchType.BranchType_INDIR) = false := rfl
@[local simp] theorem bt_beq_BranchType_DIRCALL_BranchType_INDCALL : (BranchType.BranchType_DIRCALL == BranchType.BranchType_INDCALL) = false := rfl
@[local simp] theorem bt_beq_BranchType_DIRCALL_BranchType_RET : (BranchType.BranchType_DIRCALL == BranchType.BranchType_RET) = false := rfl
@[local simp] theorem bt_beq_BranchType_INDIR_BranchType_DIR : (BranchType.BranchType_INDIR == BranchType.BranchType_DIR) = false := rfl
@[local simp] theorem bt_beq_BranchType_INDIR_BranchType_DIRCALL : (BranchType.BranchType_INDIR == BranchType.BranchType_DIRCALL) = false := rfl
@[local simp] theorem bt_beq_BranchType_INDIR_BranchType_INDIR : (BranchType.BranchType_INDIR == BranchType.BranchType_INDIR) = true := rfl
@[local simp] theorem bt_beq_BranchType_INDIR_BranchType_INDCALL : (BranchType.BranchType_INDIR == BranchType.BranchType_INDCALL) = false := rfl
@[local simp] theorem bt_beq_BranchType_INDIR_BranchType_RET : (BranchType.BranchType_INDIR == BranchType.BranchType_RET) = false := rfl
@[local simp] theorem bt_beq_BranchType_INDCALL_BranchType_DIR : (BranchType.BranchType_INDCALL == BranchType.BranchType_DIR) = false := rfl
@[local simp] theorem bt_beq_BranchType_INDCALL_BranchType_DIRCALL : (BranchType.BranchType_INDCALL == BranchType.BranchType_DIRCALL) = false := rfl
@[local simp] theorem bt_beq_BranchType_INDCALL_BranchType_INDIR : (BranchType.BranchType_INDCALL == BranchType.BranchType_INDIR) = false := rfl
@[local simp] theorem bt_beq_BranchType_INDCALL_BranchType_INDCALL : (BranchType.BranchType_INDCALL == BranchType.BranchType_INDCALL) = true := rfl
@[local simp] theorem bt_beq_BranchType_INDCALL_BranchType_RET : (BranchType.BranchType_INDCALL == BranchType.BranchType_RET) = false := rfl
@[local simp] theorem bt_beq_BranchType_RET_BranchType_DIR : (BranchType.BranchType_RET == BranchType.BranchType_DIR) = false := rfl
@[local simp] theorem bt_beq_BranchType_RET_BranchType_DIRCALL : (BranchType.BranchType_RET == BranchType.BranchType_DIRCALL) = false := rfl
@[local simp] theorem bt_beq_BranchType_RET_BranchType_INDIR : (BranchType.BranchType_RET == BranchType.BranchType_INDIR) = false := rfl
@[local simp] theorem bt_beq_BranchType_RET_BranchType_INDCALL : (BranchType.BranchType_RET == BranchType.BranchType_INDCALL) = false := rfl
@[local simp] theorem bt_beq_BranchType_RET_BranchType_RET : (BranchType.BranchType_RET == BranchType.BranchType_RET) = true := rfl

/-- The `BTYPE` value an indirect branch of type `bt` sets (not in a guarded page). -/
def btypeOf : BranchType → BitVec 2
  | .BranchType_INDIR => 0b01#2
  | .BranchType_INDCALL => 0b10#2
  | _ => 0b00#2

set_option maxHeartbeats 8000000 in
theorem run_execute_bru {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hc : LinuxEL0Config s)
    (bt : BranchType) (hbt : bt = .BranchType_INDIR ∨ bt = .BranchType_INDCALL ∨ bt = .BranchType_RET)
    {n : Nat} (hn : n < 32) (ht : (js.readZR n).toNat < 2 ^ 56) :
    ∃ s', (execute_aarch64_instrs_branch_unconditional_register bt 0 n false false true).run s = .ok () s' ∧
      Rel { (if bt == .BranchType_INDCALL then js.writeZR 30 (js.pc + 4) else js) with pc := js.readZR n } s' ∧
      s'.regs.get? .__BranchTaken = some true ∧ LinuxEL0Config s' := by
  obtain ⟨p, hp, he, _, _⟩ := hc.pstate
  have hx := run_X_read_rel h hn (N := 64) (Or.inr rfl)
  simp only [Janus.Arm64.State.getX, BitVec.setWidth_eq] at hx
  rcases hbt with rfl | rfl | rfl
  · have hb : Touches s (s.set .BTypeNext 0b01#2) (.BTypeNext :: brRegs) := (Touches.refl s _).set _ _ (by decide)
    have hc1 := hc.of_touches hb (by decide)
    have h1 := h.set_other .BTypeNext 0b01#2 rfl (by decide) (by decide) (by decide)
    obtain ⟨s', hrun, hpc, hbt, htc⟩ := run_BranchTo hc1 (js.readZR n) ht .BranchType_INDIR false
    refine ⟨s', ?_, ?_, hbt, hc1.of_touches htc brRegs_not_cfg⟩
    · cfg_simp [execute_aarch64_instrs_branch_unconditional_register, undefined_GCSInstruction, run_internal_pick,
        hx, run_readReg hc.inGuarded, HaveGCS, run_IsFeatureImplemented hc, run_readReg hp, he]
      exact hrun
    · simpa using h1.touches htc brRegs_ok hpc
  · have h0 := h.writeZR (d := 30) (by decide) (js.pc + 4#64)
    have hc0 := hc.setGpr (js.pc + 4#64) (d := 30) (by decide)
    have hpc0 : (setGpr s (js.pc + 4#64) 30).regs.get? ._PC = some js.pc := h0.pc
    have hxs : (X_set (30 : Int) 64 (js.pc + 4#64)).run s = .ok () (setGpr s (js.pc + 4#64) 30) :=
      run_X_set (s := s) (n := 30) (by decide) (Or.inr rfl) (js.pc + 4#64)
    have hb : Touches (setGpr s (js.pc + 4#64) 30) ((setGpr s (js.pc + 4#64) 30).set .BTypeNext 0b10#2)
      (.BTypeNext :: brRegs) := (Touches.refl _ _).set _ _ (by decide)
    have hc1 := hc0.of_touches hb (by decide)
    have h1 := h0.set_other .BTypeNext 0b10#2 rfl (by decide) (by decide) (by decide)
    obtain ⟨s', hrun, hpc, hbt, htc⟩ := run_BranchTo hc1 (js.readZR n) ht .BranchType_INDCALL false
    have e3 : Sail.BitVec.addInt js.pc 4 = js.pc + 4#64 := by
      apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.addInt]
    refine ⟨s', ?_, ?_, hbt, hc1.of_touches htc brRegs_not_cfg⟩
    · cfg_simp [execute_aarch64_instrs_branch_unconditional_register, undefined_GCSInstruction, run_internal_pick,
        hx, HaveGCS, run_IsFeatureImplemented hc, run_readReg hp, he, run_GCSPCREnabled hc, PC_read,
        run_readReg h.pc, e3, hxs, run_readReg hpc0]
      have hg : (setGpr s (js.pc + 4#64) 30).regs.get? .InGuardedPage = some false := hc0.inGuarded
      cfg_simp [run_readReg hg, hrun]
    · simpa using h1.touches htc brRegs_ok hpc
  · have hb : Touches s (s.set .BTypeNext 0b00#2) (.BTypeNext :: brRegs) := (Touches.refl s _).set _ _ (by decide)
    have hc1 := hc.of_touches hb (by decide)
    have h1 := h.set_other .BTypeNext 0b00#2 rfl (by decide) (by decide) (by decide)
    obtain ⟨s', hrun, hpc, hbt, htc⟩ := run_BranchTo hc1 (js.readZR n) ht .BranchType_RET false
    refine ⟨s', ?_, ?_, hbt, hc1.of_touches htc brRegs_not_cfg⟩
    · cfg_simp [execute_aarch64_instrs_branch_unconditional_register, undefined_GCSInstruction, run_internal_pick,
        hx, run_readReg hc.inGuarded, HaveGCS, run_IsFeatureImplemented hc, run_readReg hp, he, run_GCSPCREnabled hc]
      exact hrun
    · simpa using h1.touches htc brRegs_ok hpc


theorem run_decode_br (Rn : BitVec 5) (s : SState) :
    (decode_br_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 0#2 0#1).run s =
      (execute_aarch64_instrs_branch_unconditional_register .BranchType_INDIR 0 Rn.toNat false false true).run s := by
  unfold decode_br_aarch64_instrs_branch_unconditional_register
  cfg_simp [undefined_BranchType, run_internal_pick]

theorem decode_br_class {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 10) % 4194304 = 3508160) (h1 : w % 32 = 0) :
    Janus.Arm64.decode w = some (.br (Janus.Arm64.bits w 9 5)) := by
  have e : w = 0xD61F0000 + ((w / 32) % 32) * 32 := by omega
  have hl : (w / 32) % 32 < 32 := Nat.mod_lt _ (by decide)
  generalize (w / 32) % 32 = rn at e hl
  subst e
  match rn, hl with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | 31, _ => rfl
  | _ + 32, hl => exact absurd hl (by omega)

set_option maxHeartbeats 8000000 in
/-- **BR** (under `LinuxEL0Config`, to an untagged, 4-byte aligned target). -/
theorem br_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 10) % 4194304 = 3508160) (h1 : w % 32 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hcfg : LinuxEL0Config s)
    (ht : (js.readZR (Janus.Arm64.bits w 9 5)).toNat < 2 ^ 56)
    (hal : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ LinuxEL0Config s' := by
  rw [bits_eq_fld w 9 5 hw] at ht hal
  obtain ⟨s2, hrun, hrel, hbt, hcf⟩ := run_execute_bru (h.entry (BitVec.ofNat 32 w) 92)
    (hcfg.stepEntry (BitVec.ofNat 32 w) 92) .BranchType_INDIR (by simp) (fld_lt w 5 5) ht
  have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      .ok () s2 := by
    rw [run_DecodeA64_BES hw (by omega), run_BranchExcSys_br hw h0 (by simpa using h1) (see_entry _ _),
      fld_eq_of hw (show (w / 2 ^ 0) % 2 ^ 5 = 0 by simpa using h1),
      fld_eq_of hw (show (w / 2 ^ 10) % 2 ^ 1 = 0 by omega),
      fld_eq_of hw (show (w / 2 ^ 11) % 2 ^ 1 = 0 by omega),
      fld_eq_of hw (show (w / 2 ^ 21) % 2 ^ 2 = 0 by omega),
      fld_eq_of hw (show (w / 2 ^ 24) % 2 ^ 1 = 0 by omega)]
    rw [run_decode_br]
    exact hrun
  refine ⟨_, _, ?_, run_janus_step_taken _ h.pc hdec hbt, by simpa using hrel, hcf⟩
  rw [Janus.Arm64.step_of_decode (decode_br_class hw h0 h1), bits_eq_fld w 9 5 hw]
  simp only [Janus.Arm64.exec, Janus.Arm64.branchReg]
  rw [if_neg (by omega), if_pos hal]
  try rfl

theorem run_decode_blr (Rn : BitVec 5) (s : SState) :
    (decode_blr_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 1#2 0#1).run s =
      (execute_aarch64_instrs_branch_unconditional_register .BranchType_INDCALL 0 Rn.toNat false false true).run s := by
  unfold decode_blr_aarch64_instrs_branch_unconditional_register
  cfg_simp [undefined_BranchType, run_internal_pick]

theorem decode_blr_class {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 10) % 4194304 = 3510208) (h1 : w % 32 = 0) :
    Janus.Arm64.decode w = some (.blr (Janus.Arm64.bits w 9 5)) := by
  have e : w = 0xD63F0000 + ((w / 32) % 32) * 32 := by omega
  have hl : (w / 32) % 32 < 32 := Nat.mod_lt _ (by decide)
  generalize (w / 32) % 32 = rn at e hl
  subst e
  match rn, hl with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | 31, _ => rfl
  | _ + 32, hl => exact absurd hl (by omega)

set_option maxHeartbeats 8000000 in
/-- **BLR** (under `LinuxEL0Config`, to an untagged, 4-byte aligned target). -/
theorem blr_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 10) % 4194304 = 3510208) (h1 : w % 32 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hcfg : LinuxEL0Config s)
    (ht : (js.readZR (Janus.Arm64.bits w 9 5)).toNat < 2 ^ 56)
    (hal : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ LinuxEL0Config s' := by
  rw [bits_eq_fld w 9 5 hw] at ht hal
  obtain ⟨s2, hrun, hrel, hbt, hcf⟩ := run_execute_bru (h.entry (BitVec.ofNat 32 w) 90)
    (hcfg.stepEntry (BitVec.ofNat 32 w) 90) .BranchType_INDCALL (by simp) (fld_lt w 5 5) ht
  have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      .ok () s2 := by
    rw [run_DecodeA64_BES hw (by omega), run_BranchExcSys_blr hw h0 (by simpa using h1) (see_entry _ _),
      fld_eq_of hw (show (w / 2 ^ 0) % 2 ^ 5 = 0 by simpa using h1),
      fld_eq_of hw (show (w / 2 ^ 10) % 2 ^ 1 = 0 by omega),
      fld_eq_of hw (show (w / 2 ^ 11) % 2 ^ 1 = 0 by omega),
      fld_eq_of hw (show (w / 2 ^ 21) % 2 ^ 2 = 1 by omega),
      fld_eq_of hw (show (w / 2 ^ 24) % 2 ^ 1 = 0 by omega)]
    rw [run_decode_blr]
    exact hrun
  refine ⟨_, _, ?_, run_janus_step_taken _ h.pc hdec hbt, by simpa using hrel, hcf⟩
  rw [Janus.Arm64.step_of_decode (decode_blr_class hw h0 h1), bits_eq_fld w 9 5 hw]
  simp only [Janus.Arm64.exec, Janus.Arm64.branchReg]
  rw [if_neg (by omega), if_pos hal]
  try rfl

theorem run_decode_ret (Rn : BitVec 5) (s : SState) :
    (decode_ret_aarch64_instrs_branch_unconditional_register 0#5 Rn 0#1 0#1 2#2 0#1).run s =
      (execute_aarch64_instrs_branch_unconditional_register .BranchType_RET 0 Rn.toNat false false true).run s := by
  unfold decode_ret_aarch64_instrs_branch_unconditional_register
  cfg_simp [undefined_BranchType, run_internal_pick]

theorem decode_ret_class {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 10) % 4194304 = 3512256) (h1 : w % 32 = 0) :
    Janus.Arm64.decode w = some (.ret (Janus.Arm64.bits w 9 5)) := by
  have e : w = 0xD65F0000 + ((w / 32) % 32) * 32 := by omega
  have hl : (w / 32) % 32 < 32 := Nat.mod_lt _ (by decide)
  generalize (w / 32) % 32 = rn at e hl
  subst e
  match rn, hl with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | 31, _ => rfl
  | _ + 32, hl => exact absurd hl (by omega)

set_option maxHeartbeats 8000000 in
/-- **RET** (under `LinuxEL0Config`, to an untagged, 4-byte aligned target). -/
theorem ret_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 10) % 4194304 = 3512256) (h1 : w % 32 = 0)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hcfg : LinuxEL0Config s)
    (ht : (js.readZR (Janus.Arm64.bits w 9 5)).toNat < 2 ^ 56)
    (hal : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ LinuxEL0Config s' := by
  rw [bits_eq_fld w 9 5 hw] at ht hal
  obtain ⟨s2, hrun, hrel, hbt, hcf⟩ := run_execute_bru (h.entry (BitVec.ofNat 32 w) 94)
    (hcfg.stepEntry (BitVec.ofNat 32 w) 94) .BranchType_RET (by simp) (fld_lt w 5 5) ht
  have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      .ok () s2 := by
    rw [run_DecodeA64_BES hw (by omega), run_BranchExcSys_ret hw h0 (by simpa using h1) (see_entry _ _),
      fld_eq_of hw (show (w / 2 ^ 0) % 2 ^ 5 = 0 by simpa using h1),
      fld_eq_of hw (show (w / 2 ^ 10) % 2 ^ 1 = 0 by omega),
      fld_eq_of hw (show (w / 2 ^ 11) % 2 ^ 1 = 0 by omega),
      fld_eq_of hw (show (w / 2 ^ 21) % 2 ^ 2 = 2 by omega),
      fld_eq_of hw (show (w / 2 ^ 24) % 2 ^ 1 = 0 by omega)]
    rw [run_decode_ret]
    exact hrun
  refine ⟨_, _, ?_, run_janus_step_taken _ h.pc hdec hbt, by simpa using hrel, hcf⟩
  rw [Janus.Arm64.step_of_decode (decode_ret_class hw h0 h1), bits_eq_fld w 9 5 hw]
  simp only [Janus.Arm64.exec, Janus.Arm64.branchReg]
  rw [if_neg (by omega), if_pos hal]
  try rfl

end JanusASL.Proofs
