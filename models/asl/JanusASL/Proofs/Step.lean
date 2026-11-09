import JanusASL.Proofs.Ops
import JanusASL.Proofs.JanusDecode
import JanusASL.Proofs.CfgDef

/-! # From the generated `janus_step` to a decode clause

`janus_step w` (the harness, `JanusASL/sail/harness.sail`) writes a few bookkeeping registers,
calls `__DecodeA64`, and advances PC unless a branch was taken. `__DecodeA64` dispatches on
`op0 = w<28:25>` to a class function, an if-chain over sail-arm's decode clauses. This file has
the parts that do not depend on the instruction: field extraction on literal-free words,
`run_janus_step`, the class dispatch lemmas and the final assembly `step_agree`. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem extractLsb_ofNat32 (w hi lo : Nat) (_ : hi < 32) (_ : lo ≤ hi) :
    Sail.BitVec.extractLsb (BitVec.ofNat 32 w) hi lo = BitVec.ofNat (hi - lo + 1) ((w % 2 ^ 32) / 2 ^ lo) := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, Nat.shiftRight_eq_div_pow]

theorem ofNat_beq_true {n a b : Nat} (h : a % 2 ^ n = b % 2 ^ n) :
    (BitVec.ofNat n a == BitVec.ofNat n b) = true :=
  beq_iff_eq.mpr (BitVec.eq_of_toNat_eq (by simp [h]))

theorem ofNat_beq_false {n a b : Nat} (h : a % 2 ^ n ≠ b % 2 ^ n) :
    (BitVec.ofNat n a == BitVec.ofNat n b) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]; intro e; apply h
  have := congrArg BitVec.toNat e; simpa using this

theorem slice_ofNat32 (w lo len : Nat) :
    Sail.BitVec.slice (BitVec.ofNat 32 w) lo len = BitVec.ofNat len ((w % 2 ^ 32) / 2 ^ lo) := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.slice, Nat.shiftRight_eq_div_pow]

/-- The state `janus_step` hands to the decoder. -/
def stepEntry (s : SState) (w : BitVec 32) : SState :=
  ((((((s.set .__janus_exc_taken false).set .SEE (-1)).set .__BranchTaken false).set
    .__ExclusiveMonitorSet false).set .__ThisInstrEnc .__A64).set .__ThisInstr w).set .__currentCond 0xE#4


theorem run_janus_step {s : SState} (w : BitVec 32) {pc : BitVec 64}
    (hpc : s.regs.get? ._PC = some pc) {s2 : SState}
    (hdec : (__DecodeA64 pc.toNat w).run (stepEntry s w) = .ok () s2)
    (hbt : s2.regs.get? .__BranchTaken = some false) (hpc2 : s2.regs.get? ._PC = some pc) :
    (janus_step w).run s = .ok .Janus_OK (s2.set ._PC (pc + 4)) := by
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
  have e3 : Sail.BitVec.addInt pc 4 = pc + 4 := by
    apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.addInt]
  simp only [run_readReg hpc1, hdec, andM, toBool, run_pure, run_bind, e2, run_readReg hbt, Bool.not_false,
    ite_true, run_readReg hpc2, e3, run_writeReg]


/-- The fields of `w` as the decode clauses slice them. -/
abbrev fld (w lo len : Nat) : BitVec len := Sail.BitVec.slice (BitVec.ofNat 32 w) lo len

theorem fld_toNat (w lo len : Nat) (hw : w < 2 ^ 32) : (fld w lo len).toNat = (w / 2 ^ lo) % 2 ^ len := by
  simp [fld, slice_ofNat32, Nat.mod_eq_of_lt hw]

theorem fld_bit (w i : Nat) (hw : w < 2 ^ 32) : (fld w i 1 == 1#1) = Janus.Arm64.bit w i := by
  have h := fld_toNat w i 1 hw
  simp only [Janus.Arm64.bit, Nat.shiftRight_eq_div_pow]
  rcases (show (w / 2 ^ i) % 2 = 0 ∨ (w / 2 ^ i) % 2 = 1 by omega) with e | e
  · have : fld w i 1 = 0#1 := BitVec.eq_of_toNat_eq (by rw [h, e]; rfl)
    rw [this, e]; decide
  · have : fld w i 1 = 1#1 := BitVec.eq_of_toNat_eq (by rw [h, e]; rfl)
    rw [this, e]; decide

theorem bits_eq_fld (w hi lo : Nat) (hw : w < 2 ^ 32) :
    Janus.Arm64.bits w hi lo = (fld w lo (hi + 1 - lo)).toNat := by
  rw [fld_toNat w lo _ hw]; simp [Janus.Arm64.bits, Nat.shiftRight_eq_div_pow]

theorem Rel.set_other {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (r : Register) (v : RegisterType r)
    (hg : isGprReg r = false) (h1 : r ≠ .SP_EL0) (h2 : r ≠ ._PC) (h3 : r ≠ .PSTATE) : Rel js (s.set r v) where
  gpr i hi := by rw [gprVal_set s r v hg hi]; exact h.gpr i hi
  sp := by rw [get?_set_ne s (r := r) v h1]; exact h.sp
  pc := by rw [get?_set_ne s (r := r) v h2]; exact h.pc
  pstate := by rw [get?_set_ne s (r := r) v h3]; exact h.pstate

theorem Rel.stepEntry {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (w : BitVec 32) :
    Rel js (stepEntry s w) := by
  unfold JanusASL.Proofs.stepEntry
  repeat (apply Rel.set_other _ _ _ rfl (by decide) (by decide) (by decide))
  exact h

theorem Rel.setPC {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (v : BitVec 64) :
    Rel { js with pc := v } (s.set ._PC v) where
  gpr i hi := by rw [gprVal_set s ._PC v rfl hi]; exact h.gpr i hi
  sp := by rw [get?_set_ne s (r := ._PC) v (by decide)]; exact h.sp
  pc := get?_set_PC s v
  pstate := by rw [get?_set_ne s (r := ._PC) v (by decide)]; exact h.pstate

theorem run_DecodeA64_DPImm {w : Nat} (hw : w < 2 ^ 32) (hcls : (w / 2 ^ 26) % 8 = 4) (pc : Int) (s : SState) :
    (__DecodeA64 pc (BitVec.ofNat 32 w)).run s = (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s := by
  have e : ∀ c : Nat, c < 4 → (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 25 == BitVec.ofNat 4 c) = false := by
    intro c hc
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 26 == (0b100#3 : BitVec 3)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64]
  simp only [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e6, Bool.and_false,
    Bool.false_eq_true, ite_false, ite_true]


theorem access_ofNat32 (w i : Nat) (hi : i < 32) (h : (w / 2 ^ i) % 2 = 1) :
    Sail.BitVec.access (BitVec.ofNat 32 w) i = 1#1 := by
  have e : (BitVec.ofNat 32 w)[i]'hi = true := by
    rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
    simp only [hi, decide_true, Bool.true_and, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, h]
    rfl
  simp [Sail.BitVec.access, hi, e]

theorem fld_lt (w lo len : Nat) : (fld w lo len).toNat < 2 ^ len := (fld w lo len).isLt

theorem width_cases (w : Nat) : (if fld w 31 1 == 1#1 then 64 else 32) = 32 ∨
    (if fld w 31 1 == 1#1 then 64 else 32) = 64 := by
  split <;> simp


theorem bt_after {s : SState} (w : BitVec 32) {s2 : SState} (n : Int)
    (hfr : Frame ((stepEntry s w).set .SEE n) s2) : s2.regs.get? .__BranchTaken = some false := by
  rw [hfr _ rfl (by decide) (by decide), get?_set_ne _ (r := .SEE) _ (by decide)]
  simp only [stepEntry]; repeat rw [get?_set_ne _ _ (by decide)]
  exact get?_set_BranchTaken _ _

theorem see_entry (s : SState) (w : BitVec 32) : (stepEntry s w).regs.get? .SEE = some (-1) := by
  simp only [stepEntry]; repeat rw [get?_set_ne _ _ (by decide)]
  exact get?_set_SEE _ _

theorem Rel.entry {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (w : BitVec 32) (n : Int) :
    Rel js ((JanusASL.Proofs.stepEntry s w).set .SEE n) :=
  (h.stepEntry w).set_other .SEE n rfl (by decide) (by decide) (by decide)

theorem cfgFrame0_of {s : SState} {w : BitVec 32} {n : Int} {s2 : SState}
    (hfr : Frame ((stepEntry s w).set .SEE n) s2) : CfgFrame0 s s2 := by
  intro r hr hp
  rw [hfr r (cfgRegs_not_gpr r hr) (fun e => by subst e; revert hr; decide) hp]
  have hS : r ≠ .SEE := fun e => by subst e; revert hr; decide
  rw [get?_set_ne _ _ (Ne.symm hS)]
  simp only [stepEntry]
  have h1 : r ≠ .__currentCond := fun e => by subst e; revert hr; decide
  have h2 : r ≠ .__ThisInstr := fun e => by subst e; revert hr; decide
  have h3 : r ≠ .__ThisInstrEnc := fun e => by subst e; revert hr; decide
  have h4 : r ≠ .__ExclusiveMonitorSet := fun e => by subst e; revert hr; decide
  have h5 : r ≠ .__BranchTaken := fun e => by subst e; revert hr; decide
  have h6 : r ≠ .__janus_exc_taken := fun e => by subst e; revert hr; decide
  rw [get?_set_ne _ _ (Ne.symm h1), get?_set_ne _ _ (Ne.symm h2), get?_set_ne _ _ (Ne.symm h3),
    get?_set_ne _ _ (Ne.symm h4), get?_set_ne _ _ (Ne.symm h5), get?_set_ne _ _ (Ne.symm hS),
    get?_set_ne _ _ (Ne.symm h6)]

theorem fpFrame_of {s : SState} {w : BitVec 32} {n : Int} {s2 : SState}
    (hfr : Frame ((stepEntry s w).set .SEE n) s2) : FPFrame s s2 := by
  intro r hr
  rw [hfr r (fpFrameRegs_not_gpr r hr) (fun e => by subst e; revert hr; decide) (fun e => by subst e; revert hr; decide)]
  have hS : r ≠ .SEE := fun e => by subst e; revert hr; decide
  rw [get?_set_ne _ _ (Ne.symm hS)]
  simp only [stepEntry]
  have h1 : r ≠ .__currentCond := fun e => by subst e; revert hr; decide
  have h2 : r ≠ .__ThisInstr := fun e => by subst e; revert hr; decide
  have h3 : r ≠ .__ThisInstrEnc := fun e => by subst e; revert hr; decide
  have h4 : r ≠ .__ExclusiveMonitorSet := fun e => by subst e; revert hr; decide
  have h5 : r ≠ .__BranchTaken := fun e => by subst e; revert hr; decide
  have h6 : r ≠ .__janus_exc_taken := fun e => by subst e; revert hr; decide
  rw [get?_set_ne _ _ (Ne.symm h1), get?_set_ne _ _ (Ne.symm h2), get?_set_ne _ _ (Ne.symm h3),
    get?_set_ne _ _ (Ne.symm h4), get?_set_ne _ _ (Ne.symm h5), get?_set_ne _ _ (Ne.symm hS),
    get?_set_ne _ _ (Ne.symm h6)]

theorem fpFrame_entry (s : SState) (w : BitVec 32) (n : Int) : FPFrame s ((stepEntry s w).set .SEE n) := by
  intro r hr
  have hS : r ≠ .SEE := fun e => by subst e; revert hr; decide
  rw [get?_set_ne _ _ (Ne.symm hS)]
  simp only [stepEntry]
  have h1 : r ≠ .__currentCond := fun e => by subst e; revert hr; decide
  have h2 : r ≠ .__ThisInstr := fun e => by subst e; revert hr; decide
  have h3 : r ≠ .__ThisInstrEnc := fun e => by subst e; revert hr; decide
  have h4 : r ≠ .__ExclusiveMonitorSet := fun e => by subst e; revert hr; decide
  have h5 : r ≠ .__BranchTaken := fun e => by subst e; revert hr; decide
  have h6 : r ≠ .__janus_exc_taken := fun e => by subst e; revert hr; decide
  rw [get?_set_ne _ _ (Ne.symm h1), get?_set_ne _ _ (Ne.symm h2), get?_set_ne _ _ (Ne.symm h3),
    get?_set_ne _ _ (Ne.symm h4), get?_set_ne _ _ (Ne.symm h5), get?_set_ne _ _ (Ne.symm hS),
    get?_set_ne _ _ (Ne.symm h6)]

theorem cfgFrame_of {s : SState} {w : BitVec 32} {n : Int} {s2 : SState}
    (hfr : Frame ((stepEntry s w).set .SEE n) s2) : CfgFrame s s2 := ⟨cfgFrame0_of hfr, fpFrame_of hfr⟩

theorem bt_cfg_after {s : SState} (w : BitVec 32) {s2 : SState} (n : Int)
    (hfr : Frame ((stepEntry s w).set .SEE n) s2) :
    s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2 := ⟨bt_after w n hfr, cfgFrame_of hfr⟩

/-- Assembly: if the decoder, run from the state `janus_step` hands it, completes in a state
related to `spec` with no branch taken and no configuration register changed, and Janus steps to
`spec` with PC advanced, then the two agree on the whole step and the configuration is
preserved. -/
theorem step_agree {w : Nat} {js spec : Janus.Arm64.State} {s : SState} (h : Rel js s)
    (hasl : ∃ s2, (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      .ok () s2 ∧ Rel spec s2 ∧ (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2))
    (hpc : spec.pc = js.pc) (hjanus : Janus.Arm64.step w js = .ok { spec with pc := js.pc + 4 }) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧
      (LinuxEL0Config s → LinuxEL0Config s') := by
  obtain ⟨s2, hrun, hrel, hbt, hcf⟩ := hasl
  have hpc2 : s2.regs.get? ._PC = some js.pc := by rw [hrel.pc, hpc]
  refine ⟨_, _, hjanus, run_janus_step (BitVec.ofNat 32 w) h.pc hrun hbt hpc2, hrel.setPC _, fun hc => ?_⟩
  have hR := hrel.setPC (js.pc + 4)
  obtain ⟨p, hp, hps⟩ := hR.pstate
  refine hc.of_frame (fun r hr hne => ?_) ⟨p, hp, hps.el, hps.nrw, hps.sp⟩
  rw [get?_set_ne _ _ (fun e => by subst e; revert hr; decide)]
  exact hcf.1 r hr hne

/-- `step_agree` that also concludes that no floating-point register changed (`FPFrame`). -/
theorem step_agree_f {w : Nat} {js spec : Janus.Arm64.State} {s : SState} (h : Rel js s)
    (hasl : ∃ s2, (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      .ok () s2 ∧ Rel spec s2 ∧ (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2))
    (hpc : spec.pc = js.pc) (hjanus : Janus.Arm64.step w js = .ok { spec with pc := js.pc + 4 }) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧
      (LinuxEL0Config s → LinuxEL0Config s') ∧ FPFrame s s' := by
  obtain ⟨s2, hrun, hrel, hbt, hcf⟩ := hasl
  have hpc2 : s2.regs.get? ._PC = some js.pc := by rw [hrel.pc, hpc]
  refine ⟨_, _, hjanus, run_janus_step (BitVec.ofNat 32 w) h.pc hrun hbt hpc2, hrel.setPC _, fun hc => ?_, ?_⟩
  · have hR := hrel.setPC (js.pc + 4)
    obtain ⟨p, hp, hps⟩ := hR.pstate
    refine hc.of_frame (fun r hr hne => ?_) ⟨p, hp, hps.el, hps.nrw, hps.sp⟩
    rw [get?_set_ne _ _ (fun e => by subst e; revert hr; decide)]
    exact hcf.1 r hr hne
  · intro r hr
    rw [get?_set_ne _ _ (fun e => by subst e; revert hr; decide)]
    exact hcf.2 r hr

theorem run_DecodeA64_DPReg {w : Nat} (hw : w < 2 ^ 32) (hcls : (w / 2 ^ 25) % 8 = 5) (pc : Int) (s : SState) :
    (__DecodeA64 pc (BitVec.ofNat 32 w)).run s = (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s := by
  have e : ∀ c : Nat, c < 4 → (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 25 == BitVec.ofNat 4 c) = false := by
    intro c hc
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 26 == (0b100#3 : BitVec 3)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 26 == (0b101#3 : BitVec 3)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 25 25 == (0#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 27 25 == (0b101#3 : BitVec 3)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64]
  simp only [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e5, e6, e7, e8,
    Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false, ite_true]

end JanusASL.Proofs
