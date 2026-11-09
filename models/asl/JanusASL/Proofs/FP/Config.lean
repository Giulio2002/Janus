import JanusASL.Proofs.Loop
import JanusASL.Proofs.Config

/-! # The floating-point configuration

`FPConfig s`: the registers that enable the FP/SIMD unit at EL0 hold the check's values
(CPACR_EL1.FPEN = 11, CPTR_EL2 with E2H = 0 and TFP = 0, CPTR_EL3.TFP = 0). With
`LinuxEL0Config`, `CheckFPEnabled64` passes. -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- Not in streaming mode (`PSTATE.SM = 0`): Linux runs a thread outside streaming SVE mode
unless it enters it with `SMSTART`, which Janus does not decode. `FPRoundBase` reads it
(`InStreamingMode`) for `trapped_UF`. -/
def SMZero (s : SState) : Prop := ∃ p : ProcState, s.regs.get? .PSTATE = some p ∧ p.SM = 0#1

structure FPConfig (s : SState) : Prop where
  cpacr1 : s.regs.get? .CPACR_EL1 = some 0x3330000#64
  cptr2 : s.regs.get? .CPTR_EL2 = some 0x22ff#64
  cptr3 : s.regs.get? .CPTR_EL3 = some 0x1100#64
  sm : SMZero s
  zcr1 : s.regs.get? .ZCR_EL1 = some 0x3#64
  zcr2 : s.regs.get? .ZCR_EL2 = some 0xf#64
  zcr3 : s.regs.get? .ZCR_EL3 = some 0xf#64
  smcr1 : s.regs.get? .SMCR_EL1 = some 0#64
  smcr2 : s.regs.get? .SMCR_EL2 = some 0#64
  smcr3 : s.regs.get? .SMCR_EL3 = some 0#64
  smevl : s.regs.get? .__max_implemented_smeveclen = some 512

/-- The FP configuration registers (PSTATE for `SM`; the vector-length registers `V[]` reads). -/
def fpCfgRegs : List Register := [.CPACR_EL1, .CPTR_EL2, .CPTR_EL3, .PSTATE, .ZCR_EL1, .ZCR_EL2, .ZCR_EL3,
  .SMCR_EL1, .SMCR_EL2, .SMCR_EL3, .__max_implemented_smeveclen]

theorem FPConfig.of_eq {s s' : SState} (h : FPConfig s) (e : ∀ r ∈ fpCfgRegs, s'.regs.get? r = s.regs.get? r) :
    FPConfig s' :=
  { cpacr1 := by rw [e _ (by decide)]; exact h.cpacr1
    cptr2 := by rw [e _ (by decide)]; exact h.cptr2
    cptr3 := by rw [e _ (by decide)]; exact h.cptr3
    sm := by obtain ⟨p, hp, hs⟩ := h.sm; exact ⟨p, by rw [e _ (by decide)]; exact hp, hs⟩
    zcr1 := by rw [e _ (by decide)]; exact h.zcr1
    zcr2 := by rw [e _ (by decide)]; exact h.zcr2
    zcr3 := by rw [e _ (by decide)]; exact h.zcr3
    smcr1 := by rw [e _ (by decide)]; exact h.smcr1
    smcr2 := by rw [e _ (by decide)]; exact h.smcr2
    smcr3 := by rw [e _ (by decide)]; exact h.smcr3
    smevl := by rw [e _ (by decide)]; exact h.smevl }

/-- `FPConfig` from the three enable registers and `SM` (when PSTATE was written). -/
theorem FPConfig.of_eq3 {s s' : SState} (h : FPConfig s)
    (e : ∀ r ∈ [Register.CPACR_EL1, .CPTR_EL2, .CPTR_EL3, .ZCR_EL1, .ZCR_EL2, .ZCR_EL3, .SMCR_EL1, .SMCR_EL2,
      .SMCR_EL3, .__max_implemented_smeveclen], s'.regs.get? r = s.regs.get? r) (hsm : SMZero s') :
    FPConfig s' :=
  { cpacr1 := by rw [e _ (by decide)]; exact h.cpacr1
    cptr2 := by rw [e _ (by decide)]; exact h.cptr2
    cptr3 := by rw [e _ (by decide)]; exact h.cptr3
    sm := hsm
    zcr1 := by rw [e _ (by decide)]; exact h.zcr1
    zcr2 := by rw [e _ (by decide)]; exact h.zcr2
    zcr3 := by rw [e _ (by decide)]; exact h.zcr3
    smcr1 := by rw [e _ (by decide)]; exact h.smcr1
    smcr2 := by rw [e _ (by decide)]; exact h.smcr2
    smcr3 := by rw [e _ (by decide)]; exact h.smcr3
    smevl := by rw [e _ (by decide)]; exact h.smevl }

/-- `FPConfig` as a check (evaluated by `janus-asl-check` on every case's pre- and post-state). -/
def fpCfgOk (s : SState) : Bool :=
  s.regs.get? .CPACR_EL1 == some 0x3330000#64 && s.regs.get? .CPTR_EL2 == some 0x22ff#64 &&
  s.regs.get? .CPTR_EL3 == some 0x1100#64 &&
  (match s.regs.get? .PSTATE with | some p => p.SM == 0#1 | none => false) &&
  s.regs.get? .ZCR_EL1 == some 0x3#64 && s.regs.get? .ZCR_EL2 == some 0xf#64 && s.regs.get? .ZCR_EL3 == some 0xf#64 &&
  s.regs.get? .SMCR_EL1 == some 0#64 && s.regs.get? .SMCR_EL2 == some 0#64 && s.regs.get? .SMCR_EL3 == some 0#64 &&
  s.regs.get? .__max_implemented_smeveclen == some 512

theorem fpCfgOk_sound {s : SState} (h : fpCfgOk s = true) : FPConfig s := by
  simp only [fpCfgOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, z1⟩, z2⟩, z3⟩, m1⟩, m2⟩, m3⟩, sv⟩ := h
  refine ⟨h1, h2, h3, ?_, z1, z2, z3, m1, m2, m3, sv⟩
  revert h4; cases hp : s.regs.get? .PSTATE with
  | none => simp
  | some p => intro h4; exact ⟨p, hp, by simpa using h4⟩

theorem run_CheckFPEnabled64 {s : SState} (hc : LinuxEL0Config s) (hf : FPConfig s) :
    (CheckFPEnabled64 ()).run s = .ok () s := by
  obtain ⟨p, hp, he, _, _⟩ := hc.pstate
  cfg_simp [CheckFPEnabled64, AArch64_CheckFPEnabled, AArch64_CheckFPAdvSIMDTrap, run_readReg hp, he, EL0,
    run_IsInHost hc, run_readReg hf.cpacr1, run_readReg hf.cptr2, run_readReg hf.cptr3, run_readReg hc.hcr2,
    run_EL2Enabled hc, HaveEL, HaveVirtHostExt, run_IsFeatureImplemented hc, _get_CPTR_EL3_Type_TFP,
    _get_CPTR_EL2_Type_TFP, _get_CPTR_EL2_Type_FPEN, _get_HCR_EL2_Type_E2H, _get_HCR_EL2_Type_TGE, _get_CPACR_EL1_Type_FPEN,
    Sail.BitVec.extractLsb]

end JanusASL.Proofs

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem SState.set_same (s : SState) (r : Register) (v : RegisterType r) (h : s.regs.get? r = some v) :
    s.set r v = s := by
  simp only [SState.set]
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro k
  rw [Std.ExtDHashMap.get?_insert]
  split
  · next h' => have := beq_iff_eq.mp h'; subst this; rw [h]; rfl
  · rfl

theorem update_one_or (x : BitVec 64) (i : Nat) (_hi : i < 64) :
    Sail.BitVec.update x i 1#1 = x ||| BitVec.ofNat 64 (2 ^ i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h; simp [hj]
  · simp only [hj, h]
    by_cases hji : j < i
    · simp [hji]
    · have h0 : decide (j - i = 0) = false := by simp; omega
      simp [hji, h0]

@[simp] theorem set_set_FPSR (s : SState) (a b : BitVec 64) :
    (s.set .FPSR a).set .FPSR b = s.set .FPSR b := SState.set_set s .FPSR a b
@[simp] theorem get?_set_FPSR (s : SState) (v : BitVec 64) :
    (s.set .FPSR v).regs.get? .FPSR = some v := get?_set_self s .FPSR v

/-- The FPSR cumulative bit of an `FPExc`. -/
def fpExcBit : FPExc → Nat
  | .FPExc_InvalidOp => 0
  | .FPExc_DivideByZero => 1
  | .FPExc_Overflow => 2
  | .FPExc_Underflow => 3
  | .FPExc_Inexact => 4
  | .FPExc_InputDenorm => 7

theorem run_FPProcessException {s : SState} (hc : LinuxEL0Config s) (e : FPExc) (fpcr : BitVec 64)
    (hen : fpcr.getLsbD (fpExcBit e + 8) = false) {x : BitVec 64} (hx : s.regs.get? .FPSR = some x) :
    (FPProcessException e fpcr).run s = .ok () (s.set .FPSR (Sail.BitVec.update x (fpExcBit e) 1#1)) := by
  have hb : fpExcBit e + 8 < 64 := by cases e <;> decide
  have ha : Sail.BitVec.access fpcr (fpExcBit e + 8) = 0#1 := by
    simp only [Sail.BitVec.access]; rw [getElem!_pos fpcr _ hb]
    simp [← BitVec.getLsbD_eq_getElem hb, hen]
  cases e <;> simp only [fpExcBit] at ha <;>
  cfg_simp [FPProcessException, run_UsingAArch32 hc, run_readReg hx, Bit, fpExcBit, ha] <;> rfl

end JanusASL.Proofs
