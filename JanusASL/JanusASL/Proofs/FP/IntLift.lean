import JanusASL.Proofs.FP.Run
import JanusASL.Proofs.FpSame.Ctor1
import JanusASL.Proofs.FpSame.Ctor2
import JanusASL.Proofs.FpSame.Ctor3
import JanusASL.Proofs.FpSame.Ctor4

/-! # The integer and branch classes carry the floating-point relation

An integer or branch step changes neither the V registers, FPCR and FPSR (Janus: `FpSame`, FpSame/*.lean) nor
the floating-point registers of the ASL state (`FPFrame`, concluded by the `*_agree_f` theorems), and `Rel` fixes
`PSTATE.SM = 0`, so each integer and branch class is `FPStepOK`. -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions JanusASL.FpS

theorem fp_lift {js js' : Janus.Arm64.State} {s s' : SState} (hf : FPRel js s) (hfc : FPConfig s)
    (hrel : Rel js' s') (hfp : FPFrame s s') (hsame : FpSame js js') : FPRel js' s' ∧ FPConfig s' := by
  obtain ⟨z, hz, hzv⟩ := hf.z
  refine ⟨{ z := ⟨z, (hfp ._Z (by decide)).trans hz, fun i hi => by rw [hsame.1]; exact hzv i hi⟩
            fpcr := ?_, fpcrRes0 := by rw [hsame.2.1]; exact hf.fpcrRes0, fpsr := ?_ }, ?_⟩
  · rw [hfp .FPCR (by decide), hsame.2.1]; exact hf.fpcr
  · rw [hfp .FPSR (by decide), hsame.2.2]; exact hf.fpsr
  · obtain ⟨p, hp, hps⟩ := hrel.pstate
    exact { cpacr1 := (hfp .CPACR_EL1 (by decide)).trans hfc.cpacr1
            cptr2 := (hfp .CPTR_EL2 (by decide)).trans hfc.cptr2
            cptr3 := (hfp .CPTR_EL3 (by decide)).trans hfc.cptr3
            sm := ⟨p, hp, hps.sm⟩
            zcr1 := (hfp .ZCR_EL1 (by decide)).trans hfc.zcr1
            zcr2 := (hfp .ZCR_EL2 (by decide)).trans hfc.zcr2
            zcr3 := (hfp .ZCR_EL3 (by decide)).trans hfc.zcr3
            smcr1 := (hfp .SMCR_EL1 (by decide)).trans hfc.smcr1
            smcr2 := (hfp .SMCR_EL2 (by decide)).trans hfc.smcr2
            smcr3 := (hfp .SMCR_EL3 (by decide)).trans hfc.smcr3
            smevl := (hfp .__max_implemented_smeveclen (by decide)).trans hfc.smevl }

theorem FPStepOK.of_int {w : Nat}
    (H : ∀ (js : Janus.Arm64.State) (s : SState), Rel js s → LinuxEL0Config s → ∃ js' s',
      Janus.Arm64.step w js = .ok js' ∧ (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧
      (LinuxEL0Config s → LinuxEL0Config s') ∧ FPFrame s s')
    (S : ∀ js js', Janus.Arm64.step w js = .ok js' → FpSame js js') : FPStepOK w := by
  intro js js' s h hf hc hfc hj _
  obtain ⟨js2, s', hj2, hrun, hrel, hcf, hfp⟩ := H js s h hc
  rw [hj] at hj2; cases hj2
  obtain ⟨h1, h2⟩ := fp_lift hf hfc hrel hfp (S js js' hj)
  exact ⟨s', hrun, hrel, h1, hcf hc, h2⟩

section
variable {w : Nat} (hw : w < 2 ^ 32)
include hw

theorem fpStepOK_addSubImm (hc : (w / 2 ^ 23) % 64 = 0b100010) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => addSubImm_agree_f hw hc h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_addSubImm_class hw hc)] at hj
      exact fp_exec_addSubImm _ _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_addSubShifted (h1 : (w / 2 ^ 24) % 32 = 0b01011) (h2 : (w / 2 ^ 21) % 2 = 0) (h3 : (w / 2 ^ 22) % 4 ≠ 3) (h4 : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => addSubShifted_agree_f hw h1 h2 h3 h4 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_addSubShifted_class hw h1 h2 h3 h4)] at hj
      exact fp_exec_addSubShifted _ _ _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_addSubExt (h1 : (w / 2 ^ 24) % 32 = 0b01011) (h2 : (w / 2 ^ 21) % 8 = 1) (h3 : (w / 2 ^ 10) % 8 ≤ 4) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => addSubExt_agree_f hw h1 h2 h3 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_addSubExt_class hw h1 h2 h3)] at hj
      exact fp_exec_addSubExt _ _ _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_addSubCarry (h1 : (w / 2 ^ 21) % 256 = 0b11010000) (h2 : (w / 2 ^ 10) % 64 = 0) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => addSubCarry_agree_f hw h1 h2 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_addSubCarry_class hw h1 h2)] at hj
      exact fp_exec_addSubCarry _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_logicalShifted (h1 : (w / 2 ^ 24) % 32 = 0b01010) (h4 : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => logicalShifted_agree_f hw h1 h4 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_logicalShifted_class hw h1 h4)] at hj
      exact fp_exec_logicalShifted _ _ _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_logicalImm (hc : (w / 2 ^ 23) % 64 = 0b100100) (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0) (hdbm : (Janus.Arm64.decodeBitMasks (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 21 16) true (if Janus.Arm64.bit w 31 then 64 else 32)).isSome = true) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => logicalImm_agree_f hw hc hsf hdbm h)
    (fun js js' hj => by
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hdbm
      rw [Janus.Arm64.step_of_decode (decode_logicalImm_class hw hc hsf hp)] at hj
      exact fp_exec_logicalImm _ _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_moveWide (hc : (w / 2 ^ 23) % 64 = 0b100101) (hop : (w / 2 ^ 29) % 4 ≠ 1) (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => moveWide_agree_f hw hc hop hsf h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_moveWide_class hw hc hop hsf)] at hj
      exact fp_exec_moveWide _ _ _ _ _ _ _ hj)

theorem fpStepOK_bitfield (hc : (w / 2 ^ 23) % 64 = 0b100110) (hop : (w / 2 ^ 29) % 4 ≠ 3) (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2) (hsf : (w / 2 ^ 31) % 2 = 1 ∨ ((w / 2 ^ 16) % 64 < 32 ∧ (w / 2 ^ 10) % 64 < 32)) (hdbm : (Janus.Arm64.decodeBitMasks (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 21 16) false (if Janus.Arm64.bit w 31 then 64 else 32)).isSome = true) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => bitfield_agree_f hw hc hop hN hsf hdbm h)
    (fun js js' hj => by
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hdbm
      rw [Janus.Arm64.step_of_decode (decode_bitfield_class hw hc hop hN hsf hp)] at hj
      exact fp_exec_bitfield _ _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_extr (hc : (w / 2 ^ 23) % 64 = 0b100111) (h0 : (w / 2 ^ 29) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 0) (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2) (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => extr_agree_f hw hc h0 h21 hN hsf h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_extr_class hw hc h0 h21 hN hsf)] at hj
      exact fp_exec_extr _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_pcrel (hc : (w / 2 ^ 24) % 32 = 0b10000) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => pcrel_agree_f hw hc h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_pcrel_class hw hc)] at hj
      exact fp_exec_adr _ _ _ _ _ _ hj)

theorem fpStepOK_condSel (h1 : (w / 2 ^ 21) % 512 = 0b011010100) (h2 : (w / 2 ^ 11) % 2 = 0) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => condSel_agree_f hw h1 h2 h hcfg.speInFlight)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_condSel_class hw h1 h2)] at hj
      exact fp_exec_condSel _ _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_condCmpReg (h1 : (w / 2 ^ 21) % 512 = 0b111010010) (h2 : (w / 2 ^ 10) % 2 = 0) (h3 : (w / 2 ^ 4) % 2 = 0) (h4 : (w / 2 ^ 11) % 2 = 0) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => condCmpReg_agree_f hw h1 h2 h3 h4 h hcfg.speInFlight)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_condCmpReg_class hw h1 h2 h3 h4)] at hj
      exact fp_exec_condCmpReg _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_condCmpImm (h1 : (w / 2 ^ 21) % 512 = 0b111010010) (h2 : (w / 2 ^ 10) % 2 = 0) (h3 : (w / 2 ^ 4) % 2 = 0) (h4 : (w / 2 ^ 11) % 2 = 1) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => condCmpImm_agree_f hw h1 h2 h3 h4 h hcfg.speInFlight)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_condCmpImm_class hw h1 h2 h3 h4)] at hj
      exact fp_exec_condCmpImm _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_madd (h1 : (w / 2 ^ 21) % 1024 = 0b0011011000) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => madd_agree_f hw h1 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_madd_class hw h1)] at hj
      exact fp_exec_madd _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_maddl (hc : (w / 2 ^ 24) % 256 = 0b10011011) (h2 : (w / 2 ^ 21) % 4 = 1) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => maddl_agree_f hw hc h2 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_maddl_class hw hc h2)] at hj
      exact fp_exec_maddl _ _ _ _ _ _ _ _ hj)

theorem fpStepOK_mulh (hc : (w / 2 ^ 24) % 256 = 0b10011011) (h2 : (w / 2 ^ 21) % 4 = 2) (h3 : (w / 2 ^ 15) % 2 = 0) (h4 : (w / 2 ^ 10) % 32 = 31) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => mulh_agree_f hw hc h2 h3 h4 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_mulh_class hw hc h2 h3 h4)] at hj
      exact fp_exec_mulh _ _ _ _ _ _ hj)

theorem fpStepOK_div (h1 : (w / 2 ^ 21) % 1024 = 0b0011010110) (h2 : (w / 2 ^ 11) % 32 = 1) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => div_agree_f hw h1 h2 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_div_class hw h1 h2)] at hj
      exact fp_exec_div _ _ _ _ _ _ _ hj)

theorem fpStepOK_shiftV (h1 : (w / 2 ^ 21) % 1024 = 0b0011010110) (h2 : (w / 2 ^ 12) % 16 = 0b0010) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => shiftV_agree_f hw h1 h2 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_shiftV_class hw h1 h2)] at hj
      exact fp_exec_shiftV _ _ _ _ _ _ _ hj)

theorem fpStepOK_rbit (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 0) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => rbit_agree_f hw h1 h2 h3 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_rbit_class hw h1 h2 h3)] at hj
      exact fp_exec_rbit _ _ _ _ _ hj)

theorem fpStepOK_clz (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 4) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => clz_agree_f hw h1 h2 h3 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_clz_class hw h1 h2 h3)] at hj
      exact fp_exec_clz _ _ _ _ _ hj)

theorem fpStepOK_cls (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 5) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => cls_agree_f hw h1 h2 h3 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_cls_class hw h1 h2 h3)] at hj
      exact fp_exec_cls _ _ _ _ _ hj)

theorem fpStepOK_rev16 (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 1) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => rev16_agree_f hw h1 h2 h3 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_rev1_class hw h1 h2 h3)] at hj
      exact fp_exec_rev _ _ _ _ _ _ hj)

theorem fpStepOK_rev32 (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 2) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => rev32_agree_f hw h1 h2 h3 h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_rev2_class hw h1 h2 h3)] at hj
      exact fp_exec_rev _ _ _ _ _ _ hj)

theorem fpStepOK_rev64 (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0) (h3 : (w / 2 ^ 10) % 64 = 3) (hsf : (w / 2 ^ 31) % 2 = 1) : FPStepOK w :=
  FPStepOK.of_int (fun _ _ h hcfg => rev64_agree_f hw h1 h2 h3 hsf h)
    (fun js js' hj => by
      rw [Janus.Arm64.step_of_decode (decode_rev3_class hw h1 h2 h3 hsf)] at hj
      exact fp_exec_rev _ _ _ _ _ _ hj)


/-- The branch classes: as `stepOK_b` etc. (Run.lean), with the floating-point relation carried. -/
theorem fpStepOK_b (hc : (w / 2 ^ 26) % 32 = 0b00101) : FPStepOK w := by
  intro js js' s h hf hcfg hfc hst hpc
  have hsame : FpSame js js' := by
    have hst1 := hst
    rw [Janus.Arm64.step_of_decode (decode_b_class hw hc)] at hst1
    exact fp_exec_b _ _ _ _ hst1
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_b_class hw hc)] at hst'
  simp only [Janus.Arm64.exec] at hst'
  have hpc' : js'.pc = js.pc + Janus.Arm64.sext64 28 (Janus.Arm64.bits w 25 0 * 4) := by
    cases hst'; split <;> rfl
  obtain ⟨js'', s', h1, h2, h3, h4, h5⟩ := b_agree_f hw hc h hcfg (hpc' ▸ hpc)
  rw [hst] at h1; cases h1
  obtain ⟨q1, q2⟩ := fp_lift hf hfc h3 h5 hsame
  exact ⟨s', h2, h3, q1, h4, q2⟩

theorem fpStepOK_bcond (hc : (w / 2 ^ 24) % 256 = 0b01010100) (h4 : (w / 2 ^ 4) % 2 = 0) : FPStepOK w := by
  intro js js' s h hf hcfg hfc hst hpc
  have hsame : FpSame js js' := by
    have hst1 := hst
    rw [Janus.Arm64.step_of_decode (decode_bcond_class hw hc h4)] at hst1
    exact fp_exec_bcond _ _ _ _ hst1
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_bcond_class hw hc h4)] at hst'
  simp only [Janus.Arm64.exec] at hst'
  have ht : Janus.Arm64.conditionHolds (Janus.Arm64.bits w 3 0) js.flags = true →
      (js.pc + Janus.Arm64.sext64 21 (Janus.Arm64.bits w 23 5 * 4)).toNat < 2 ^ 56 := by
    intro hcnd; rw [if_pos hcnd] at hst'; cases hst'; exact hpc
  obtain ⟨js'', s', h1, h2, h3, h5, h6⟩ := bcond_agree_f hw hc h4 h hcfg ht
  rw [hst] at h1; cases h1
  obtain ⟨q1, q2⟩ := fp_lift hf hfc h3 h6 hsame
  exact ⟨s', h2, h3, q1, h5, q2⟩

theorem fpStepOK_cb (hc : (w / 2 ^ 25) % 64 = 0b011010) : FPStepOK w := by
  intro js js' s h hf hcfg hfc hst hpc
  have hsame : FpSame js js' := by
    have hst1 := hst
    rw [Janus.Arm64.step_of_decode (decode_cb_class hw hc)] at hst1
    exact fp_exec_cb _ _ _ _ _ _ hst1
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_cb_class hw hc)] at hst'
  simp only [Janus.Arm64.exec] at hst'
  obtain ⟨js'', s', h1, h2, h3, h5, h6⟩ := cb_agree_f hw hc h hcfg (by
    intro hcnd; rw [if_pos hcnd] at hst'; cases hst'; exact hpc)
  rw [hst] at h1; cases h1
  obtain ⟨q1, q2⟩ := fp_lift hf hfc h3 h6 hsame
  exact ⟨s', h2, h3, q1, h5, q2⟩

theorem fpStepOK_tb (hc : (w / 2 ^ 25) % 64 = 0b011011) : FPStepOK w := by
  intro js js' s h hf hcfg hfc hst hpc
  have hsame : FpSame js js' := by
    have hst1 := hst
    rw [Janus.Arm64.step_of_decode (decode_tb_class hw hc)] at hst1
    exact fp_exec_tb _ _ _ _ _ _ _ hst1
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_tb_class hw hc)] at hst'
  simp only [Janus.Arm64.exec] at hst'
  obtain ⟨js'', s', h1, h2, h3, h5, h6⟩ := tb_agree_f hw hc h hcfg (by
    intro hcnd; rw [if_pos hcnd] at hst'; cases hst'; exact hpc)
  rw [hst] at h1; cases h1
  obtain ⟨q1, q2⟩ := fp_lift hf hfc h3 h6 hsame
  exact ⟨s', h2, h3, q1, h5, q2⟩

theorem fpStepOK_br (h0 : (w / 2 ^ 10) % 4194304 = 3508160) (h1 : w % 32 = 0) : FPStepOK w := by
  intro js js' s h hf hcfg hfc hst hpc
  have hsame : FpSame js js' := by
    have hst1 := hst
    rw [Janus.Arm64.step_of_decode (decode_br_class hw h0 h1)] at hst1
    exact fp_exec_br _ _ _ hst1
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_br_class hw h0 h1)] at hst'
  simp only [Janus.Arm64.exec, Janus.Arm64.branchReg] at hst'
  have ht : ¬ (js.readZR (Janus.Arm64.bits w 9 5)).toNat ≥ 2 ^ 56 := by
    intro hge; rw [if_pos hge] at hst'; cases hst'
  rw [if_neg ht] at hst'
  have hal : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0 := by
    by_cases hne : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0
    · exact hne
    · rw [if_neg hne] at hst'; cases hst'
  obtain ⟨js'', s', h2, h3, h4, h5, h6⟩ := br_agree_f hw h0 h1 h hcfg (by omega) hal
  rw [hst] at h2; cases h2
  obtain ⟨q1, q2⟩ := fp_lift hf hfc h4 h6 hsame
  exact ⟨s', h3, h4, q1, h5, q2⟩

theorem fpStepOK_blr (h0 : (w / 2 ^ 10) % 4194304 = 3510208) (h1 : w % 32 = 0) : FPStepOK w := by
  intro js js' s h hf hcfg hfc hst hpc
  have hsame : FpSame js js' := by
    have hst1 := hst
    rw [Janus.Arm64.step_of_decode (decode_blr_class hw h0 h1)] at hst1
    exact fp_exec_blr _ _ _ hst1
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_blr_class hw h0 h1)] at hst'
  simp only [Janus.Arm64.exec, Janus.Arm64.branchReg] at hst'
  have ht : ¬ (js.readZR (Janus.Arm64.bits w 9 5)).toNat ≥ 2 ^ 56 := by
    intro hge; rw [if_pos hge] at hst'; cases hst'
  rw [if_neg ht] at hst'
  have hal : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0 := by
    by_cases hne : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0
    · exact hne
    · rw [if_neg hne] at hst'; cases hst'
  obtain ⟨js'', s', h2, h3, h4, h5, h6⟩ := blr_agree_f hw h0 h1 h hcfg (by omega) hal
  rw [hst] at h2; cases h2
  obtain ⟨q1, q2⟩ := fp_lift hf hfc h4 h6 hsame
  exact ⟨s', h3, h4, q1, h5, q2⟩

theorem fpStepOK_ret (h0 : (w / 2 ^ 10) % 4194304 = 3512256) (h1 : w % 32 = 0) : FPStepOK w := by
  intro js js' s h hf hcfg hfc hst hpc
  have hsame : FpSame js js' := by
    have hst1 := hst
    rw [Janus.Arm64.step_of_decode (decode_ret_class hw h0 h1)] at hst1
    exact fp_exec_ret _ _ _ hst1
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_ret_class hw h0 h1)] at hst'
  simp only [Janus.Arm64.exec, Janus.Arm64.branchReg] at hst'
  have ht : ¬ (js.readZR (Janus.Arm64.bits w 9 5)).toNat ≥ 2 ^ 56 := by
    intro hge; rw [if_pos hge] at hst'; cases hst'
  rw [if_neg ht] at hst'
  have hal : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0 := by
    by_cases hne : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0
    · exact hne
    · rw [if_neg hne] at hst'; cases hst'
  obtain ⟨js'', s', h2, h3, h4, h5, h6⟩ := ret_agree_f hw h0 h1 h hcfg (by omega) hal
  rw [hst] at h2; cases h2
  obtain ⟨q1, q2⟩ := fp_lift hf hfc h4 h6 hsame
  exact ⟨s', h3, h4, q1, h5, q2⟩

end

end JanusASL.Proofs
