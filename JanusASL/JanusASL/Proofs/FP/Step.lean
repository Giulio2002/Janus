import JanusASL.Proofs.FP.Decode
import JanusASL.Proofs.LdSt

/-! # Assembling a floating-point step

A floating-point instruction's ASL execution changes at most PSTATE (NZCV), FPSR and the
V registers (`_Z`) and GPRs; `step_agree_fp` turns the decoder's run into `janus_step`'s with
`Rel`, `FPRel`, `LinuxEL0Config` and `FPConfig` after the step. -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem FPRel.of_same {js js' : Janus.Arm64.State} {s : SState} (h : FPRel js s) (hv : js'.vregs = js.vregs)
    (hc : js'.fpcr = js.fpcr) (hs : js'.fpsr = js.fpsr) : FPRel js' s := by
  obtain ⟨z, hz, hzv⟩ := h.z
  exact { z := ⟨z, hz, by rw [hv]; exact hzv⟩, fpcr := by rw [hc]; exact h.fpcr,
          fpcrRes0 := by rw [hc]; exact h.fpcrRes0, fpsr := by rw [hs]; exact h.fpsr }

/-- The registers a floating-point execute function may write. -/
def fpWriteRegs : List Register := [.PSTATE, .FPSR, ._Z]

theorem step_agree_fp {w : Nat} {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) {k : Int} {s2 : SState}
    (hrun : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2)
    (hr : Rel js1 s2) (hfr : FPRel js1 s2)
    (hg : ∀ r, isGprReg r = false → r ∉ fpWriteRegs → s2.regs.get? r = (entrySt s w k).regs.get? r)
    (hpc : js1.pc = js.pc) :
    (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK (s2.set ._PC (js.pc + 4)) ∧
      Rel js1.next (s2.set ._PC (js.pc + 4)) ∧ FPRel js1.next (s2.set ._PC (js.pc + 4)) ∧
      LinuxEL0Config (s2.set ._PC (js.pc + 4)) ∧ FPConfig (s2.set ._PC (js.pc + 4)) := by
  have hbt : s2.regs.get? .__BranchTaken = some false := by
    rw [hg _ rfl (by decide)]
    simp only [entrySt, stepEntry]; repeat rw [get?_set_ne _ _ (by decide)]
    exact get?_set_BranchTaken _ _
  have hpc2 : s2.regs.get? ._PC = some js.pc := by rw [hr.pc, hpc]
  have hnext : js1.next = { js1 with pc := js.pc + 4 } := by simp [Janus.Arm64.State.next, hpc]
  refine ⟨run_janus_step (BitVec.ofNat 32 w) h.pc hrun hbt hpc2, by rw [hnext]; exact hr.setPC _, ?_, ?_, ?_⟩
  · rw [hnext]
    exact (hfr.of_eq fun r hr' => get?_set_ne _ _ (fun e => by subst e; revert hr'; decide)).of_same rfl rfl rfl
  · obtain ⟨p, hp, hpp⟩ := hr.pstate
    refine LinuxEL0Config.of_frame (s := s) hc (fun r hr' hne => ?_) ⟨p, ?_, hpp.el, hpp.nrw, hpp.sp⟩
    · rw [get?_set_ne _ _ (fun e => by subst e; revert hr'; decide), hg r (cfgRegs_not_gpr r hr')
        (fun hm => by simp [fpWriteRegs] at hm; rcases hm with rfl | rfl | rfl <;> first | exact hne rfl | revert hr'; decide),
        entry_get s w k r (cfg_not_entry r hr')]
    · rw [get?_set_ne _ _ (by decide)]; exact hp
  · refine hfc.of_eq fun r hr' => ?_
    rw [get?_set_ne _ _ (fun e => by subst e; revert hr'; decide), hg r (by revert hr'; revert r; decide)
      (by revert hr'; revert r; decide), entry_get s w k r (by revert hr'; revert r; decide)]

end JanusASL.Proofs
