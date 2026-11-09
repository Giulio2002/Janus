import JanusASL.Proofs.FP.FCmpCls
import JanusASL.Proofs.FP.Exec2
import JanusASL.Proofs.FPDecodeA

/-! # Assembling the agreement of a scalar floating-point instruction

`fp_agree_core`: if the decoder reaches the execute function `E` (at SEE `k`) and `E` completes in related states
whenever it starts from related, configured states, then `janus_step` completes in related states. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem fp_agree_core {w : Nat} {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s)
    (hc : LinuxEL0Config s) (hfc : FPConfig s) (k : Int) (E : SailM Unit)
    (hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      E.run (entrySt s w k))
    (hexec : ∀ s0 : SState, Rel js s0 → FPRel js s0 → LinuxEL0Config s0 → FPConfig s0 →
      ∃ s2, E.run s0 = .ok () s2 ∧ Rel js1 s2 ∧ FPRel js1 s2 ∧
        (∀ r, r ≠ ._Z → r ≠ .FPSR → s2.regs.get? r = s0.regs.get? r) ∧ SMZero s2)  :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js1.next s' ∧ FPRel js1.next s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hRe := h.entry (BitVec.ofNat 32 w) k
  have hce : LinuxEL0Config (entrySt s w k) := hc.of_eq fun r hr => entry_get s w k r (cfg_not_entry r hr)
  obtain ⟨hfe, hfce⟩ := fp_entry hf hfc w k
  obtain ⟨s2, hrun2, hr2, hfr2, hg2, hsm2⟩ := hexec _ hRe hfe hce hfce
  have hpc : js1.pc = js.pc := by
    have h1 := hr2.pc
    rw [hg2 ._PC (by decide) (by decide), hRe.pc] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨e1, e2, e3, e4, e5⟩ := step_agree_fp h hc hfc (k := k) (hdec.trans hrun2) hr2 hfr2
    (fun r _ hn => hg2 r (fun e => hn (by subst e; decide)) (fun e => hn (by subst e; decide))) hpc hsm2
  exact ⟨_, e1, e2, e3, e4, e5⟩

theorem fp_agree_core_ps {w : Nat} {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s)
    (hc : LinuxEL0Config s) (hfc : FPConfig s) (k : Int) (E : SailM Unit)
    (hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      E.run (entrySt s w k))
    (hexec : ∀ s0 : SState, Rel js s0 → FPRel js s0 → LinuxEL0Config s0 → FPConfig s0 →
      ∃ s2, E.run s0 = .ok () s2 ∧ Rel js1 s2 ∧ FPRel js1 s2 ∧
        (∀ r, r ≠ .PSTATE → r ≠ .FPSR → s2.regs.get? r = s0.regs.get? r) ∧ SMZero s2)  :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js1.next s' ∧ FPRel js1.next s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hRe := h.entry (BitVec.ofNat 32 w) k
  have hce : LinuxEL0Config (entrySt s w k) := hc.of_eq fun r hr => entry_get s w k r (cfg_not_entry r hr)
  obtain ⟨hfe, hfce⟩ := fp_entry hf hfc w k
  obtain ⟨s2, hrun2, hr2, hfr2, hg2, hsm2⟩ := hexec _ hRe hfe hce hfce
  have hpc : js1.pc = js.pc := by
    have h1 := hr2.pc
    rw [hg2 ._PC (by decide) (by decide), hRe.pc] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨e1, e2, e3, e4, e5⟩ := step_agree_fp h hc hfc (k := k) (hdec.trans hrun2) hr2 hfr2
    (fun r _ hn => hg2 r (fun e => hn (by subst e; decide)) (fun e => hn (by subst e; decide))) hpc hsm2
  exact ⟨_, e1, e2, e3, e4, e5⟩

theorem fp_agree_core_gpr {w : Nat} {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s)
    (hc : LinuxEL0Config s) (hfc : FPConfig s) (k : Int) (E : SailM Unit)
    (hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      E.run (entrySt s w k))
    (hexec : ∀ s0 : SState, Rel js s0 → FPRel js s0 → LinuxEL0Config s0 → FPConfig s0 →
      ∃ s2, E.run s0 = .ok () s2 ∧ Rel js1 s2 ∧ FPRel js1 s2 ∧
        (∀ r, isGprReg r = false → r ≠ .FPSR → s2.regs.get? r = s0.regs.get? r) ∧ SMZero s2)  :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js1.next s' ∧ FPRel js1.next s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hRe := h.entry (BitVec.ofNat 32 w) k
  have hce : LinuxEL0Config (entrySt s w k) := hc.of_eq fun r hr => entry_get s w k r (cfg_not_entry r hr)
  obtain ⟨hfe, hfce⟩ := fp_entry hf hfc w k
  obtain ⟨s2, hrun2, hr2, hfr2, hg2, hsm2⟩ := hexec _ hRe hfe hce hfce
  have hpc : js1.pc = js.pc := by
    have h1 := hr2.pc
    rw [hg2 ._PC (by decide) (by decide), hRe.pc] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨e1, e2, e3, e4, e5⟩ := step_agree_fp h hc hfc (k := k) (hdec.trans hrun2) hr2 hfr2
    (fun r hg hn => hg2 r hg (fun e => hn (by subst e; decide))) hpc hsm2
  exact ⟨_, e1, e2, e3, e4, e5⟩

end JanusASL.Proofs
