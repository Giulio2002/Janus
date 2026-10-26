import JanusASL.Proofs.FP.Step
import JanusASL.Proofs.FP.JanusDecode
import JanusASL.Proofs.FPDecode

/-! # Proved: FCMP, FCMPE (single and double precision, register and `#0.0` forms) -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem access_fld (w lo len i : Nat) (hw : w < 2 ^ 32) (hi : i < len) :
    (Sail.BitVec.access (fld w lo len) i == 1#1) = decide ((w / 2 ^ (lo + i)) % 2 = 1) := by
  rw [access_eq _ i hi, fld_toNat w lo len hw, ← Nat.testBit_eq_decide_div_mod_eq,
    ← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hi, Nat.add_comm]
  cases w.testBit (lo + i) <;> decide

theorem fp_entry {js : Janus.Arm64.State} {s : SState} (hf : FPRel js s) (hfc : FPConfig s) (w : Nat) (k : Int) :
    FPRel js (entrySt s w k) ∧ FPConfig (entrySt s w k) :=
  ⟨hf.of_eq fun r hr => entry_get s w k r (by revert hr; revert r; decide),
   hfc.of_eq fun r hr => entry_get s w k r (by revert hr; revert r; decide)⟩

theorem fpCommit_pc {s t t' : Janus.Arm64.State} {e : Janus.Arm64.FP.Exc}
    (h : Janus.Arm64.fpCommit s e t = .ok t') : t'.pc = t.pc := by
  unfold Janus.Arm64.fpCommit at h
  split at h
  · cases h
  · cases h; rfl

theorem execFpCmp_pc {js js1 : Janus.Arm64.State} {ft rm opc rn : Nat}
    (h : Janus.Arm64.execFpCmp js ft rm opc rn = .ok js1) : js1.pc = js.pc := by
  unfold Janus.Arm64.execFpCmp at h
  have := fpCommit_pc h
  exact this

set_option maxHeartbeats 16000000 in
/-- **FCMP, FCMPE** (`0 0 0 11110 ftype 1 Rm 00 1000 Rn opc 000`, single and double precision,
register and `#0.0` forms; with `#0.0`, `Rm = 00000`): for every related pair of states (the
integer `Rel`, the floating-point `FPRel`) under `LinuxEL0Config` and `FPConfig`, whenever Janus
steps the word the generated ASL step completes in a related state. -/
theorem fcmp_agree {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 16 = 8) (h14 : (w / 2 ^ 14) % 4 = 0) (h0 : w % 8 = 0)
    (hz : (w / 2 ^ 3) % 2 = 1 → (w / 2 ^ 16) % 32 = 0)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ FPRel js' s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hdec : Janus.Arm64.decode w = some (.fpCmp (Janus.Arm64.bits w 23 22) (Janus.Arm64.bits w 20 16)
      (Janus.Arm64.bits w 4 3) (Janus.Arm64.bits w 9 5)) := by
    rw [decode_float hw (.inl htop) (by omega)]; exact decodeFloat_fpCmp hw htop hft h21 h10 h14 h0 hz
  rw [Janus.Arm64.step_of_decode hdec] at hj
  simp only [Janus.Arm64.exec] at hj
  split at hj
  · cases hj
  · next js1 hx =>
    cases hj
    have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
    have hrm : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
    have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
    have hm32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
    have ha0 : (Sail.BitVec.access (fld w 3 2) 0 == 1#1) = decide (Janus.Arm64.bits w 4 3 % 2 = 1) := by
      rw [access_fld w 3 2 0 hw (by decide)]; simp only [bits_def]; congr 1; apply propext; omega
    have ha1 : (Sail.BitVec.access (fld w 3 2) 1 == 1#1) = decide (Janus.Arm64.bits w 4 3 / 2 % 2 = 1) := by
      rw [access_fld w 3 2 1 hw (by decide)]; simp only [bits_def]; congr 1; apply propext; omega
    have hb : Janus.Arm64.bits w 23 22 = (w / 2 ^ 22) % 4 := by simp only [bits_def]
    rw [hb] at hx
    rcases (by omega : (w / 2 ^ 22) % 4 = 0 ∨ (w / 2 ^ 22) % 4 = 1) with e | e <;>
    rcases (by omega : (w / 2 ^ 4) % 2 = 0 ∨ (w / 2 ^ 4) % 2 = 1) with f | f <;> rw [e] at hx
    · -- ftype 0, fcmp
      have hRe := h.entry (BitVec.ofNat 32 w) 272
      have hce : LinuxEL0Config (entrySt s w 272) := hc.of_eq fun r hr => entry_get s w 272 r (cfg_not_entry r hr)
      obtain ⟨hfe, hfce⟩ := fp_entry hf hfc w 272
      obtain ⟨s2, hrun2, hr2, hfr2, hg2, hsm2⟩ := run_exec_fcmp32 hRe hfe hce hfce hm32 hn32 hx
      have hdec2 : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
          (execute_aarch64_instrs_float_compare_uncond (decide (Janus.Arm64.bits w 4 3 % 2 = 1)) 32
            (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 9 5)
            (decide (Janus.Arm64.bits w 4 3 / 2 % 2 = 1))).run (entrySt s w 272) := by
        rw [run_DecodeA64_FP hw (by omega), run_FP_fcmp hw (by omega) (by omega) (by omega) (by omega) h21 h14 h10
          (by omega) f (see_entry s _),
          show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          run_dec_fcmp_0, ha0, ha1, hrn, hrm]
      obtain ⟨e1, e2, e3, e4, e5⟩ := step_agree_fp h hc hfc (k := 272) (hdec2.trans hrun2) hr2 hfr2
        (fun r _ hn => hg2 r (fun e => hn (by subst e; decide)) (fun e => hn (by subst e; decide)))
        (execFpCmp_pc hx) hsm2
      exact ⟨_, e1, e2, e3, e4, e5⟩
    · -- ftype 0, fcmpe
      have hRe := h.entry (BitVec.ofNat 32 w) 273
      have hce : LinuxEL0Config (entrySt s w 273) := hc.of_eq fun r hr => entry_get s w 273 r (cfg_not_entry r hr)
      obtain ⟨hfe, hfce⟩ := fp_entry hf hfc w 273
      obtain ⟨s2, hrun2, hr2, hfr2, hg2, hsm2⟩ := run_exec_fcmp32 hRe hfe hce hfce hm32 hn32 hx
      have hdec2 : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
          (execute_aarch64_instrs_float_compare_uncond (decide (Janus.Arm64.bits w 4 3 % 2 = 1)) 32
            (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 9 5)
            (decide (Janus.Arm64.bits w 4 3 / 2 % 2 = 1))).run (entrySt s w 273) := by
        rw [run_DecodeA64_FP hw (by omega), run_FP_fcmpe hw (by omega) (by omega) (by omega) (by omega) h21 h14 h10
          (by omega) f (see_entry s _),
          show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          run_dec_fcmpe_0, ha0, ha1, hrn, hrm]
      obtain ⟨e1, e2, e3, e4, e5⟩ := step_agree_fp h hc hfc (k := 273) (hdec2.trans hrun2) hr2 hfr2
        (fun r _ hn => hg2 r (fun e => hn (by subst e; decide)) (fun e => hn (by subst e; decide)))
        (execFpCmp_pc hx) hsm2
      exact ⟨_, e1, e2, e3, e4, e5⟩
    · -- ftype 1, fcmp
      have hRe := h.entry (BitVec.ofNat 32 w) 272
      have hce : LinuxEL0Config (entrySt s w 272) := hc.of_eq fun r hr => entry_get s w 272 r (cfg_not_entry r hr)
      obtain ⟨hfe, hfce⟩ := fp_entry hf hfc w 272
      obtain ⟨s2, hrun2, hr2, hfr2, hg2, hsm2⟩ := run_exec_fcmp64 hRe hfe hce hfce hm32 hn32 hx
      have hdec2 : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
          (execute_aarch64_instrs_float_compare_uncond (decide (Janus.Arm64.bits w 4 3 % 2 = 1)) 64
            (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 9 5)
            (decide (Janus.Arm64.bits w 4 3 / 2 % 2 = 1))).run (entrySt s w 272) := by
        rw [run_DecodeA64_FP hw (by omega), run_FP_fcmp hw (by omega) (by omega) (by omega) (by omega) h21 h14 h10
          (by omega) f (see_entry s _),
          show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          run_dec_fcmp_1, ha0, ha1, hrn, hrm]
      obtain ⟨e1, e2, e3, e4, e5⟩ := step_agree_fp h hc hfc (k := 272) (hdec2.trans hrun2) hr2 hfr2
        (fun r _ hn => hg2 r (fun e => hn (by subst e; decide)) (fun e => hn (by subst e; decide)))
        (execFpCmp_pc hx) hsm2
      exact ⟨_, e1, e2, e3, e4, e5⟩
    · -- ftype 1, fcmpe
      have hRe := h.entry (BitVec.ofNat 32 w) 273
      have hce : LinuxEL0Config (entrySt s w 273) := hc.of_eq fun r hr => entry_get s w 273 r (cfg_not_entry r hr)
      obtain ⟨hfe, hfce⟩ := fp_entry hf hfc w 273
      obtain ⟨s2, hrun2, hr2, hfr2, hg2, hsm2⟩ := run_exec_fcmp64 hRe hfe hce hfce hm32 hn32 hx
      have hdec2 : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
          (execute_aarch64_instrs_float_compare_uncond (decide (Janus.Arm64.bits w 4 3 % 2 = 1)) 64
            (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 9 5)
            (decide (Janus.Arm64.bits w 4 3 / 2 % 2 = 1))).run (entrySt s w 273) := by
        rw [run_DecodeA64_FP hw (by omega), run_FP_fcmpe hw (by omega) (by omega) (by omega) (by omega) h21 h14 h10
          (by omega) f (see_entry s _),
          show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          run_dec_fcmpe_1, ha0, ha1, hrn, hrm]
      obtain ⟨e1, e2, e3, e4, e5⟩ := step_agree_fp h hc hfc (k := 273) (hdec2.trans hrun2) hr2 hfr2
        (fun r _ hn => hg2 r (fun e => hn (by subst e; decide)) (fun e => hn (by subst e; decide)))
        (execFpCmp_pc hx) hsm2
      exact ⟨_, e1, e2, e3, e4, e5⟩

end JanusASL.Proofs
