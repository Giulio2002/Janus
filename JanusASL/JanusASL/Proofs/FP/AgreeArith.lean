import JanusASL.Proofs.FP.DecodeFns
import JanusASL.Proofs.FP.JanusDecode2

/-! # Proved: FADD, FSUB, FMUL, FDIV, FMADD, FMSUB, FNMADD, FNMSUB, FSQRT (single and double precision) -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem bne_fld (w a b : Nat) (hw : w < 2 ^ 32) :
    (fld w a 1 != fld w b 1) = (Janus.Arm64.bit w a != Janus.Arm64.bit w b) := by
  rw [← fld_bit w a hw, ← fld_bit w b hw]
  generalize fld w a 1 = x; generalize fld w b 1 = y
  revert x y; decide

theorem fmul_agree {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 2) (hop : (w / 2 ^ 12) % 16 = 0)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ FPRel js' s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hdec : Janus.Arm64.decode w = some (.fpDP2 (Janus.Arm64.bits w 23 22) (Janus.Arm64.bits w 20 16)
      (Janus.Arm64.bits w 15 12) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
    rw [decode_float hw (.inl htop) (by omega)]; exact decodeFloat_fpDP2 hw htop hft h21 h10 (by omega)
  rw [Janus.Arm64.step_of_decode hdec] at hj
  simp only [Janus.Arm64.exec] at hj
  split at hj
  · cases hj
  · next js1 hx =>
    cases hj
    have hrd : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
    have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
    have hrm : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
    have hd32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
    have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
    have hm32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
    have hop' : Janus.Arm64.bits w 15 12 = 0 := by simp only [bits_def]; omega
    have hb : Janus.Arm64.bits w 23 22 = (w / 2 ^ 22) % 4 := by simp only [bits_def]
    rw [hop', hb] at hx
    rcases (by omega : (w / 2 ^ 22) % 4 = 0 ∨ (w / 2 ^ 22) % 4 = 1) with e | e <;> rw [e] at hx
    · refine fp_agree_core h hf hc hfc 410 _ ?_
        (fun s0 a b c d => run_exec_fmul (Or.inl ⟨rfl, rfl⟩) a b c d hm32 hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fmul hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (see_entry s _),
          show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          show fld w 15 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
          run_dec_fmul_0, hrd, hrn, hrm]
      all_goals rfl
    · refine fp_agree_core h hf hc hfc 410 _ ?_
        (fun s0 a b c d => run_exec_fmul (Or.inr ⟨rfl, rfl⟩) a b c d hm32 hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fmul hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (see_entry s _),
          show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          show fld w 15 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
          run_dec_fmul_1, hrd, hrn, hrm]
      all_goals rfl

theorem fdiv_agree {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 2) (hop : (w / 2 ^ 12) % 16 = 1)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ FPRel js' s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hdec : Janus.Arm64.decode w = some (.fpDP2 (Janus.Arm64.bits w 23 22) (Janus.Arm64.bits w 20 16)
      (Janus.Arm64.bits w 15 12) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
    rw [decode_float hw (.inl htop) (by omega)]; exact decodeFloat_fpDP2 hw htop hft h21 h10 (by omega)
  rw [Janus.Arm64.step_of_decode hdec] at hj
  simp only [Janus.Arm64.exec] at hj
  split at hj
  · cases hj
  · next js1 hx =>
    cases hj
    have hrd : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
    have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
    have hrm : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
    have hd32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
    have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
    have hm32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
    have hop' : Janus.Arm64.bits w 15 12 = 1 := by simp only [bits_def]; omega
    have hb : Janus.Arm64.bits w 23 22 = (w / 2 ^ 22) % 4 := by simp only [bits_def]
    rw [hop', hb] at hx
    rcases (by omega : (w / 2 ^ 22) % 4 = 0 ∨ (w / 2 ^ 22) % 4 = 1) with e | e <;> rw [e] at hx
    · refine fp_agree_core h hf hc hfc 344 _ ?_
        (fun s0 a b c d => run_exec_fdiv (Or.inl ⟨rfl, rfl⟩) a b c d hm32 hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fdiv hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (see_entry s _),
          show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          run_dec_fdiv_0, hrd, hrn, hrm]
      all_goals rfl
    · refine fp_agree_core h hf hc hfc 344 _ ?_
        (fun s0 a b c d => run_exec_fdiv (Or.inr ⟨rfl, rfl⟩) a b c d hm32 hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fdiv hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (see_entry s _),
          show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          run_dec_fdiv_1, hrd, hrn, hrm]
      all_goals rfl

theorem fadd_agree {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 2) (hop : (w / 2 ^ 12) % 16 = 2)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ FPRel js' s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hdec : Janus.Arm64.decode w = some (.fpDP2 (Janus.Arm64.bits w 23 22) (Janus.Arm64.bits w 20 16)
      (Janus.Arm64.bits w 15 12) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
    rw [decode_float hw (.inl htop) (by omega)]; exact decodeFloat_fpDP2 hw htop hft h21 h10 (by omega)
  rw [Janus.Arm64.step_of_decode hdec] at hj
  simp only [Janus.Arm64.exec] at hj
  split at hj
  · cases hj
  · next js1 hx =>
    cases hj
    have hrd : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
    have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
    have hrm : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
    have hd32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
    have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
    have hm32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
    have hop' : Janus.Arm64.bits w 15 12 = 2 := by simp only [bits_def]; omega
    have hb : Janus.Arm64.bits w 23 22 = (w / 2 ^ 22) % 4 := by simp only [bits_def]
    rw [hop', hb] at hx
    rcases (by omega : (w / 2 ^ 22) % 4 = 0 ∨ (w / 2 ^ 22) % 4 = 1) with e | e <;> rw [e] at hx
    · refine fp_agree_core h hf hc hfc 243 _ ?_
        (fun s0 a b c d => run_exec_addsub (Or.inl ⟨rfl, rfl⟩) false a b c d hm32 hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fadd hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (see_entry s _),
          show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          show fld w 12 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 1 hw]; simp; omega),
          run_dec_fadd_0, hrd, hrn, hrm]
      all_goals rfl
    · refine fp_agree_core h hf hc hfc 243 _ ?_
        (fun s0 a b c d => run_exec_addsub (Or.inr ⟨rfl, rfl⟩) false a b c d hm32 hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fadd hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (see_entry s _),
          show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          show fld w 12 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 1 hw]; simp; omega),
          run_dec_fadd_1, hrd, hrn, hrm]
      all_goals rfl

theorem fsub_agree {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 2) (hop : (w / 2 ^ 12) % 16 = 3)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ FPRel js' s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hdec : Janus.Arm64.decode w = some (.fpDP2 (Janus.Arm64.bits w 23 22) (Janus.Arm64.bits w 20 16)
      (Janus.Arm64.bits w 15 12) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
    rw [decode_float hw (.inl htop) (by omega)]; exact decodeFloat_fpDP2 hw htop hft h21 h10 (by omega)
  rw [Janus.Arm64.step_of_decode hdec] at hj
  simp only [Janus.Arm64.exec] at hj
  split at hj
  · cases hj
  · next js1 hx =>
    cases hj
    have hrd : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
    have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
    have hrm : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
    have hd32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
    have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
    have hm32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
    have hop' : Janus.Arm64.bits w 15 12 = 3 := by simp only [bits_def]; omega
    have hb : Janus.Arm64.bits w 23 22 = (w / 2 ^ 22) % 4 := by simp only [bits_def]
    rw [hop', hb] at hx
    rcases (by omega : (w / 2 ^ 22) % 4 = 0 ∨ (w / 2 ^ 22) % 4 = 1) with e | e <;> rw [e] at hx
    · refine fp_agree_core h hf hc hfc 244 _ ?_
        (fun s0 a b c d => run_exec_addsub (Or.inl ⟨rfl, rfl⟩) true a b c d hm32 hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fsub hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (see_entry s _),
          show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          show fld w 12 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 1 hw]; simp; omega),
          run_dec_fsub_0, hrd, hrn, hrm]
      all_goals rfl
    · refine fp_agree_core h hf hc hfc 244 _ ?_
        (fun s0 a b c d => run_exec_addsub (Or.inr ⟨rfl, rfl⟩) true a b c d hm32 hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fsub hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (see_entry s _),
          show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
          show fld w 12 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 1 hw]; simp; omega),
          run_dec_fsub_1, hrd, hrn, hrm]
      all_goals rfl

end JanusASL.Proofs
