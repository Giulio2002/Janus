import JanusASL.Proofs.FP.DecodeFns2
import JanusASL.Proofs.FP.JanusDecode2
import JanusASL.Proofs.FPDecodeB

/-! # Proved: SCVTF, UCVTF (scalar, from W or X, to single or double precision) -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem scvtf_agree {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E)
    (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 64 = 0)
    (hop : (w / 2 ^ 16) % 8 = 2) (hrm : (w / 2 ^ 19) % 4 = 0)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ FPRel js' s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hdec : Janus.Arm64.decode w = some (.fpCvtInt (Janus.Arm64.bit w 31) (Janus.Arm64.bits w 23 22)
      (Janus.Arm64.bits w 20 19) (Janus.Arm64.bits w 18 16) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
    rw [decode_conv hw htop h21 h10 (by omega) (by omega)]
    exact decodeFpCvtInt_itof hft (by omega) hrm
  rw [Janus.Arm64.step_of_decode hdec] at hj
  simp only [Janus.Arm64.exec] at hj
  split at hj
  · cases hj
  · next js1 hx =>
    cases hj
    have hrd : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
    have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
    have hd32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
    have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
    have hop' : Janus.Arm64.bits w 18 16 = 2 := by simp only [bits_def]; omega
    have hrm' : Janus.Arm64.bits w 20 19 = 0 := by simp only [bits_def]; omega
    have hb : Janus.Arm64.bits w 23 22 = (w / 2 ^ 22) % 4 := by simp only [bits_def]
    have hsf : (fld w 31 1 == 1#1) = Janus.Arm64.bit w 31 := fld_bit w 31 hw
    rw [hop', hrm', hb] at hx
    rcases (by omega : (w / 2 ^ 22) % 4 = 0 ∨ (w / 2 ^ 22) % 4 = 1) with e | e <;> rw [e] at hx
    · refine fp_agree_core h hf hc hfc 296 _ ?_
        (fun s0 a b c d => run_exec_cvtf (Or.inl ⟨rfl, rfl⟩) (Janus.Arm64.bit w 31) false a b c d hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_scvtf hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (see_entry s _),
        show fld w 16 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 16 3 hw]; simp; omega),
        show fld w 19 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 19 2 hw]; simp; omega),
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        run_dec_scvtf_0 (fp_entry hf hfc w 296).1, hsf, hrd, hrn]
      all_goals rfl
    · refine fp_agree_core h hf hc hfc 296 _ ?_
        (fun s0 a b c d => run_exec_cvtf (Or.inr ⟨rfl, rfl⟩) (Janus.Arm64.bit w 31) false a b c d hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_scvtf hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (see_entry s _),
        show fld w 16 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 16 3 hw]; simp; omega),
        show fld w 19 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 19 2 hw]; simp; omega),
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        run_dec_scvtf_1 (fp_entry hf hfc w 296).1, hsf, hrd, hrn]
      all_goals rfl

theorem ucvtf_agree {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E)
    (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 64 = 0)
    (hop : (w / 2 ^ 16) % 8 = 3) (hrm : (w / 2 ^ 19) % 4 = 0)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ FPRel js' s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hdec : Janus.Arm64.decode w = some (.fpCvtInt (Janus.Arm64.bit w 31) (Janus.Arm64.bits w 23 22)
      (Janus.Arm64.bits w 20 19) (Janus.Arm64.bits w 18 16) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
    rw [decode_conv hw htop h21 h10 (by omega) (by omega)]
    exact decodeFpCvtInt_itof hft (by omega) hrm
  rw [Janus.Arm64.step_of_decode hdec] at hj
  simp only [Janus.Arm64.exec] at hj
  split at hj
  · cases hj
  · next js1 hx =>
    cases hj
    have hrd : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
    have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
    have hd32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
    have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
    have hop' : Janus.Arm64.bits w 18 16 = 3 := by simp only [bits_def]; omega
    have hrm' : Janus.Arm64.bits w 20 19 = 0 := by simp only [bits_def]; omega
    have hb : Janus.Arm64.bits w 23 22 = (w / 2 ^ 22) % 4 := by simp only [bits_def]
    have hsf : (fld w 31 1 == 1#1) = Janus.Arm64.bit w 31 := fld_bit w 31 hw
    rw [hop', hrm', hb] at hx
    rcases (by omega : (w / 2 ^ 22) % 4 = 0 ∨ (w / 2 ^ 22) % 4 = 1) with e | e <;> rw [e] at hx
    · refine fp_agree_core h hf hc hfc 297 _ ?_
        (fun s0 a b c d => run_exec_cvtf (Or.inl ⟨rfl, rfl⟩) (Janus.Arm64.bit w 31) true a b c d hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_ucvtf hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (see_entry s _),
        show fld w 16 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 16 3 hw]; simp; omega),
        show fld w 19 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 19 2 hw]; simp; omega),
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        run_dec_ucvtf_0 (fp_entry hf hfc w 297).1, hsf, hrd, hrn]
      all_goals rfl
    · refine fp_agree_core h hf hc hfc 297 _ ?_
        (fun s0 a b c d => run_exec_cvtf (Or.inr ⟨rfl, rfl⟩) (Janus.Arm64.bit w 31) true a b c d hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_ucvtf hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (see_entry s _),
        show fld w 16 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 16 3 hw]; simp; omega),
        show fld w 19 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 19 2 hw]; simp; omega),
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        run_dec_ucvtf_1 (fp_entry hf hfc w 297).1, hsf, hrd, hrn]
      all_goals rfl

end JanusASL.Proofs
