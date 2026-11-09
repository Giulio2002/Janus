import JanusASL.Proofs.FP.FCcmp
import JanusASL.Proofs.FP.JanusDecode2
import JanusASL.Proofs.FPDecodeB

/-! # Proved: FCCMP, FCCMPE (single and double precision) -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem decodeFloat_fpCcmp {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 1) :
    Janus.Arm64.decodeFloat w = some (.fpCcmp (Janus.Arm64.bits w 23 22) (Janus.Arm64.bits w 20 16)
      (Janus.Arm64.bits w 15 12) (Janus.Arm64.bit w 4) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 3 0)) := by
  have e1 : ¬ Janus.Arm64.bits w 23 22 ≥ 2 := by simp only [bits_def]; omega
  have e2 : (w &&& 0xFF000000 = 0x1F000000) = False := by
    apply propext; constructor
    · intro h; have := and_top_byte h; rw [htop] at this; exact absurd this (by decide)
    · intro h; exact h.elim
  have e3 := mask_FF200000 hw htop h21
  have e4 : Janus.Arm64.bits w 11 10 = 1 := by simp only [bits_def]; omega
  unfold Janus.Arm64.decodeFloat
  simp only [e1, ite_false, e2, e3, ite_true, e4]

theorem run_dec_fccmp_0 (nzcv : BitVec 4) (op : BitVec 1) (Rn : BitVec 5) (cond : BitVec 4) (Rm : BitVec 5) (st : SState) :
    (decode_fccmp_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm 0#2).run st =
      (execute_aarch64_instrs_float_compare_cond cond 32 nzcv Rm.toNat Rn.toNat (op == 1#1)).run st := by
  unfold decode_fccmp_float_aarch64_instrs_float_compare_cond
  cfg_simp
  all_goals rfl

theorem run_dec_fccmp_1 (nzcv : BitVec 4) (op : BitVec 1) (Rn : BitVec 5) (cond : BitVec 4) (Rm : BitVec 5) (st : SState) :
    (decode_fccmp_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm 1#2).run st =
      (execute_aarch64_instrs_float_compare_cond cond 64 nzcv Rm.toNat Rn.toNat (op == 1#1)).run st := by
  unfold decode_fccmp_float_aarch64_instrs_float_compare_cond
  cfg_simp
  all_goals rfl

theorem run_dec_fccmpe_0 (nzcv : BitVec 4) (op : BitVec 1) (Rn : BitVec 5) (cond : BitVec 4) (Rm : BitVec 5) (st : SState) :
    (decode_fccmpe_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm 0#2).run st =
      (execute_aarch64_instrs_float_compare_cond cond 32 nzcv Rm.toNat Rn.toNat (op == 1#1)).run st := by
  unfold decode_fccmpe_float_aarch64_instrs_float_compare_cond
  cfg_simp
  all_goals rfl

theorem run_dec_fccmpe_1 (nzcv : BitVec 4) (op : BitVec 1) (Rn : BitVec 5) (cond : BitVec 4) (Rm : BitVec 5) (st : SState) :
    (decode_fccmpe_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm 1#2).run st =
      (execute_aarch64_instrs_float_compare_cond cond 64 nzcv Rm.toNat Rn.toNat (op == 1#1)).run st := by
  unfold decode_fccmpe_float_aarch64_instrs_float_compare_cond
  cfg_simp
  all_goals rfl

theorem fld_nzcv (w : Nat) (hw : w < 2 ^ 32) : fld w 0 4 = BitVec.ofNat 4 (Janus.Arm64.bits w 3 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [fld_toNat w 0 4 hw, BitVec.toNat_ofNat]
  simp [bits_def]

set_option maxHeartbeats 4000000 in
theorem fccmp_agree {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 1)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ FPRel js' s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hdec : Janus.Arm64.decode w = some (.fpCcmp (Janus.Arm64.bits w 23 22) (Janus.Arm64.bits w 20 16)
      (Janus.Arm64.bits w 15 12) (Janus.Arm64.bit w 4) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 3 0)) := by
    rw [decode_float hw (.inl htop) (by omega)]; exact decodeFloat_fpCcmp hw htop hft h21 h10
  rw [Janus.Arm64.step_of_decode hdec] at hj
  simp only [Janus.Arm64.exec] at hj
  split at hj
  · cases hj
  · next js1 hx =>
    cases hj
    have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
    have hrm : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
    have hrc : (fld w 12 4).toNat = Janus.Arm64.bits w 15 12 := (bits_eq_fld w 15 12 hw).symm
    have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
    have hm32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
    have hb : Janus.Arm64.bits w 23 22 = (w / 2 ^ 22) % 4 := by simp only [bits_def]
    rw [← hrc] at hx
    rw [hb] at hx
    have hsig : (fld w 4 1 == 1#1) = Janus.Arm64.bit w 4 := fld_bit w 4 hw
    rcases (by omega : (w / 2 ^ 22) % 4 = 0 ∨ (w / 2 ^ 22) % 4 = 1) with e | e <;>
    rcases (by omega : (w / 2 ^ 4) % 2 = 0 ∨ (w / 2 ^ 4) % 2 = 1) with f | f <;> rw [e] at hx
    · refine fp_agree_core_ps h hf hc hfc 248 _ ?_
        (fun s0 a b c d => run_exec_fccmp (Or.inl ⟨rfl, rfl⟩) a b c d hm32 hn32 _ _ _ hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fccmp hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (see_entry s _),
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        run_dec_fccmp_0, hsig, fld_nzcv w hw, hrn, hrm]
      all_goals rfl
    · refine fp_agree_core_ps h hf hc hfc 249 _ ?_
        (fun s0 a b c d => run_exec_fccmp (Or.inl ⟨rfl, rfl⟩) a b c d hm32 hn32 _ _ _ hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fccmpe hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (see_entry s _),
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        run_dec_fccmpe_0, hsig, fld_nzcv w hw, hrn, hrm]
      all_goals rfl
    · refine fp_agree_core_ps h hf hc hfc 248 _ ?_
        (fun s0 a b c d => run_exec_fccmp (Or.inr ⟨rfl, rfl⟩) a b c d hm32 hn32 _ _ _ hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fccmp hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (see_entry s _),
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        run_dec_fccmp_1, hsig, fld_nzcv w hw, hrn, hrm]
      all_goals rfl
    · refine fp_agree_core_ps h hf hc hfc 249 _ ?_
        (fun s0 a b c d => run_exec_fccmp (Or.inr ⟨rfl, rfl⟩) a b c d hm32 hn32 _ _ _ hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fccmpe hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (see_entry s _),
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        run_dec_fccmpe_1, hsig, fld_nzcv w hw, hrn, hrm]
      all_goals rfl

end JanusASL.Proofs
