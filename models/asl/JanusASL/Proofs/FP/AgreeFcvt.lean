import JanusASL.Proofs.FP.DecodeFns2
import JanusASL.Proofs.FP.JanusDecode2
import JanusASL.Proofs.FPDecodeB

/-! # Proved: FCVT between single and double precision -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem fcvt_agree {w : Nat} (hw : w < 2 ^ 32) (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 32 = 16)
    (hop : ((w / 2 ^ 15) % 64 = 4 ∧ (w / 2 ^ 22) % 4 = 1) ∨ ((w / 2 ^ 15) % 64 = 5 ∧ (w / 2 ^ 22) % 4 = 0))
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ FPRel js' s' ∧
      LinuxEL0Config s' ∧ FPConfig s' := by
  have hdec : Janus.Arm64.decode w = some (.fpDP1 (Janus.Arm64.bits w 23 22) (Janus.Arm64.bits w 20 15)
      (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
    rw [decode_float hw (.inl htop) (by omega)]
    exact decodeFloat_fpDP1_cvt hw htop hft h21 h10 hop
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
    have hb : Janus.Arm64.bits w 23 22 = (w / 2 ^ 22) % 4 := by simp only [bits_def]
    have ho : Janus.Arm64.bits w 20 15 = (w / 2 ^ 15) % 64 := by simp only [bits_def]
    rw [hb, ho] at hx
    rcases hop with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a, b] at hx
      refine fp_agree_core h hf hc hfc 275 _ ?_
        (fun s0 a b c d => run_exec_fcvt (Or.inr ⟨rfl, rfl, rfl, rfl⟩) a b c d hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fcvt_ds hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (see_entry s _),
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 15 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 2 hw]; simp; omega),
        run_dec_fcvt_ds, hrd, hrn]
    · rw [a, b] at hx
      refine fp_agree_core h hf hc hfc 275 _ ?_
        (fun s0 a b c d => run_exec_fcvt (Or.inl ⟨rfl, rfl, rfl, rfl⟩) a b c d hn32 hd32 hx)
      rw [run_DecodeA64_FP hw (by omega), run_FP_fcvt_sd hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (see_entry s _),
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 15 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 2 hw]; simp; omega),
        run_dec_fcvt_sd, hrd, hrn]

end JanusASL.Proofs
