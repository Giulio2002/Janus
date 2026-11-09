import JanusASL.Proofs.FpSame.Base

namespace JanusASL.FpS
open Janus.Arm64

theorem fp_branchReg (s s' : State) (t : W64) (h : branchReg s t = .ok s') : FpSame s s' := by
  unfold branchReg at h
  split at h
  · cases h
  · split at h
    · cases h; exact ⟨rfl, rfl, rfl⟩
    · cases h

theorem fp_exec_b (op : Bool) (imm26 : Nat) (js js' : State) (h : exec (.b op imm26) js = .ok js') :
    FpSame js js' := by
  simp only [exec] at h
  cases h
  dsimp only [FpSame]
  split <;> simp only [writeZR_vregs, writeZR_fpcr, writeZR_fpsr, and_self]

theorem fp_exec_bcond (imm19 cond : Nat) (js js' : State) (h : exec (.bcond imm19 cond) js = .ok js') :
    FpSame js js' := by
  simp only [exec] at h
  split at h <;> cases h <;> exact ⟨rfl, rfl, rfl⟩

theorem fp_exec_cb (sf op : Bool) (imm19 rt : Nat) (js js' : State) (h : exec (.cb sf op imm19 rt) js = .ok js') :
    FpSame js js' := by
  simp only [exec] at h
  split at h <;> split at h <;> cases h <;> exact ⟨rfl, rfl, rfl⟩

theorem fp_exec_tb (b5 op : Bool) (b40 imm14 rt : Nat) (js js' : State)
    (h : exec (.tb b5 op b40 imm14 rt) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  split at h <;> cases h <;> exact ⟨rfl, rfl, rfl⟩

theorem fp_exec_br (rn : Nat) (js js' : State) (h : exec (.br rn) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  exact fp_branchReg _ _ _ h

theorem fp_exec_ret (rn : Nat) (js js' : State) (h : exec (.ret rn) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  exact fp_branchReg _ _ _ h

theorem fp_exec_blr (rn : Nat) (js js' : State) (h : exec (.blr rn) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  have := fp_branchReg _ _ _ h
  exact ⟨by rw [this.1]; exact writeZR_vregs .., by rw [this.2.1]; exact writeZR_fpcr .., by rw [this.2.2]; exact writeZR_fpsr ..⟩

end JanusASL.FpS
