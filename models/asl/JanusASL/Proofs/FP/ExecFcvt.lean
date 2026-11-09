import JanusASL.Proofs.FP.FPConvert
import JanusASL.Proofs.FP.Exec2

/-! # FCVT between single and double precision: the execute function -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_exec_fcvt {N M ftype opcode : Nat}
    (hft : (ftype = 0 ∧ opcode = 5 ∧ N = 32 ∧ M = 64) ∨ (ftype = 1 ∧ opcode = 4 ∧ N = 64 ∧ M = 32))
    {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) {rn rd : Nat} (hn : rn < 32) (hd : rd < 32)
    (hj : Janus.Arm64.execFpDP1 js ftype opcode rn rd = .ok js1) :
    ∃ s', (execute_aarch64_instrs_float_convert_fp rd M rn N).run s = .ok () s' ∧ Rel js1 s' ∧ FPRel js1 s' ∧
      (∀ r, r ≠ ._Z → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) ∧ SMZero s' := by
  have hNM : (N = 32 ∧ M = 64) ∨ (N = 64 ∧ M = 32) := by rcases hft with ⟨_, _, a, b⟩ | ⟨_, _, a, b⟩ <;> simp [a, b]
  have hN : N = 32 ∨ N = 64 := by omega
  have hM : M = 32 ∨ M = 64 := by omega
  have hfmt : Janus.Arm64.ftypeFmt ftype = fmtN N ∧ Janus.Arm64.ftypeSize ftype = N := by
    rcases hft with ⟨rfl, _, rfl, _⟩ | ⟨rfl, _, rfl, _⟩ <;> simp [Janus.Arm64.ftypeFmt, Janus.Arm64.ftypeSize, fmtN]
  obtain ⟨hfmt1, hsz⟩ := hfmt
  have hjc : Janus.Arm64.fpCommit js
      (Janus.Arm64.FP.fpConvert (fmtN N) (fmtN M) js.fpcr.toNat (Janus.Arm64.FP.roundingMode js.fpcr.toNat)
        (js.getV rn N)).2
      (js.setScalar rd M (js.mergeBase rd)
        (Janus.Arm64.FP.fpConvert (fmtN N) (fmtN M) js.fpcr.toNat (Janus.Arm64.FP.roundingMode js.fpcr.toNat)
          (js.getV rn N)).1) = .ok js1 := by
    unfold Janus.Arm64.execFpDP1 at hj
    rcases hft with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · simpa [Janus.Arm64.ftypeFmt, Janus.Arm64.ftypeSize, fmtN, Janus.Float.binary32, Janus.Float.binary64] using hj
    · simpa [Janus.Arm64.ftypeFmt, Janus.Arm64.ftypeSize, fmtN, Janus.Float.binary32, Janus.Float.binary64] using hj
  have e : execute_aarch64_instrs_float_convert_fp rd M rn N =
      (do CheckFPEnabled64 ()
          let a ← V_read (rn : Int) N
          let fpcr ← FPCR_read ()
          scalarTail rd rd fpcr (FPConvert__1 a fpcr M)) := by
    simp only [execute_aarch64_instrs_float_convert_fp, scalarTail]
    simp
  have hv1 := run_V_read hf hn (w := N) (by omega)
  have hfcr := run_FPCR_read hf
  have hchk := run_CheckFPEnabled64 hc hfc
  have hlt := fpConvert_lt (fmtN N) (fmtN M) js.fpcr.toNat (Janus.Arm64.FP.roundingMode js.fpcr.toNat) (js.getV rn N)
  obtain ⟨s', hs', p1, p2, p3, p4⟩ := run_exec_generic hM h hf hc hfc hd hd _ hlt hjc
    (FPConvert__1 (BitVec.ofNat N (js.getV rn N)) (js.fpcr.setWidth 64) M)
    (fun v hnt => by
      have := run_FPConvert hNM hc hfc.sm (BitVec.ofNat N (js.getV rn N)) (js.fpcr.setWidth 64) v
        (by rw [getV_ofNat, hfn_fpcr]; rw [hfn_fpcr] at hnt; exact hnt)
      rw [getV_ofNat, hfn_fpcr] at this
      unfold FPConvert__1
      simp only [EStateM.run_bind, run_FPRoundingMode, hfn_fpcr, this])
  refine ⟨s', ?_, p1, p2, p3, p4⟩
  rw [e]
  simp only [run_bind, hchk, hv1, hfcr, hs']

end JanusASL.Proofs
