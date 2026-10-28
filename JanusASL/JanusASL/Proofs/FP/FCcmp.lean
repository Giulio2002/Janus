import JanusASL.Proofs.FP.FCmp
import JanusASL.Proofs.FP.Agree
import JanusASL.Proofs.Cond

/-! # FCCMP / FCCMPE: the execute function -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- The post-state facts of an operation that sets `NZCV` from `k` and ORs `e` into FPSR. -/
theorem fp_flags_post {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hfc : FPConfig s)
    {p : ProcState} (hp : s.regs.get? .PSTATE = some p) (k e : Nat) (he : e < 2 ^ 32) :
    Rel { js with flags := Janus.Arm64.flagsOfNzcv k, fpsr := js.fpsr ||| BitVec.ofNat 32 e }
        ((s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e)).set .PSTATE (psNZCV p k)) ∧
    FPRel { js with flags := Janus.Arm64.flagsOfNzcv k, fpsr := js.fpsr ||| BitVec.ofNat 32 e }
        ((s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e)).set .PSTATE (psNZCV p k)) ∧
    (∀ x, x ≠ .PSTATE → x ≠ .FPSR →
      ((s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e)).set .PSTATE (psNZCV p k)).regs.get? x = s.regs.get? x) ∧
    SMZero ((s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e)).set .PSTATE (psNZCV p k)) := by
  refine ⟨?_, ?_, ?_, smz_psNZCV hfc hp _ _⟩
  · have h1 := (h.set_other .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e) rfl (by decide) (by decide)
      (by decide)).setFlags ((get?_set_ne s _ (by decide)).trans hp) (Janus.Arm64.flagsOfNzcv k)
    refine Rel.of_same (js := js.setFlags (Janus.Arm64.flagsOfNzcv k)) ?_ rfl rfl rfl rfl
    rw [psNZCV_eq]; exact h1
  · obtain ⟨z, hz0, hzv⟩ := hf.z
    refine { z := ⟨z, ?_, hzv⟩, fpcr := ?_, fpcrRes0 := hf.fpcrRes0, fpsr := ?_ }
    · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hz0
    · rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hf.fpcr
    · rw [get?_set_ne _ _ (by decide), get?_set_FPSR]
      show _ = some ((js.fpsr ||| BitVec.ofNat 32 e).setWidth 64)
      rw [fpsr_or_cast js.fpsr e he]
  · intro x hx1 hx2
    rw [get?_set_ne _ _ (Ne.symm hx1), get?_set_ne _ _ (Ne.symm hx2)]

theorem run_FPCompareN {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (op1 op2 : BitVec N)
    (sig : Bool) (fpcr : BitVec 64) {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs)
    (hIO : Nat.testBit (Janus.Arm64.FP.fpCompare (fmtN N) fpcr.toNat sig op1.toNat op2.toNat).2.proc 0 = true →
      fpcr.getLsbD 8 = false)
    (hID : Nat.testBit (Janus.Arm64.FP.fpCompare (fmtN N) fpcr.toNat sig op1.toNat op2.toNat).2.proc 7 = true →
      fpcr.getLsbD 15 = false) :
    (FPCompare op1 op2 sig fpcr).run s =
      let r := Janus.Arm64.FP.fpCompare (fmtN N) fpcr.toNat sig op1.toNat op2.toNat
      .ok (BitVec.ofNat 4 r.1) (s.set .FPSR (xs ||| BitVec.ofNat 64 r.2.proc)) := by
  rcases hN with rfl | rfl
  · exact run_FPCompare32 hc op1 op2 sig fpcr hx hIO hID
  · exact run_FPCompare64 hc op1 op2 sig fpcr hx hIO hID

set_option maxHeartbeats 4000000 in
theorem run_exec_fccmp {N ftype : Nat} (hft : (ftype = 0 ∧ N = 32) ∨ (ftype = 1 ∧ N = 64))
    {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) {rm rn : Nat} (hm : rm < 32) (hn : rn < 32) (cond : BitVec 4) (k : Nat) (signal : Bool)
    (hj : Janus.Arm64.execFpCcmp js ftype rm (Janus.Arm64.conditionHolds cond.toNat js.flags) signal rn k = .ok js1) :
    ∃ s', (execute_aarch64_instrs_float_compare_cond cond N (BitVec.ofNat 4 k) rm rn signal).run s = .ok () s' ∧
      Rel js1 s' ∧ FPRel js1 s' ∧ (∀ r, r ≠ .PSTATE → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) ∧ SMZero s' := by
  obtain ⟨hfmt, hsz⟩ := ftype_fmt hft
  have hN : N = 32 ∨ N = 64 := by rcases hft with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨p, hp, hpp⟩ := h.pstate
  unfold Janus.Arm64.execFpCcmp at hj
  have hpv : ∀ v, (s.set .FPSR v).regs.get? .PSTATE = some p := fun v => (get?_set_ne s v (by decide)).trans hp
  have hv1 := run_V_read hf hn (w := N) (by omega)
  have hv2 := run_V_read hf hm (w := N) (by omega)
  have hchk := run_CheckFPEnabled64 hc hfc
  have hcond := run_ConditionHolds hp hpp cond
  have hspe : ∀ v q, ((s.set .FPSR v).set .PSTATE q).regs.get? .SPESampleInFlight = some false := fun v q => by
    rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; exact hc.speInFlight
  have hspe1 : ∀ q, (s.set .PSTATE q).regs.get? .SPESampleInFlight = some false := fun q => by
    rw [get?_set_ne _ _ (by decide)]; exact hc.speInFlight
  unfold execute_aarch64_instrs_float_compare_cond
  by_cases hh : Janus.Arm64.conditionHolds cond.toNat js.flags = true
  · simp only [hh, ite_true, hfmt, hsz] at hj
    unfold Janus.Arm64.fpCommit at hj
    generalize ho : Janus.Arm64.FP.fpCompare (fmtN N) js.fpcr.toNat signal (js.getV rn N) (js.getV rm N) = o at hj
    by_cases ht : o.2.proc &&& Janus.Arm64.FP.trapEnables js.fpcr.toNat ≠ 0
    · simp [ht] at hj
    · simp only [ht, ite_false, Except.ok.injEq] at hj
      subst hj
      have ht' : o.2.proc &&& Janus.Arm64.FP.trapEnables js.fpcr.toNat = 0 := by simpa using ht
      have hcmp := run_FPCompareN hN hc (BitVec.ofNat N (js.getV rn N)) (BitVec.ofNat N (js.getV rm N)) signal
        (js.fpcr.setWidth 64) hf.fpsr
        (fun hb => by
          rw [getLsbD_setWidth64]
          exact trap_bit ht' (.inl rfl) (by rwa [getV_ofNat, getV_ofNat, hfn_fpcr, ho] at hb))
        (fun hb => by
          rw [getLsbD_setWidth64]
          exact trap_bit ht' (.inr rfl) (by rwa [getV_ofNat, getV_ofNat, hfn_fpcr, ho] at hb))
      rw [getV_ofNat, getV_ofNat, hfn_fpcr, ho] at hcmp
      have hrd : o.2.direct = 0 := ho ▸ fpCompare_direct _ _ _ _ _
      have hrp : o.2.proc < 256 := ho ▸ fpCompare_proc_lt _ _ _ _ _
      obtain ⟨q1, q2, q3, q4⟩ := fp_flags_post h hf hfc hp o.1 o.2.proc (by omega)
      refine ⟨_, ?_, ?_, ?_, q3, q4⟩
      · cfg_simp [hchk, hv1, hv2, hcond, hh, run_FPCR_read hf, hcmp, fun v => run_readReg (hpv v), nzcv_bit3, nzcv_bit2,
          nzcv_bit1, nzcv_bit0, fun t (q : ProcState) => run_readReg (get?_set_self t .PSTATE q), set_set_PSTATE, psNZCV, fun v q => run_readReg (hspe v q)]
      · rw [hrd]; simpa using q1
      · rw [hrd]; simpa using q2
  · have hh' : Janus.Arm64.conditionHolds cond.toNat js.flags = false := by simpa using hh
    simp only [hh', Bool.false_eq_true, ite_false] at hj
    cases hj
    obtain ⟨q1, q2, q3, q4⟩ := fp_flags_post h hf hfc hp k 0 (by decide)
    have e1 : (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 0) = js.fpsr.setWidth 64 := by simp
    rw [e1, set_fpsr_self hf] at q1 q2 q3 q4
    have e2 : js.fpsr ||| BitVec.ofNat 32 0 = js.fpsr := by simp
    rw [e2] at q1 q2
    refine ⟨_, ?_, q1, q2, q3, q4⟩
    cfg_simp [hchk, hv1, hv2, hcond, hh', nzcv_bit3, nzcv_bit2, nzcv_bit1, nzcv_bit0,
      fun q => run_readReg (hspe1 q), fun t (q : ProcState) => run_readReg (get?_set_self t .PSTATE q), set_set_PSTATE, psNZCV,
      run_readReg hp]

end JanusASL.Proofs
