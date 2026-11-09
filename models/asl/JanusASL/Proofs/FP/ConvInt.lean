import JanusASL.Proofs.FP.ToFixed
import JanusASL.Proofs.FP.Conv
import JanusASL.Proofs.FP.Step

/-! # FCVTZS / FCVTZU (scalar, to W or X): the execute function -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- Writing a general register after an operation that ORed `e` into FPSR. -/
theorem gpr_post {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hfc : FPConfig s)
    {d : Nat} (hd : d < 32) {I : Nat} (hI : I = 32 ∨ I = 64) (r : BitVec I) (e : Nat) (he : e < 2 ^ 32) :
    ∃ s', (X_set (d : Int) I r).run (s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e)) = .ok () s' ∧
      Rel { js.writeZR d (r.setWidth 64) with fpsr := js.fpsr ||| BitVec.ofNat 32 e } s' ∧
      FPRel { js.writeZR d (r.setWidth 64) with fpsr := js.fpsr ||| BitVec.ofNat 32 e } s' ∧
      (∀ x, isGprReg x = false → x ≠ .FPSR → s'.regs.get? x = s.regs.get? x) ∧ SMZero s' := by
  obtain ⟨st, hst⟩ : ∃ st, st = s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 e) := ⟨_, rfl⟩
  rw [← hst]
  have hst' := hst
  have hRst : Rel js st := by rw [hst]; exact h.set_other .FPSR _ rfl (by decide) (by decide) (by decide)
  have hfpsr : FPRel { js with fpsr := js.fpsr ||| BitVec.ofNat 32 e } st := by
    obtain ⟨z, hz0, hzv⟩ := hf.z
    refine { z := ⟨z, ?_, hzv⟩, fpcr := ?_, fpcrRes0 := hf.fpcrRes0, fpsr := ?_ }
    · rw [hst, get?_set_ne _ _ (by decide)]; exact hz0
    · rw [hst, get?_set_ne _ _ (by decide)]; exact hf.fpcr
    · rw [hst, get?_set_FPSR]
      show _ = some ((js.fpsr ||| BitVec.ofNat 32 e).setWidth 64)
      rw [fpsr_or_cast js.fpsr e he]
  have hsm : SMZero st := by
    obtain ⟨p, hp, hs⟩ := hfc.sm
    exact ⟨p, by rw [hst, get?_set_ne _ _ (by decide)]; exact hp, hs⟩
  have hvr : ∀ q : Janus.Arm64.State, q.vregs = js.vregs → q.fpcr = js.fpcr → q.fpsr = js.fpsr ||| BitVec.ofNat 32 e →
      ∀ st' : SState, FPRel { js with fpsr := js.fpsr ||| BitVec.ofNat 32 e } st' → FPRel q st' :=
    fun q h1 h2 h3 st' hh => FPRel.of_same hh h1 h2 h3
  by_cases hd31 : d = 31
  · subst hd31
    refine ⟨st, run_X_set_zr st hI r, ?_, ?_, fun x _ hx => ?_, hsm⟩
    · exact Rel.of_same_fp hRst (by simp [Janus.Arm64.State.writeZR]) (by simp [Janus.Arm64.State.writeZR])
        (by simp [Janus.Arm64.State.writeZR]) (by simp [Janus.Arm64.State.writeZR])
    · exact hvr _ (by simp [Janus.Arm64.State.writeZR]) (by simp [Janus.Arm64.State.writeZR])
        (by simp [Janus.Arm64.State.writeZR]) st hfpsr
    · rw [hst, get?_set_ne _ _ (Ne.symm hx)]
  · have hd' : d < 31 := by omega
    refine ⟨setGpr st (r.setWidth 64) d, ?_, ?_, ?_, fun x hx1 hx2 => ?_, ?_⟩
    · have := run_X_set (s := st) hd' hI r
      simpa [Sail.BitVec.zeroExtend] using this
    · exact Rel.of_same_fp (hRst.writeZR hd' (r.setWidth 64)) (by simp [Janus.Arm64.State.writeZR, hd31]) (by simp [Janus.Arm64.State.writeZR, hd31]) (by simp [Janus.Arm64.State.writeZR, hd31]) (by simp [Janus.Arm64.State.writeZR, hd31])
    · refine hvr { js.writeZR d (r.setWidth 64) with fpsr := js.fpsr ||| BitVec.ofNat 32 e }
        (by simp [Janus.Arm64.State.writeZR, hd31]) (by simp [Janus.Arm64.State.writeZR, hd31]) (by simp [Janus.Arm64.State.writeZR, hd31]) _ ?_
      exact hfpsr.of_eq (fun x hx => get?_setGpr st _ hd' x (by revert hx; revert x; decide))
    · rw [get?_setGpr st _ hd' x hx1, hst, get?_set_ne _ _ (Ne.symm hx2)]
    · obtain ⟨p, hp, hs⟩ := hsm
      exact ⟨p, by rw [get?_setGpr st _ hd' _ (by decide)]; exact hp, hs⟩

theorem execFpCvtInt_ftoi (js : Janus.Arm64.State) (sf u : Bool) (ftype rn rd : Nat) :
    Janus.Arm64.execFpCvtInt js sf ftype 3 (if u then 1 else 0) rn rd =
      Janus.Arm64.fpCommit js
        (Janus.Arm64.FP.fpToFixed (Janus.Arm64.ftypeFmt ftype) js.fpcr.toNat u .rz (if sf then 64 else 32)
          (js.getV rn (Janus.Arm64.ftypeSize ftype))).2
        (js.writeZR rd (BitVec.ofNat 64
          (Janus.Arm64.FP.fpToFixed (Janus.Arm64.ftypeFmt ftype) js.fpcr.toNat u .rz (if sf then 64 else 32)
            (js.getV rn (Janus.Arm64.ftypeSize ftype))).1)) := by
  cases u <;> simp [Janus.Arm64.execFpCvtInt, Janus.Arm64.FP.decodeRounding]

theorem run_exec_fcvtz {N ftype : Nat} (hft : (ftype = 0 ∧ N = 32) ∨ (ftype = 1 ∧ N = 64)) (sf u : Bool)
    {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) {rn rd : Nat} (hn : rn < 32) (hd : rd < 32)
    (hj : Janus.Arm64.execFpCvtInt js sf ftype 3 (if u then 1 else 0) rn rd = .ok js1) :
    ∃ s', (execute_aarch64_instrs_float_convert_int rd N (if sf then 64 else 32) rn FPConvOp.FPConvOp_CVT_FtoI 0
        (aslRM .rz) u).run s = .ok () s' ∧
      Rel js1 s' ∧ FPRel js1 s' ∧ (∀ r, isGprReg r = false → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) ∧ SMZero s' := by
  obtain ⟨hfmt, hsz⟩ := ftype_fmt hft
  have hN : N = 32 ∨ N = 64 := by rcases hft with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have hM : (if sf then 64 else 32) = 32 ∨ (if sf then 64 else 32) = 64 := by cases sf <;> simp
  rw [execFpCvtInt_ftoi, hfmt, hsz] at hj
  obtain ⟨hnt, hj1⟩ := fpCommit_ok hj
  have hlt := fpToFixed_lt (fmtN N) js.fpcr.toNat u .rz (if sf then 64 else 32) (js.getV rn N)
  generalize hI : (if sf then 64 else 32 : Nat) = I at hM hj hj1 hnt hlt ⊢
  generalize hO : Janus.Arm64.FP.fpToFixed (fmtN N) js.fpcr.toNat u .rz I (js.getV rn N) = o at hj hj1 hnt hlt
  have hM0 : 0 < I := by omega
  have hov : o.1 < 2 ^ I := by
    rw [← hO]
    unfold Janus.Arm64.FP.fpToFixed
    dsimp only
    generalize Janus.Arm64.FP.unpack (fmtN N) js.fpcr.toNat (!Janus.Arm64.FP.ah js.fpcr.toNat) (js.getV rn N) = U
    rcases U with ⟨⟨t1, s1, v1⟩, x1⟩
    rcases v1 with ⟨n, ex⟩ | neg
    · simp only
      generalize (if n = 0 then (0, false) else Janus.Float.roundToInt .rz s1 n.natAbs ex) = r
      rcases r with ⟨i, inx⟩
      exact satQ_lt I hM0 u i
    · exact satQ_lt I hM0 u _
  have hfa := set_fpsr_self hf
  have hfcr := run_FPCR_read hf
  have hchk := run_CheckFPEnabled64 hc hfc
  have hmg := run_IsMerging hc hfc (js.fpcr.setWidth 64)
  rw [hfn_fpcr] at hmg
  have hv := run_V_read hf hn (w := N) (by omega)
  have hFP : ∀ v, (FPToFixed (BitVec.ofNat N (js.getV rn N)) 0 u (js.fpcr.setWidth 64) (aslRM .rz) I).run (s.set .FPSR v) =
      .ok (BitVec.ofNat I o.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (o.2.proc ||| o.2.direct))) := by
    intro v
    have := run_FPToFixed hN hM hc (BitVec.ofNat N (js.getV rn N)) u (js.fpcr.setWidth 64) v
      (by rw [getV_ofNat, hfn_fpcr, hO]; exact hnt)
    rw [getV_ofNat, hfn_fpcr, hO] at this
    exact this
  have hFP' := hFP (js.fpsr.setWidth 64)
  rw [hfa] at hFP'
  have he : o.2.proc ||| o.2.direct < 2 ^ 32 := by
    have := Nat.or_lt_two_pow (n := 8) hlt.1 hlt.2; omega
  obtain ⟨s', hxs, p1, p2, p3, p4⟩ := gpr_post h hf hfc hd hM (BitVec.ofNat I o.1) (o.2.proc ||| o.2.direct) he
  have hj1' : js1 = { js.writeZR rd ((BitVec.ofNat I o.1).setWidth 64) with fpsr := js.fpsr ||| BitVec.ofNat 32 (o.2.proc ||| o.2.direct) } := by
    rw [hj1]
    have : (BitVec.ofNat I o.1).setWidth 64 = BitVec.ofNat 64 o.1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hov]
    have hz : (js.writeZR rd (BitVec.ofNat 64 o.1)).fpsr = js.fpsr := by
      unfold Janus.Arm64.State.writeZR; split <;> rfl
    rw [this]
    simp only [hz]
  rw [hj1']
  refine ⟨s', ?_, p1, p2, p3, p4⟩
  unfold execute_aarch64_instrs_float_convert_int
  have hb : (FPConvOp.FPConvOp_CVT_FtoI == FPConvOp.FPConvOp_CVT_FtoI_JS) = false := by decide
  have hbb : (FPConvOp.FPConvOp_CVT_FtoI == FPConvOp.FPConvOp_CVT_ItoF) = false := by decide
  have hass : ((N == 16 || N == 32 || N == 64) && (I == 16 || I == 32 || I == 64)) = true := by
    rcases hN with rfl | rfl <;> rcases hM with rfl | rfl <;> decide
  have hass3 : ((N == 16 || N == 32 || N == 64) && (I == 16 || I == 32 || I == 64)) = true := hass
  have hass4 : ((N == 32 || N == 64) && (I == 16 || I == 32 || I == 64)) = true := by
    rcases hN with rfl | rfl <;> rcases hM with rfl | rfl <;> decide
  have hass5 : ((N == 16 || (N == 32 || (N == 64))) && (I == 16 || (I == 32 || (I == 64)))) = true := by
    rcases hN with rfl | rfl <;> rcases hM with rfl | rfl <;> decide
  cfg_simp [hb, hbb, hchk, hfcr, hmg, run_undefined_bitvector, hv, run_sail_assert_of hass, run_sail_assert_of hass4,
    run_sail_assert_of hass5, hFP']
  rw [ofNat_or] at hxs; exact hxs

end JanusASL.Proofs
