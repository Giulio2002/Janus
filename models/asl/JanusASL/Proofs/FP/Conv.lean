import JanusASL.Proofs.FP.Sqrt
import JanusASL.Proofs.FP.Exec2

/-! # Integer to floating-point conversion: `FixedToFP` against Janus' `fixedToFP`; the execute function (SCVTF/UCVTF) -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem fixedToFP_lt (f : Janus.Float.Fmt) (fpcr : Nat) (u : Bool) (rm : Janus.Float.RM) (M x : Nat) :
    ExcLt (Janus.Arm64.FP.fixedToFP f fpcr u rm M x).2 := by
  unfold Janus.Arm64.FP.fixedToFP
  dsimp only
  generalize (if u || x < 2 ^ (M - 1) then (x : Int) else (x : Int) - 2 ^ M) = i
  split
  · exact ExcLt.empty
  · exact fpRound_lt _ _ _ _ _ _

theorem toInt_cond {M : Nat} (x : BitVec M) (hM : 0 < M) :
    x.toInt = if x.toNat < 2 ^ (M - 1) then (x.toNat : Int) else (x.toNat : Int) - 2 ^ M := by
  rw [BitVec.toInt_eq_toNat_cond]
  have : 2 ^ M = 2 * 2 ^ (M - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  by_cases h : x.toNat < 2 ^ (M - 1)
  · have : 2 * x.toNat < 2 ^ M := by omega
    simp [this, h]
  · have : ¬ 2 * x.toNat < 2 ^ M := by omega
    simp [this, h]

theorem run_FixedToFP {N M : Nat} (hN : N = 32 ∨ N = 64) (hM : M = 32 ∨ M = 64) {s : SState} (hc : LinuxEL0Config s)
    (hsm : SMZero s) (x : BitVec M) (u : Bool) (fpcr v : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fixedToFP (fmtN N) fpcr.toNat u rm M x.toNat).2) :
    (FixedToFP x 0 u fpcr (aslRM rm) N).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fixedToFP (fmtN N) fpcr.toNat u rm M x.toNat
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have hN' : (N == 16 || (N == 32 || N == 64)) = true := by rcases hN with rfl | rfl <;> decide
  have hM' : (Sail.BitVec.length x == 16 || (Sail.BitVec.length x == 32 || Sail.BitVec.length x == 64)) = true := by
    simp only [Sail.BitVec.length]; rcases hM with rfl | rfl <;> decide
  have hrne : (aslRM rm != FPRounding.FPRounding_ODD) = true := by cases rm <;> decide
  unfold FixedToFP
  have hM0 : 0 < M := by rcases hM with rfl | rfl <;> decide
  obtain ⟨i, hrun, hF⟩ : ∃ i : Int, (∀ st, (asl_Int x u).run st = .ok i st) ∧
      Janus.Arm64.FP.fixedToFP (fmtN N) fpcr.toNat u rm M x.toNat =
        (if i = 0 then (Janus.Float.zero (fmtN N) false, ({ } : Janus.Arm64.FP.Exc))
         else Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat rm (decide (i < 0)) i.natAbs 0) := by
    cases u
    · refine ⟨x.toInt, fun st => ?_, ?_⟩
      · simp only [asl_Int, Bool.false_eq_true, ite_false, run_bind, run_sail_assert_true, run_pure]
        simp [Sail.BitVec.length, hM0]
      · unfold Janus.Arm64.FP.fixedToFP
        simp only [Bool.false_or, Bool.false_eq_true, ite_false]
        rw [toInt_cond x hM0]
        by_cases h : x.toNat < 2 ^ (M - 1) <;> simp [h]
    · refine ⟨(x.toNat : Int), fun st => ?_, ?_⟩
      · simp [asl_Int, run_pure]
      · unfold Janus.Arm64.FP.fixedToFP
        simp
  have h1inv : (1 : Rat)⁻¹ = 1 := by
    have := Rat.mul_inv_cancel (1 : Rat) (by decide)
    rwa [Rat.one_mul] at this
  have hq : div_real (to_real i) (real_power 2 0) = (i : Rat) := by
    simp only [div_real, to_real, real_power]
    rw [Rat.zpow_zero, Rat.div_def, h1inv, Rat.mul_one]; rfl
  have hz : eq_real (div_real (to_real i) (real_power 2 0)) 0 = decide (i = 0) := by
    rw [hq]; simp only [eq_real]; by_cases h : i = 0 <;> simp [h]
  rw [hF] at hnt ⊢
  have h0 : ((0 : Int) ≥b 0) = true := by decide
  simp only [run_bind, run_sail_assert_true, run_undefined_bitvector, hN', hM', hrne, hrun, run_pure, hz, h0]
  by_cases hi : i = 0
  · simp only [hi, decide_true, ite_true]
    rw [show (0#1 : BitVec 1) = BitVec.ofBool false from rfl, FPZero_ofBool hN]
    simp only [exc_empty_proc, exc_empty_direct, Nat.or_zero, ofNat0, BitVec.or_zero]
    rfl
  · simp only [hi, decide_false, ite_false] at hnt ⊢
    have hq' : div_real (to_real i) (real_power 2 0) = (if decide (i < 0) then -((i.natAbs : Nat) : Rat) else (i.natAbs : Nat)) := by
      rw [hq]
      by_cases hn : i < 0
      · simp only [hn, decide_true, ite_true]
        have : (i : Rat) = -((i.natAbs : Nat) : Rat) := by
          have h1 : ((i.natAbs : Nat) : Int) = Neg.neg i := by omega
          have := congrArg (fun z : Int => (z : Rat)) h1
          simp only [Rat.intCast_natCast, Rat.intCast_neg] at this
          rw [this]; simp
        exact this
      · simp only [hn, decide_false, ite_false]
        have h1 : ((i.natAbs : Nat) : Int) = i := by omega
        have := congrArg (fun z : Int => (z : Rat)) h1
        simp only [Rat.intCast_natCast] at this
        exact this.symm
    rw [hq']
    have hMne : i.natAbs ≠ 0 := by omega
    have hS : Side (((Nat.log2 i.natAbs : Nat) : Int) - ((fmtN N).fbits : Int) - 1) ((i.natAbs : Nat) : Rat)
        (((i.natAbs : Nat) : Rat) * 2 ^ (0 : Int)) := by
      rw [Rat.zpow_zero, Rat.mul_one]; exact Side.refl _ _
    have Rr := run_FPRound_side hN hc hsm fpcr v rm hrm (decide (i < 0)) i.natAbs hMne 0 _ hS (by omega) hnt
    exact Rr


theorem elem_set_full {N : Nat} (base r : BitVec N) (s : SState) :
    (Elem_set base 0 N r).run s = .ok r s := by
  have hs : (decide ((0 : Int) ≥ 0) && decide (((0 : Int) + 1) * (N : Int) ≤ (Sail.BitVec.length base : Int))) = true := by
    simp [Sail.BitVec.length]
  unfold Elem_set
  simp only [run_bind, run_sail_assert_of hs, run_pure]
  have : Sail.BitVec.updateSubrange base ((((0 : Int) + 1) * (N : Int) - 1).toNat) (((0 : Int) * (N : Int)).toNat)
      (BitVec.setWidth ((((0 : Int) + 1) * (N : Int) - 1).toNat - ((0 : Int) * (N : Int)).toNat + 1) r) = r := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
    have e1 : ((((0 : Int) + 1) * (N : Int) - 1).toNat - ((0 : Int) * (N : Int)).toNat + 1) = N := by omega
    simp [hj, e1, show N - 1 + 1 = N by omega]
  rw [this]


theorem upd_lowW {w : Nat} (hw : w ≤ 128) (x : BitVec 2048) (v : BitVec w) :
    (Sail.BitVec.updateSubrange x 511 0 (Sail.BitVec.zeroExtend v 512)).toNat % 2 ^ 128 = v.toNat := by
  have h : (Sail.BitVec.updateSubrange x 511 0 (Sail.BitVec.zeroExtend v 512)).setWidth 128 = v.setWidth 128 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, Sail.BitVec.zeroExtend, BitVec.getLsbD_allOnes]
    have h1 : j < 2048 := by omega
    have h2 : j < 512 := by omega
    simp [hj, h1, h2]
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth] at this
  rw [this]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) hw))

theorem run_V_setW {w : Nat} (hw : w = 32 ∨ w = 64 ∨ w = 128) {s : SState} (hc : LinuxEL0Config s) (hfc : FPConfig s)
    (n : Nat) (hn : n < 32) (value : BitVec w) {z0 : Vector (BitVec 2048) 32} (hz : s.regs.get? ._Z = some z0) :
    ∃ z', (V_set (n : Int) w value).run s = .ok () (s.set ._Z z') ∧
      ∀ i < 32, (z'[i]!).toNat % 2 ^ 128 = if i = n then value.toNat else (z0[i]!).toNat % 2 ^ 128 := by
  obtain ⟨p, hp, hpe, hpn, hps⟩ := hc.pstate
  obtain ⟨p', hp', hsm⟩ := hfc.sm
  rw [hp] at hp'; cases hp'
  have hn31 : decide ((n : Int) ≤ 31) = true := by simp; omega
  have hw' : (w == 8 || (w == 16 || (w == 32 || (w == 64 || w == 128)))) = true := by
    rcases hw with rfl | rfl | rfl <;> rfl
  have hw128 : w ≤ 128 := by omega
  unfold V_set
  refine ⟨Sail.vectorUpdate z0 n (Sail.BitVec.updateSubrange (z0[(n : Int)]!) 511 0 (Sail.BitVec.zeroExtend value 512)), ?_, ?_⟩
  · cfg_simp [hn31, hw', run_CurrentVL_read hc hfc, run_readReg hp, hpe, run_IsSVEEnabled0 hc hfc, EL0, EL1, EL2, EL3,
      ConstrainUnpredictableBool, __UNKNOWN_boolean, run_undefined_bool, run_readReg hz]
  · intro i hi
    rw [vec_get_set z0 n i hn hi]
    by_cases h : i = n
    · subst h; simp only [if_true]; exact upd_lowW hw128 _ _
    · simp [h]


theorem execFpCvtInt_itof (js : Janus.Arm64.State) (sf u : Bool) (ftype rn rd : Nat) :
    Janus.Arm64.execFpCvtInt js sf ftype 0 (if u then 3 else 2) rn rd =
      Janus.Arm64.fpCommit js
        (Janus.Arm64.FP.fixedToFP (Janus.Arm64.ftypeFmt ftype) js.fpcr.toNat u (Janus.Arm64.FP.roundingMode js.fpcr.toNat)
          (if sf then 64 else 32) ((js.readZR rn).toNat % 2 ^ (if sf then 64 else 32))).2
        (js.setScalar rd (Janus.Arm64.ftypeSize ftype) (js.mergeBase rd)
          (Janus.Arm64.FP.fixedToFP (Janus.Arm64.ftypeFmt ftype) js.fpcr.toNat u (Janus.Arm64.FP.roundingMode js.fpcr.toNat)
            (if sf then 64 else 32) ((js.readZR rn).toNat % 2 ^ (if sf then 64 else 32))).1) := by
  cases u <;> simp [Janus.Arm64.execFpCvtInt]

theorem run_exec_cvtf {N ftype : Nat} (hft : (ftype = 0 ∧ N = 32) ∨ (ftype = 1 ∧ N = 64)) (sf u : Bool)
    {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s)
    (hfc : FPConfig s) {rn rd : Nat} (hn : rn < 32) (hd : rd < 32)
    (hj : Janus.Arm64.execFpCvtInt js sf ftype 0 (if u then 3 else 2) rn rd = .ok js1) :
    ∃ s', (execute_aarch64_instrs_float_convert_int rd N (if sf then 64 else 32) rn FPConvOp.FPConvOp_CVT_ItoF 0
        (aslRM (Janus.Arm64.FP.roundingMode js.fpcr.toNat)) u).run s = .ok () s' ∧
      Rel js1 s' ∧ FPRel js1 s' ∧ (∀ r, r ≠ ._Z → r ≠ .FPSR → s'.regs.get? r = s.regs.get? r) ∧ SMZero s' := by
  obtain ⟨hfmt, hsz⟩ := ftype_fmt hft
  have hN : N = 32 ∨ N = 64 := by rcases hft with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have hM : (if sf then 64 else 32) = 32 ∨ (if sf then 64 else 32) = 64 := by cases sf <;> simp
  rw [execFpCvtInt_itof, hfmt, hsz] at hj
  obtain ⟨hnt, hj1⟩ := fpCommit_ok hj
  have hlt := fixedToFP_lt (fmtN N) js.fpcr.toNat u (Janus.Arm64.FP.roundingMode js.fpcr.toNat) (if sf then 64 else 32)
    ((js.readZR rn).toNat % 2 ^ (if sf then 64 else 32))
  generalize hI : (if sf then 64 else 32 : Nat) = I at hM hj hj1 hnt hlt ⊢
  generalize hO : Janus.Arm64.FP.fixedToFP (fmtN N) js.fpcr.toNat u (Janus.Arm64.FP.roundingMode js.fpcr.toNat) I
    ((js.readZR rn).toNat % 2 ^ I) = o at hj hj1 hnt hlt
  have hxr := run_X_read_rel h hn hM
  have hxn : (js.getX I rn).toNat = (js.readZR rn).toNat % 2 ^ I := by
    simp [Janus.Arm64.State.getX, BitVec.toNat_setWidth]
  have hFP : ∀ v, (FixedToFP (js.getX I rn) 0 u (js.fpcr.setWidth 64) (aslRM (Janus.Arm64.FP.roundingMode js.fpcr.toNat)) N).run
      (s.set .FPSR v) = .ok (BitVec.ofNat N o.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (o.2.proc ||| o.2.direct))) := by
    intro v
    have := run_FixedToFP hN hM hc hfc.sm (js.getX I rn) u (js.fpcr.setWidth 64) v (Janus.Arm64.FP.roundingMode js.fpcr.toNat)
      (roundingMode_ne_rna _) (by rw [hfn_fpcr, hxn, hO]; exact fpcr_bit_of_nt hnt |> fun x => by rw [hfn_fpcr] at x; exact x)
    rw [hfn_fpcr, hxn, hO] at this
    exact this
  have hfa := set_fpsr_self hf
  have hfcr := run_FPCR_read hf
  have hchk := run_CheckFPEnabled64 hc hfc
  have hmg := run_IsMerging hc hfc (js.fpcr.setWidth 64)
  rw [hfn_fpcr] at hmg
  unfold execute_aarch64_instrs_float_convert_int
  have hb : (FPConvOp.FPConvOp_CVT_ItoF == FPConvOp.FPConvOp_CVT_FtoI_JS) = false := by decide
  have hbb : (FPConvOp.FPConvOp_CVT_ItoF == FPConvOp.FPConvOp_CVT_ItoF) = true := by decide
  have h0 : ((0 : Int) ≥b 0) = true := by decide
  have hass : ((N == 16 || N == 32 || N == 64) && (I == 16 || I == 32 || I == 64)) = true := by
    rcases hN with rfl | rfl <;> rcases hM with rfl | rfl <;> decide
  have hFP' := hFP (js.fpsr.setWidth 64)
  rw [hfa] at hFP'
  have hj1' : js1 = { js.setScalar rd N (js.mergeBase rd) o.1 with fpsr := js.fpsr ||| BitVec.ofNat 32 (o.2.proc ||| o.2.direct) } := by
    rw [hj1]; rfl
  generalize hmq : Janus.Arm64.FP.isMerging js.fpcr.toNat = mg at hmg
  cases mg
  case true =>
    have hm : Janus.Arm64.FP.isMerging js.fpcr.toNat = true := hmq
    have hts := run_scalarTail hN h hf hc hfc hd hd o hlt hj1'
      (do let x ← X_read (rn : Int) I; FixedToFP x 0 u (js.fpcr.setWidth 64) (aslRM (Janus.Arm64.FP.roundingMode js.fpcr.toNat)) N)
      (by simp only [run_bind, hxr, hFP'])
    obtain ⟨s', hs', p1, p2, p3, p4⟩ := hts
    refine ⟨s', ?_, p1, p2, p3, p4⟩
    have hv := run_V_read hf hd (w := 128) (by omega)
    simp only [scalarTail, EStateM.run_bind, hmg, hm, ite_true, hv, hxr, hFP', ofNat_or] at hs'
    cfg_simp [hb, hbb, hchk, hfcr, hmg, hm, run_undefined_bitvector, hxr, run_sail_assert_of hass, hv, hFP']
    refine Eq.trans ?_ hs'
    rfl
  case false =>
    have hm : ¬ Janus.Arm64.FP.isMerging js.fpcr.toNat = true := by rw [hmq]; decide
    have hmb : js.mergeBase rd = 0 := by unfold Janus.Arm64.State.mergeBase; simp [hm]
    obtain ⟨z0, hz, hzv⟩ := hf.z
    have hz1 : (s.set .FPSR (js.fpsr.setWidth 64 ||| BitVec.ofNat 64 (o.2.proc ||| o.2.direct))).regs.get? ._Z = some z0 := by
      rw [get?_set_ne _ _ (by decide)]; exact hz
    obtain ⟨z', hrun, hz'⟩ := run_V_setW (w := N) (by omega) (hc.set_FPSR _) (hfc.set_FPSR _) rd hd (BitVec.ofNat N o.1) hz1
    have he : o.2.proc ||| o.2.direct < 2 ^ 32 := by
      have := Nat.or_lt_two_pow (n := 8) hlt.1 hlt.2; omega
    have hr : (BitVec.ofNat N o.1).toNat = o.1 % 2 ^ N := by rw [BitVec.toNat_ofNat]
    have hlt2 : 0 / 2 ^ N * 2 ^ N + (BitVec.ofNat N o.1).toNat < 2 ^ 128 := by
      have := run_elem_vset_lt hN (BitVec.ofNat 128 0) (BitVec.ofNat N o.1)
      simpa using this
    have hj1'' : js1 = { js.setV rd 128 (0 / 2 ^ N * 2 ^ N + (BitVec.ofNat N o.1).toNat) with
        fpsr := js.fpsr ||| BitVec.ofNat 32 (o.2.proc ||| o.2.direct) } := by
      rw [hj1', hmb, hr]; rfl
    obtain ⟨p1, p2, p3, p4⟩ := scalar_post h hf hfc hd 0 (by decide) (BitVec.ofNat N o.1) (o.2.proc ||| o.2.direct) he hj1''
      hz (z' := z') (fun i hi => by rw [hz' i hi, hr]; simp) hlt2
    refine ⟨_, ?_, p1, p2, p3, p4⟩
    cfg_simp [hb, hbb, hchk, hfcr, hmg, hm, run_undefined_bitvector, hxr, run_sail_assert_of hass, hFP', elem_set_full, ofNat_or]
    simp only [ofNat_or] at hrun
    exact hrun

end JanusASL.Proofs
