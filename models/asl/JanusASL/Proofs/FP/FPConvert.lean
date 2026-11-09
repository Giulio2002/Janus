import JanusASL.Proofs.FP.ConvertNaN
import JanusASL.Proofs.FP.Sqrt
import JanusASL.Proofs.FP.Exec2

/-! # `FPConvert` (FCVT between single and double) against Janus' `fpConvert` -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_FPConvertNaN {N M : Nat} (hNM : (N = 32 ∧ M = 64) ∨ (N = 64 ∧ M = 32)) (op : BitVec N) (s : SState) :
    (FPConvertNaN op M).run s = .ok (BitVec.ofNat M (Janus.Arm64.FP.convertNaN (fmtN N) (fmtN M) op.toNat)) s := by
  rcases hNM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cnan_3264 op s
  · exact cnan_6432 op s

theorem fpConvert_lt (f g : Janus.Float.Fmt) (fpcr : Nat) (rm : Janus.Float.RM) (a : Nat) :
    ExcLt (Janus.Arm64.FP.fpConvert f g fpcr rm a).2 := by
  unfold Janus.Arm64.FP.fpConvert
  dsimp only
  exc_lt
  all_goals exact processDenorm_lt _ _

theorem fpConvert_nt (f g : Janus.Float.Fmt) (fpcr : Nat) (rm : Janus.Float.RM) (a : Nat)
    (h : NT fpcr (Janus.Arm64.FP.fpConvert f g fpcr rm a).2) : NT fpcr (Janus.Arm64.FP.unpack f fpcr true a).2 := by
  unfold Janus.Arm64.FP.fpConvert at h
  generalize Janus.Arm64.FP.unpack f fpcr true a = u1 at *
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  simp only at h ⊢
  exact nt_left h

set_option hygiene false in
macro "fp_or_closeC" : tactic => `(tactic| (
  simp only [d1, raise_direct, raise_proc, exc_empty_direct, exc_empty_proc, processDenorm_direct, ofNat0,
    BitVec.or_zero, BitVec.zero_or, ofNat_or, fpExcBit, Janus.Arm64.FP.IOC, Nat.pow_zero, Nat.pow_one,
    exc_append_proc, exc_append_direct, processNaN_direct'] <;> ac_rfl))

theorem run_FPConvert {N M : Nat} (hNM : (N = 32 ∧ M = 64) ∨ (N = 64 ∧ M = 32)) {s : SState} (hc : LinuxEL0Config s)
    (hsm : SMZero s) (op : BitVec N) (fpcr v : BitVec 64)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpConvert (fmtN N) (fmtN M) fpcr.toNat
      (Janus.Arm64.FP.roundingMode fpcr.toNat) op.toNat).2) :
    (FPConvert op fpcr (aslRM (Janus.Arm64.FP.roundingMode fpcr.toNat)) M).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpConvert (fmtN N) (fmtN M) fpcr.toNat (Janus.Arm64.FP.roundingMode fpcr.toNat) op.toNat
      .ok (BitVec.ofNat M r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have hN : N = 32 ∨ N = 64 := by omega
  have hM : M = 32 ∨ M = 64 := by omega
  have hM16 : (M == 16) = false := by rcases hM with rfl | rfl <;> rfl
  have hM' : (M == 16 || (M == 32 || M == 64)) = true := by rcases hM with rfl | rfl <;> decide
  have hM2 : (M == 32 || M == 64) = true := by rcases hM with rfl | rfl <;> decide
  have hN' : (Sail.BitVec.length op == 16 || (Sail.BitVec.length op == 32 || Sail.BitVec.length op == 64)) = true := by
    simp only [Sail.BitVec.length]; rcases hN with rfl | rfl <;> decide
  have H1 := fpConvert_nt _ _ _ _ _ hnt
  have R1 : (FPUnpackCV op fpcr).run (s.set .FPSR v) = _ := run_FPUnpackCVN hN hc op fpcr v (nt_unpack H1)
  unfold FPConvert
  cfg_simp [undefined_FPType, undefined_real, run_internal_pick, Sail.BitVec.length, run_sail_assert_true, hM', hN',
    run_undefined_bool, run_undefined_bitvector, R1, hM16, hM2]
  unfold Janus.Arm64.FP.fpConvert at hnt ⊢
  have d1 := unpack_direct' (fmtN N) fpcr.toNat true op.toNat
  have sp1 := unpack_spec (fmtN N) fpcr.toNat true op.toNat
  have nz1 := unpack_nzs (fmtN N) fpcr.toNat true op.toNat
  have lb := unpack_lb (fmtN N) fpcr.toNat true op.toNat
  generalize Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op.toNat = U1 at hnt d1 sp1 nz1 lb ⊢
  rcases U1 with ⟨⟨t1, s1, v1⟩, x1⟩
  simp only at hnt d1 sp1 nz1 ⊢
  have hNe : (N : Int) ≠ 16 := by rcases hN with rfl | rfl <;> decide
  have hE := nt_right hnt
  by_cases hn : t1.isNaN = true
  · have ht : t1 = .snan ∨ t1 = .qnan := by cases t1 <;> simp_all [Janus.Arm64.FP.FPType.isNaN]
    have hc1 : (aslFPType t1 == FPType.FPType_SNaN) = true ∨ (aslFPType t1 == FPType.FPType_QNaN) = true := by
      rcases ht with rfl | rfl <;> simp only [aslFPType] <;> decide
    simp only [if_pos hn] at hE ⊢
    rw [if_pos hc1]
    have Rdn := fun v' => run_FPDefaultNaN hM (hc.set_FPSR v') fpcr
    have Rcn := run_FPConvertNaN hNM op
    by_cases hdn : fpcr.toNat / 2 ^ 25 % 2 = 1
    · have hdn' : Janus.Arm64.FP.dn fpcr.toNat = true := by simp [Janus.Arm64.FP.dn, Janus.Arm64.FP.fpcrBit, hdn]
      rcases ht with rfl | rfl
      · have hbit : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false :=
          getLsbD_of_testBit (nt_raise_ioc (by simpa using hE))
        have Rpe := run_PE_set (s := s) hc .FPExc_InvalidOp fpcr hbit
        cfg_simp [get_DN, ofBool_eq_one, hdn, hdn', Rdn, Rpe, aslFPType]
        fp_or_closeC
      · cfg_simp [get_DN, ofBool_eq_one, hdn, hdn', Rdn, aslFPType]
        fp_or_closeC
    · have hdn' : Janus.Arm64.FP.dn fpcr.toNat = false := by simp [Janus.Arm64.FP.dn, Janus.Arm64.FP.fpcrBit, hdn]
      rcases ht with rfl | rfl
      · have hbit : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false :=
          getLsbD_of_testBit (nt_raise_ioc (by simpa using hE))
        have Rpe := run_PE_set (s := s) hc .FPExc_InvalidOp fpcr hbit
        cfg_simp [get_DN, ofBool_eq_one, hdn, hdn', Rcn, Rpe, aslFPType]
        fp_or_closeC
      · cfg_simp [get_DN, ofBool_eq_one, hdn, hdn', Rcn, aslFPType]
        fp_or_closeC
  simp only [if_neg hn] at hE ⊢
  have hc1 : ¬ ((aslFPType t1 == FPType.FPType_SNaN) = true ∨ (aslFPType t1 == FPType.FPType_QNaN) = true) := by
    intro h; apply hn; cases t1 <;> first | rfl | (simp only [aslFPType] at h; revert h; decide)
  rw [if_neg hc1]
  by_cases hi : t1 = .infinity
  · simp only [if_pos hi] at hE ⊢
    have hc2 : (aslFPType t1 == FPType.FPType_Infinity) = true := by subst hi; decide
    rw [if_pos hc2, FPInf_ofBool hM]
    simp only [exc_append_proc, exc_append_direct, d1, exc_empty_proc, exc_empty_direct, BitVec.or_zero, ofNat_or,
      ofNat0, BitVec.zero_or]
    rfl
  simp only [if_neg hi] at hE ⊢
  have hc2 : ¬ (aslFPType t1 == FPType.FPType_Infinity) = true := by
    intro h; apply hi; cases t1 <;> first | rfl | (simp only [aslFPType] at h; revert h; decide)
  rw [if_neg hc2]
  by_cases hz : t1 = .zero
  · simp only [if_pos hz] at hE ⊢
    have hc3 : (aslFPType t1 == FPType.FPType_Zero) = true := by subst hz; decide
    rw [if_pos hc3, FPZero_ofBool hM]
    simp only [exc_append_proc, exc_append_direct, d1, exc_empty_proc, exc_empty_direct, BitVec.or_zero, ofNat_or,
      ofNat0, BitVec.zero_or]
    rfl
  simp only [if_neg hz] at hE ⊢
  have hc3 : ¬ (aslFPType t1 == FPType.FPType_Zero) = true := by
    intro h; apply hz; cases t1 <;> first | rfl | (simp only [aslFPType] at h; revert h; decide)
  rw [if_neg hc3]
  have ht : t1 = .nonzero ∨ t1 = .denormal := by
    cases t1 <;> simp_all [Janus.Arm64.FP.FPType.isNaN]
  obtain ⟨n, e', hv, hn0, hsn⟩ := nz1 ht
  have hlb := lb n e' hv hn0
  subst hv
  simp only [Janus.Float.Val.mag] at hE ⊢
  have hs0 : s1 = decide (n < 0) := hsn
  subst hs0
  have hq : valRat (Janus.Float.Val.num n e') = if decide (n < 0) = true then -((n.natAbs : Rat) * 2 ^ e') else (n.natAbs : Rat) * 2 ^ e' := by
    rw [valRat_num]
    by_cases hn : n < 0
    · have h1 : (n : Rat) = -((n.natAbs : Nat) : Rat) := by
        have h2 : ((n.natAbs : Nat) : Int) = Neg.neg n := by omega
        have := congrArg (fun z : Int => (z : Rat)) h2
        simp only [Rat.intCast_natCast, Rat.intCast_neg] at this
        rw [this, Rat.neg_neg]
      simp only [hn, decide_true, ite_true]
      rw [h1, Rat.neg_mul]
    · have h1 : (n : Rat) = ((n.natAbs : Nat) : Rat) := by
        have h2 : ((n.natAbs : Nat) : Int) = n := by omega
        have := congrArg (fun z : Int => (z : Rat)) h2
        simp only [Rat.intCast_natCast] at this
        exact this.symm
      simp only [hn, decide_false, ite_false, Bool.false_eq_true]
      rw [h1]
  rw [hq]
  have hMne : n.natAbs ≠ 0 := by omega
  have hS : Side (((Nat.log2 n.natAbs : Nat) : Int) + e' - ((fmtN M).fbits : Int) - 1) ((n.natAbs : Rat) * 2 ^ e')
      ((n.natAbs : Rat) * 2 ^ e') := Side.refl _ _
  have Rr := fun v' => run_FPRoundCV_side hM hc hsm fpcr v' (Janus.Arm64.FP.roundingMode fpcr.toNat)
    (roundingMode_ne_rna _) (decide (n < 0)) n.natAbs hMne e' _ hS (by omega) (nt_left hE)
  have Rden := fun v' => run_FPProcessDenorm hc t1 (N : Int) hNe fpcr v' (nt_pd1 (nt_right hE))
  simp only [decide_eq_true_eq] at Rr
  cfg_simp [Rr, Rden]
  fp_or_closeC


end JanusASL.Proofs
