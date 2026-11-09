import JanusASL.Proofs.FP.FPRoundSide
import JanusASL.Proofs.FP.Arith

/-! # `FPDiv` against Janus' `fpDiv` -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option hygiene false in
macro "fp_or_closeD" : tactic => `(tactic| (
  simp only [d1, d2, raise_direct, raise_proc, exc_empty_direct, exc_empty_proc, processDenorms_direct, ofNat0,
    BitVec.or_zero, BitVec.zero_or, ofNat_or, fpExcBit, Janus.Arm64.FP.IOC, Janus.Arm64.FP.DZC, Nat.pow_zero, Nat.pow_one,
    hz2, bne_eq_xor', decide_true, Bool.not_true, Bool.not_false, ite_true, ite_false, decide_false, Bool.false_eq_true,
    exc_append_proc, exc_append_direct, decide_eq_true_eq] <;> ac_rfl))

theorem run_FPDiv {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s)
    (op1 op2 : BitVec N) (fpcr v : BitVec 64)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpDiv (fmtN N) fpcr.toNat op1.toNat op2.toNat).2) :
    (FPDiv op1 op2 fpcr).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpDiv (fmtN N) fpcr.toNat op1.toNat op2.toNat
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have ha : (N == 16 || (N == 32 || N == 64)) = true := by rcases hN with rfl | rfl <;> decide
  obtain ⟨H1, H2, H3⟩ := fpDiv_nt _ _ _ _ hnt
  have R1 : (FPUnpack op1 fpcr).run (s.set .FPSR v) = _ := run_FPUnpackN hN hc op1 fpcr v (nt_unpack H1)
  have R2 : ∀ v', (FPUnpack op2 fpcr).run (s.set .FPSR v') = _ :=
    fun v' => run_FPUnpackN hN hc op2 fpcr v' (nt_unpack H2)
  have R3 : ∀ v', (FPProcessNaNs (aslFPType (Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op1.toNat).fst.fst)
      (aslFPType (Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op2.toNat).fst.fst) op1 op2 fpcr).run
      (s.set .FPSR v') = _ := fun v' => run_FPProcessNaNs hN hc _ _ op1 op2 fpcr v' H3
  unfold FPDiv
  cfg_simp [undefined_FPType, undefined_real, run_internal_pick, Sail.BitVec.length, run_sail_assert_true, ha,
    run_undefined_bool, run_undefined_bitvector, R1, R2, R3]
  unfold Janus.Arm64.FP.fpDiv at hnt ⊢
  have d1 := unpack_direct' (fmtN N) fpcr.toNat true op1.toNat
  have d2 := unpack_direct' (fmtN N) fpcr.toNat true op2.toNat
  have sp1 := unpack_spec (fmtN N) fpcr.toNat true op1.toNat
  have sp2 := unpack_spec (fmtN N) fpcr.toNat true op2.toNat
  have nz1 := unpack_nzs (fmtN N) fpcr.toNat true op1.toNat
  have nz2 := unpack_nzs (fmtN N) fpcr.toNat true op2.toNat
  generalize Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op1.toNat = U1 at hnt d1 sp1 nz1 ⊢
  generalize Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op2.toNat = U2 at hnt d2 sp2 nz2 ⊢
  rcases U1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases U2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at hnt d1 d2 sp1 sp2 nz1 nz2 ⊢
  have hNe : (N : Int) ≠ 16 := by rcases hN with rfl | rfl <;> decide
  rcases hp : Janus.Arm64.FP.processNaNs (fmtN N) fpcr.toNat t1 t2 op1.toNat op2.toNat with _ | ⟨r, e⟩
  · simp only [hp] at hnt ⊢
    obtain ⟨hn1, hn2, hn3, hn4⟩ := processNaNs_none hp
    cfg_simp [asl_beq_inf, asl_beq_zero, ofBool_eq_zero, ofBool_eq_one', ofBool_eq_not', eq_not_iff',
      ofBool_eq_ofBool, xor_ofBool]
    have hpd := hnt
    have hE := nt_right (nt_left hnt)
    have Rdn := fun v' => run_FPDefaultNaN hN (hc.set_FPSR v') fpcr
    have Rden : ¬ t2 = .zero → ∀ v', (FPProcessDenorms (aslFPType t1) (aslFPType t2) (N : Int) fpcr).run (s.set .FPSR v') =
        .ok () (s.set .FPSR (v' ||| BitVec.ofNat 64 (Janus.Arm64.FP.processDenorms fpcr.toNat t1 t2).proc)) := fun hz v' =>
      run_FPProcessDenorms hc t1 t2 (N : Int) hNe fpcr v' (nt_pd (by
        have := nt_right hpd
        simpa [hz] using this))
    by_cases b1 : (decide (t1 = .infinity) && decide (t2 = .infinity) || decide (t1 = .zero) && decide (t2 = .zero)) = true
    · have c1 : (t1 = .infinity ∧ t2 = .infinity) ∨ (t1 = .zero ∧ t2 = .zero) := by simpa using b1
      simp only [if_pos b1] at hE
      simp only [if_pos c1]
      have hbit : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false := getLsbD_of_testBit (nt_raise_ioc hE)
      have Rpe := fun v' => run_PE_set hc .FPExc_InvalidOp fpcr hbit v'
      by_cases hz2 : t2 = .zero
      · cfg_simp [Rdn, Rpe, hz2]
        fp_or_closeD
      · cfg_simp [Rdn, Rpe, Rden hz2, hz2]
        fp_or_closeD
    have nc1 : ¬ ((t1 = .infinity ∧ t2 = .infinity) ∨ (t1 = .zero ∧ t2 = .zero)) := by simpa using b1
    simp only [if_neg b1] at hE
    simp only [if_neg nc1]
    by_cases b2 : (decide (t1 = .infinity) || decide (t2 = .zero)) = true
    · have c2 : t1 = .infinity ∨ t2 = .zero := by simpa using b2
      simp only [if_pos b2] at hE
      simp only [if_pos c2]
      by_cases hi : t1 = .infinity
      · subst hi
        by_cases hz2 : t2 = .zero
        · cfg_simp [FPInf_ofBool hN, hz2]
          fp_or_closeD
        · cfg_simp [FPInf_ofBool hN, Rden hz2, hz2]
          fp_or_closeD
      · have hbit : fpcr.getLsbD (fpExcBit .FPExc_DivideByZero + 8) = false := by
          have hE' : NT fpcr.toNat (Janus.Arm64.FP.raise Janus.Arm64.FP.DZC) := by simpa [hi] using hE
          exact getLsbD_of_testBit (nt_bit hE' (k := 1) (by decide) (by decide))
        have Rpe := fun v' => run_PE_set hc .FPExc_DivideByZero fpcr hbit v'
        by_cases hz2 : t2 = .zero
        · cfg_simp [FPInf_ofBool hN, Rpe, hi, hz2]
          fp_or_closeD
        · cfg_simp [FPInf_ofBool hN, Rpe, Rden hz2, hi, hz2]
          fp_or_closeD
    have nc2 : ¬ (t1 = .infinity ∨ t2 = .zero) := by simpa using b2
    simp only [if_neg b2] at hE
    simp only [if_neg nc2]
    by_cases b3 : (decide (t1 = .zero) || decide (t2 = .infinity)) = true
    · have c3 : t1 = .zero ∨ t2 = .infinity := by simpa using b3
      simp only [if_pos b3] at hE
      simp only [if_pos c3]
      have hz2 : ¬ t2 = .zero := fun h => nc2 (Or.inr h)
      cfg_simp [FPZero_ofBool hN, Rden hz2, hz2]
      fp_or_closeD
    have nc3 : ¬ (t1 = .zero ∨ t2 = .infinity) := by simpa using b3
    simp only [if_neg b3] at hE
    simp only [if_neg nc3]
    have hz2 : ¬ t2 = .zero := fun h => nc2 (Or.inr h)
    have ht1 : t1 = .nonzero ∨ t1 = .denormal := by
      cases t1 <;> simp_all
    have ht2 : t2 = .nonzero ∨ t2 = .denormal := by
      cases t2 <;> simp_all
    obtain ⟨n1, e1, rfl, hn1', hs1⟩ := nz1 ht1
    obtain ⟨n2, e2, rfl, hn2', hs2⟩ := nz2 ht2
    simp only [Janus.Float.Val.mag] at hE ⊢
    obtain ⟨hside, hbig⟩ := div_side (fmtN N).fbits n1.natAbs n2.natAbs e1 e2 (Int.natAbs_ne_zero.mpr hn1')
      (Int.natAbs_ne_zero.mpr hn2')
    have hdiv := div_sign n1 n2 hn1' hn2' e1 e2
    generalize hdo : Janus.Float.divOdd (fmtN N).fbits n1.natAbs e1 n2.natAbs e2 = dd at hside hbig hE ⊢
    have hMne : dd.1 ≠ 0 := by
      have := Nat.two_pow_pos ((fmtN N).fbits + 4); omega
    have hlog : ((fmtN N).fbits + 4 : Nat) ≤ Nat.log2 dd.1 := (Nat.le_log2 hMne).mpr hbig
    have hg : (dd.2 + 1) + ((fmtN N).fbits : Int) + 1 ≤ (Nat.log2 dd.1 : Int) + dd.2 := by omega
    subst hs1 hs2
    have Rr := fun v' => run_FPRoundDefault_side hN hc hsm fpcr v' (decide (n1 < 0) != decide (n2 < 0)) dd.1 hMne dd.2 _
      hside hg hE
    have hop : div_real (valRat (Janus.Float.Val.num n1 e1)) (valRat (Janus.Float.Val.num n2 e2)) =
        (if (decide (n1 < 0) != decide (n2 < 0)) = true then
          -((n1.natAbs : Rat) * 2 ^ e1 / ((n2.natAbs : Rat) * 2 ^ e2))
        else (n1.natAbs : Rat) * 2 ^ e1 / ((n2.natAbs : Rat) * 2 ^ e2)) := by
      simp only [valRat_num, div_real]; exact hdiv
    rw [hop]
    generalize hopq : (if (decide (n1 < 0) != decide (n2 < 0)) = true then
          -((n1.natAbs : Rat) * 2 ^ e1 / ((n2.natAbs : Rat) * 2 ^ e2))
        else (n1.natAbs : Rat) * 2 ^ e1 / ((n2.natAbs : Rat) * 2 ^ e2)) = op at Rr ⊢
    cfg_simp [Rr, Rden hz2, hz2]
    fp_or_closeD
  · simp only [hp] at hnt ⊢
    cfg_simp
    have de := processNaNs_direct hp
    simp only [d1, d2, de, ofNat_or, BitVec.or_zero, BitVec.or_assoc]


end JanusASL.Proofs
