import JanusASL.Proofs.FP.Prim

/-! # `FPAdd`, `FPSub`, `FPMul`, ... against Janus' `Janus.Arm64.FP` (width-generic, `N = 32` or `64`) -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_FPAdd {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s)
    (op1 op2 : BitVec N) (fpcr v : BitVec 64)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpAdd (fmtN N) fpcr.toNat op1.toNat op2.toNat).2) :
    (FPAdd__1 op1 op2 fpcr true).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpAdd (fmtN N) fpcr.toNat op1.toNat op2.toNat
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have ha : (N == 16 || (N == 32 || N == 64)) = true := by rcases hN with rfl | rfl <;> decide
  obtain ⟨H1, H2, H3⟩ := fpAdd_nt _ _ _ _ hnt
  have R1 := run_FPUnpackN hN hc op1 fpcr v (nt_unpack H1)
  have R2 := fun v' => run_FPUnpackN hN hc op2 fpcr v' (nt_unpack H2)
  have R3 := fun v' => run_FPProcessNaNs hN hc _ _ op1 op2 fpcr v' H3
  unfold FPAdd__1
  cfg_simp [undefined_FPType, undefined_real, run_internal_pick, Sail.BitVec.length, run_sail_assert_true, ha,
    run_undefined_bool, run_undefined_bitvector, run_FPRoundingMode, R1, R2, R3]
  unfold Janus.Arm64.FP.fpAdd at hnt ⊢
  have d1 := unpack_direct' (fmtN N) fpcr.toNat true op1.toNat
  have d2 := unpack_direct' (fmtN N) fpcr.toNat true op2.toNat
  have sp1 := unpack_spec (fmtN N) fpcr.toNat true op1.toNat
  have sp2 := unpack_spec (fmtN N) fpcr.toNat true op2.toNat
  generalize Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op1.toNat = U1 at hnt d1 sp1 ⊢
  generalize Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op2.toNat = U2 at hnt d2 sp2 ⊢
  rcases U1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases U2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at hnt d1 d2 sp1 sp2 ⊢
  have hNe : (N : Int) ≠ 16 := by rcases hN with rfl | rfl <;> decide
  have hrm := roundingMode_ne_rna fpcr.toNat
  rcases hp : Janus.Arm64.FP.processNaNs (fmtN N) fpcr.toNat t1 t2 op1.toNat op2.toNat with _ | ⟨r, e⟩
  · simp only [hp] at hnt ⊢
    cfg_simp [asl_beq_inf, asl_beq_zero, ofBool_eq_zero, ofBool_eq_one', ofBool_eq_not', eq_not_iff', ofBool_eq_ofBool]
    have hpd := nt_right hnt
    have Rden := fun v' => run_FPProcessDenorms hc t1 t2 (N : Int) hNe fpcr v' (nt_pd hpd)
    have hE := nt_right (nt_left hnt)
    have Rdn := fun v' => run_FPDefaultNaN hN (hc.set_FPSR v') fpcr
    have hhd := hE
    by_cases b1 : (decide (t1 = .infinity) && decide (t2 = .infinity) && s1 != s2) = true
    · have c1 : (t1 = .infinity ∧ t2 = .infinity) ∧ ¬ s1 = s2 := by simpa using b1
      simp only [if_pos b1] at hE
      simp only [if_pos c1]
      have hbit : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false := getLsbD_of_testBit (nt_raise_ioc hE)
      have Rpe := fun v' => run_PE_set hc .FPExc_InvalidOp fpcr hbit v'
      cfg_simp [Rdn, Rpe, Rden]
      fp_or_close
    have nc1 : ¬ ((t1 = .infinity ∧ t2 = .infinity) ∧ ¬ s1 = s2) := by simpa using b1
    simp only [if_neg b1] at hE
    simp only [if_neg nc1]
    by_cases b2 : (decide (t1 = .infinity) && !s1 || decide (t2 = .infinity) && !s2) = true
    · have c2 : t1 = .infinity ∧ s1 = false ∨ t2 = .infinity ∧ s2 = false := by simpa using b2
      simp only [if_pos b2] at hE
      simp only [if_pos c2]
      cfg_simp [FPInf_0 hN, Rden]
      fp_or_close
    have nc2 : ¬ (t1 = .infinity ∧ s1 = false ∨ t2 = .infinity ∧ s2 = false) := by simpa using b2
    simp only [if_neg b2] at hE
    simp only [if_neg nc2]
    by_cases b3 : (decide (t1 = .infinity) && s1 || decide (t2 = .infinity) && s2) = true
    · have c3 : t1 = .infinity ∧ s1 = true ∨ t2 = .infinity ∧ s2 = true := by simpa using b3
      simp only [if_pos b3] at hE
      simp only [if_pos c3]
      cfg_simp [FPInf_1 hN, Rden]
      fp_or_close
    have nc3 : ¬ (t1 = .infinity ∧ s1 = true ∨ t2 = .infinity ∧ s2 = true) := by simpa using b3
    simp only [if_neg b3] at hE
    simp only [if_neg nc3]
    by_cases b4 : (decide (t1 = .zero) && decide (t2 = .zero) && s1 == s2) = true
    · have c4 : (t1 = .zero ∧ t2 = .zero) ∧ s1 = s2 := by simpa using b4
      simp only [if_pos b4] at hE
      simp only [if_pos c4]
      cfg_simp [FPZero_ofBool hN, Rden]
      fp_or_close
    have nc4 : ¬ ((t1 = .zero ∧ t2 = .zero) ∧ s1 = s2) := by simpa using b4
    simp only [if_neg b4] at hE
    simp only [if_neg nc4]
    have ht1 : t1 ≠ .infinity := fun h => by cases s1 <;> simp_all
    have ht2 : t2 ≠ .infinity := fun h => by cases s2 <;> simp_all
    obtain ⟨n1, e1, rfl⟩ := sp1.2.1 ht1
    obtain ⟨n2, e2, rfl⟩ := sp2.2.1 ht2
    simp only [Janus.Float.Val.n, Janus.Float.Val.e] at hE ⊢
    have hrmz : (aslRM (Janus.Arm64.FP.roundingMode fpcr.toNat) == FPRounding.FPRounding_NEGINF) =
        decide (Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi) := asl_beq_rmi _
    cases hx : Janus.Float.addExact n1 e1 n2 e2 with
    | none =>
      have hz := addExact_none hx
      simp only [hx] at hE ⊢
      have hq : eq_real (add_real (valRat (Janus.Float.Val.num n1 e1)) (valRat (Janus.Float.Val.num n2 e2))) 0 = true := by
        simp [eq_real_zero_iff, add_real, valRat_num, hz]
      simp only [hq, ite_true, hrmz]
      have hFZ : FPZero (if Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi then 1#1 else 0#1) N =
          pure (BitVec.ofNat N (Janus.Float.zero (fmtN N) (decide (Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi)))) := by
        have := FPZero_pure hN (decide (Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi))
        simpa using this
      cfg_simp [hFZ, Rden]
      fp_or_close
    | some p =>
      obtain ⟨neg, m, ex⟩ := p
      obtain ⟨hm, hs⟩ := addExact_some hx
      simp only [hx] at hE ⊢
      have hq : eq_real (sval neg m ex) 0 = false := by
        simp only [eq_real_zero_iff]
        simpa using sval_ne_zero neg m hm ex
      have hadd : add_real (valRat (Janus.Float.Val.num n1 e1)) (valRat (Janus.Float.Val.num n2 e2)) = sval neg m ex := by
        simp only [add_real, valRat_num, hs]
      simp only [hq, hadd]
      have Rr := fun v' => run_FPRound hN hc hsm fpcr v' _ hrm neg m hm ex hE
      cfg_simp [Rr, Rden]
      fp_or_close
  · simp only [hp] at hnt ⊢
    cfg_simp
    have de := processNaNs_direct hp
    simp only [d1, d2, de, ofNat_or, BitVec.or_zero, BitVec.or_assoc]

theorem run_FPSub {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s)
    (op1 op2 : BitVec N) (fpcr v : BitVec 64)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpSub (fmtN N) fpcr.toNat op1.toNat op2.toNat).2) :
    (FPSub__1 op1 op2 fpcr true).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpSub (fmtN N) fpcr.toNat op1.toNat op2.toNat
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have ha : (N == 16 || (N == 32 || N == 64)) = true := by rcases hN with rfl | rfl <;> decide
  obtain ⟨H1, H2, H3⟩ := fpSub_nt _ _ _ _ hnt
  have R1 := run_FPUnpackN hN hc op1 fpcr v (nt_unpack H1)
  have R2 := fun v' => run_FPUnpackN hN hc op2 fpcr v' (nt_unpack H2)
  have R3 := fun v' => run_FPProcessNaNs hN hc _ _ op1 op2 fpcr v' H3
  unfold FPSub__1
  cfg_simp [undefined_FPType, undefined_real, run_internal_pick, Sail.BitVec.length, run_sail_assert_true, ha,
    run_undefined_bool, run_undefined_bitvector, run_FPRoundingMode, R1, R2, R3]
  unfold Janus.Arm64.FP.fpSub at hnt ⊢
  have d1 := unpack_direct' (fmtN N) fpcr.toNat true op1.toNat
  have d2 := unpack_direct' (fmtN N) fpcr.toNat true op2.toNat
  have sp1 := unpack_spec (fmtN N) fpcr.toNat true op1.toNat
  have sp2 := unpack_spec (fmtN N) fpcr.toNat true op2.toNat
  generalize Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op1.toNat = U1 at hnt d1 sp1 ⊢
  generalize Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op2.toNat = U2 at hnt d2 sp2 ⊢
  rcases U1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases U2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at hnt d1 d2 sp1 sp2 ⊢
  have hNe : (N : Int) ≠ 16 := by rcases hN with rfl | rfl <;> decide
  have hrm := roundingMode_ne_rna fpcr.toNat
  rcases hp : Janus.Arm64.FP.processNaNs (fmtN N) fpcr.toNat t1 t2 op1.toNat op2.toNat with _ | ⟨r, e⟩
  · simp only [hp] at hnt ⊢
    cfg_simp [asl_beq_inf, asl_beq_zero, ofBool_eq_zero, ofBool_eq_one', ofBool_eq_not', eq_not_iff', ofBool_eq_ofBool]
    have hpd := nt_right hnt
    have Rden := fun v' => run_FPProcessDenorms hc t1 t2 (N : Int) hNe fpcr v' (nt_pd hpd)
    have hE := nt_right (nt_left hnt)
    have Rdn := fun v' => run_FPDefaultNaN hN (hc.set_FPSR v') fpcr
    have hhd := hE
    by_cases b1 : (decide (t1 = .infinity) && decide (t2 = .infinity) && s1 == s2) = true
    · have c1 : (t1 = .infinity ∧ t2 = .infinity) ∧ s1 = s2 := by simpa using b1
      simp only [if_pos b1] at hE
      simp only [if_pos c1]
      have hbit : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false := getLsbD_of_testBit (nt_raise_ioc hE)
      have Rpe := fun v' => run_PE_set hc .FPExc_InvalidOp fpcr hbit v'
      cfg_simp [Rdn, Rpe, Rden]
      fp_or_close
    have nc1 : ¬ ((t1 = .infinity ∧ t2 = .infinity) ∧ s1 = s2) := by simpa using b1
    simp only [if_neg b1] at hE
    simp only [if_neg nc1]
    by_cases b2 : (decide (t1 = .infinity) && !s1 || decide (t2 = .infinity) && s2) = true
    · have c2 : t1 = .infinity ∧ s1 = false ∨ t2 = .infinity ∧ s2 = true := by simpa using b2
      simp only [if_pos b2] at hE
      simp only [if_pos c2]
      cfg_simp [FPInf_0 hN, Rden]
      fp_or_close
    have nc2 : ¬ (t1 = .infinity ∧ s1 = false ∨ t2 = .infinity ∧ s2 = true) := by simpa using b2
    simp only [if_neg b2] at hE
    simp only [if_neg nc2]
    by_cases b3 : (decide (t1 = .infinity) && s1 || decide (t2 = .infinity) && !s2) = true
    · have c3 : t1 = .infinity ∧ s1 = true ∨ t2 = .infinity ∧ s2 = false := by simpa using b3
      simp only [if_pos b3] at hE
      simp only [if_pos c3]
      cfg_simp [FPInf_1 hN, Rden]
      fp_or_close
    have nc3 : ¬ (t1 = .infinity ∧ s1 = true ∨ t2 = .infinity ∧ s2 = false) := by simpa using b3
    simp only [if_neg b3] at hE
    simp only [if_neg nc3]
    by_cases b4 : (decide (t1 = .zero) && decide (t2 = .zero) && s1 == !s2) = true
    · have c4 : (t1 = .zero ∧ t2 = .zero) ∧ ¬ s1 = s2 := by simpa [eq_not_iff'] using b4
      simp only [if_pos b4] at hE
      simp only [if_pos c4]
      cfg_simp [FPZero_ofBool hN, Rden]
      fp_or_close
    have nc4 : ¬ ((t1 = .zero ∧ t2 = .zero) ∧ ¬ s1 = s2) := by simpa [eq_not_iff'] using b4
    simp only [if_neg b4] at hE
    simp only [if_neg nc4]
    have ht1 : t1 ≠ .infinity := fun h => by cases s1 <;> simp_all
    have ht2 : t2 ≠ .infinity := fun h => by cases s2 <;> simp_all
    obtain ⟨n1, e1, rfl⟩ := sp1.2.1 ht1
    obtain ⟨n2, e2, rfl⟩ := sp2.2.1 ht2
    simp only [Janus.Float.Val.n, Janus.Float.Val.e] at hE ⊢
    have hrmz : (aslRM (Janus.Arm64.FP.roundingMode fpcr.toNat) == FPRounding.FPRounding_NEGINF) =
        decide (Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi) := asl_beq_rmi _
    cases hx : Janus.Float.addExact n1 e1 (-n2) e2 with
    | none =>
      have hz := addExact_none hx
      simp only [hx] at hE ⊢
      have hq : eq_real (sub_real (valRat (Janus.Float.Val.num n1 e1)) (valRat (Janus.Float.Val.num n2 e2))) 0 = true := by
        have hz' : (n1 : Rat) * 2 ^ e1 + -((n2 : Rat) * 2 ^ e2) = 0 := by
          simpa [Rat.intCast_neg, Rat.neg_mul] using hz
        simp [eq_real_zero_iff, sub_real, valRat_num, Rat.sub_eq_add_neg, hz']
      simp only [hq, ite_true, hrmz]
      have hFZ : FPZero (if Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi then 1#1 else 0#1) N =
          pure (BitVec.ofNat N (Janus.Float.zero (fmtN N) (decide (Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi)))) := by
        have := FPZero_pure hN (decide (Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi))
        simpa using this
      cfg_simp [hFZ, Rden]
      fp_or_close
    | some p =>
      obtain ⟨neg, m, ex⟩ := p
      obtain ⟨hm, hs⟩ := addExact_some hx
      simp only [hx] at hE ⊢
      have hq : eq_real (sval neg m ex) 0 = false := by
        simp only [eq_real_zero_iff]
        simpa using sval_ne_zero neg m hm ex
      have hadd : sub_real (valRat (Janus.Float.Val.num n1 e1)) (valRat (Janus.Float.Val.num n2 e2)) = sval neg m ex := by
        simp only [sub_real, valRat_num, hs, Rat.sub_eq_add_neg, Rat.intCast_neg, Rat.neg_mul]
      simp only [hq, hadd]
      have Rr := fun v' => run_FPRound hN hc hsm fpcr v' _ hrm neg m hm ex hE
      cfg_simp [Rr, Rden]
      fp_or_close
  · simp only [hp] at hnt ⊢
    cfg_simp
    have de := processNaNs_direct hp
    simp only [d1, d2, de, ofNat_or, BitVec.or_zero, BitVec.or_assoc]


theorem run_FPMul {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s)
    (op1 op2 : BitVec N) (fpcr v : BitVec 64)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpMul (fmtN N) fpcr.toNat op1.toNat op2.toNat).2) :
    (FPMul op1 op2 fpcr).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpMul (fmtN N) fpcr.toNat op1.toNat op2.toNat
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have ha : (N == 16 || (N == 32 || N == 64)) = true := by rcases hN with rfl | rfl <;> decide
  obtain ⟨H1, H2, H3⟩ := fpMul_nt _ _ _ _ hnt
  have R1 : (FPUnpack op1 fpcr).run (s.set .FPSR v) = _ := run_FPUnpackN hN hc op1 fpcr v (nt_unpack H1)
  have R2 : ∀ v', (FPUnpack op2 fpcr).run (s.set .FPSR v') = _ :=
    fun v' => run_FPUnpackN hN hc op2 fpcr v' (nt_unpack H2)
  have R3 : ∀ v', (FPProcessNaNs (aslFPType (Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op1.toNat).fst.fst)
      (aslFPType (Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op2.toNat).fst.fst) op1 op2 fpcr).run
      (s.set .FPSR v') = _ := fun v' => run_FPProcessNaNs hN hc _ _ op1 op2 fpcr v' H3
  unfold FPMul
  cfg_simp [undefined_FPType, undefined_real, run_internal_pick, Sail.BitVec.length, run_sail_assert_true, ha,
    run_undefined_bool, run_undefined_bitvector, R1, R2, R3]
  unfold Janus.Arm64.FP.fpMul at hnt ⊢
  have d1 := unpack_direct' (fmtN N) fpcr.toNat true op1.toNat
  have d2 := unpack_direct' (fmtN N) fpcr.toNat true op2.toNat
  have sp1 := unpack_spec (fmtN N) fpcr.toNat true op1.toNat
  have sp2 := unpack_spec (fmtN N) fpcr.toNat true op2.toNat
  have nz1 := unpack_nz (fmtN N) fpcr.toNat true op1.toNat
  have nz2 := unpack_nz (fmtN N) fpcr.toNat true op2.toNat
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
    have hpd := nt_right hnt
    have Rden := fun v' => run_FPProcessDenorms hc t1 t2 (N : Int) hNe fpcr v' (nt_pd hpd)
    have hE := nt_right (nt_left hnt)
    have Rdn := fun v' => run_FPDefaultNaN hN (hc.set_FPSR v') fpcr
    by_cases b1 : ((decide (t1 = .infinity) && decide (t2 = .zero)) || (decide (t1 = .zero) && decide (t2 = .infinity))) = true
    · have c1 : (t1 = .infinity ∧ t2 = .zero) ∨ (t1 = .zero ∧ t2 = .infinity) := by simpa using b1
      simp only [if_pos b1] at hE
      simp only [if_pos c1]
      have hbit : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false := getLsbD_of_testBit (nt_raise_ioc hE)
      have Rpe := fun v' => run_PE_set hc .FPExc_InvalidOp fpcr hbit v'
      cfg_simp [Rdn, Rpe, Rden]
      fp_or_close
    have nc1 : ¬ ((t1 = .infinity ∧ t2 = .zero) ∨ (t1 = .zero ∧ t2 = .infinity)) := by simpa using b1
    simp only [if_neg b1] at hE
    simp only [if_neg nc1]
    by_cases b2 : (decide (t1 = .infinity) || decide (t2 = .infinity)) = true
    · have c2 : t1 = .infinity ∨ t2 = .infinity := by simpa using b2
      simp only [if_pos b2] at hE
      simp only [if_pos c2]
      cfg_simp [FPInf_ofBool hN, Rden]
      fp_or_close
    have nc2 : ¬ (t1 = .infinity ∨ t2 = .infinity) := by simpa using b2
    simp only [if_neg b2] at hE
    simp only [if_neg nc2]
    by_cases b3 : (decide (t1 = .zero) || decide (t2 = .zero)) = true
    · have c3 : t1 = .zero ∨ t2 = .zero := by simpa using b3
      simp only [if_pos b3] at hE
      simp only [if_pos c3]
      cfg_simp [FPZero_ofBool hN, Rden]
      fp_or_close
    have nc3 : ¬ (t1 = .zero ∨ t2 = .zero) := by simpa using b3
    simp only [if_neg b3] at hE
    simp only [if_neg nc3]
    have ht1 : t1 = .nonzero ∨ t1 = .denormal := by
      cases t1 <;> simp_all
    have ht2 : t2 = .nonzero ∨ t2 = .denormal := by
      cases t2 <;> simp_all
    obtain ⟨n1, e1, rfl, hn1'⟩ := nz1 ht1
    obtain ⟨n2, e2, rfl, hn2'⟩ := nz2 ht2
    simp only [Janus.Float.Val.n, Janus.Float.Val.e] at hE ⊢
    cases hx : Janus.Float.mulExact n1 e1 n2 e2 with
    | none =>
      exfalso
      unfold Janus.Float.mulExact at hx
      exact Int.mul_ne_zero hn1' hn2' (ofInt_none hx)
    | some p =>
      obtain ⟨neg, m, ex⟩ := p
      obtain ⟨hm, hs⟩ := mulExact_some hx
      simp only [hx] at hE ⊢
      have hmul : mult_real (valRat (Janus.Float.Val.num n1 e1)) (valRat (Janus.Float.Val.num n2 e2)) = sval neg m ex := by
        simp only [mult_real, valRat_num, hs]
      simp only [hmul]
      have Rr := fun v' => run_FPRoundDefault hN hc hsm fpcr v' neg m hm ex hE
      cfg_simp [Rr, Rden]
      fp_or_close
  · simp only [hp] at hnt ⊢
    cfg_simp
    have de := processNaNs_direct hp
    simp only [d1, d2, de, ofNat_or, BitVec.or_zero, BitVec.or_assoc]

end JanusASL.Proofs
