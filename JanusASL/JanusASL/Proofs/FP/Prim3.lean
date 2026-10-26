import JanusASL.Proofs.FP.Arith

/-! # Three-operand NaN and denormal processing, and `FPMulAdd` -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem processNaNs3_snan (f : Janus.Float.Fmt) (fpcr : Nat) (t1 t2 t3 : Janus.Arm64.FP.FPType) (a b c : Nat)
    (hs : t1 = .snan ∨ t2 = .snan ∨ t3 = .snan) :
    ∃ r, Janus.Arm64.FP.processNaNs3 f fpcr t1 t2 t3 a b c = some (r, Janus.Arm64.FP.raise Janus.Arm64.FP.IOC) := by
  by_cases hah : Janus.Arm64.FP.ah fpcr = true <;> cases t1 <;> cases t2 <;> cases t3 <;> simp at hs <;>
    simp [Janus.Arm64.FP.processNaNs3, Janus.Arm64.FP.processNaN, Janus.Arm64.FP.FPType.isNaN, hah]

theorem processNaNs3_direct {f : Janus.Float.Fmt} {fpcr : Nat} {t1 t2 t3 : Janus.Arm64.FP.FPType} {a b c r : Nat}
    {e : Janus.Arm64.FP.Exc} (h : Janus.Arm64.FP.processNaNs3 f fpcr t1 t2 t3 a b c = some (r, e)) : e.direct = 0 := by
  by_cases hah : Janus.Arm64.FP.ah fpcr = true <;> cases t1 <;> cases t2 <;> cases t3 <;>
    simp [Janus.Arm64.FP.processNaNs3, Janus.Arm64.FP.processNaN, Janus.Arm64.FP.FPType.isNaN, hah] at h <;>
    (rw [← h.2] <;> simp [Janus.Arm64.FP.raise])

theorem processNaNs3_none {f : Janus.Float.Fmt} {fpcr : Nat} {t1 t2 t3 : Janus.Arm64.FP.FPType} {a b c : Nat}
    (h : Janus.Arm64.FP.processNaNs3 f fpcr t1 t2 t3 a b c = none) :
    t1 ≠ .snan ∧ t1 ≠ .qnan ∧ t2 ≠ .snan ∧ t2 ≠ .qnan ∧ t3 ≠ .snan ∧ t3 ≠ .qnan := by
  by_cases hah : Janus.Arm64.FP.ah fpcr = true <;> cases t1 <;> cases t2 <;> cases t3 <;>
    simp [Janus.Arm64.FP.processNaNs3, Janus.Arm64.FP.FPType.isNaN, hah] at h ⊢

theorem nan3_ioc {N : Nat} {fpcr : BitVec 64} {t1 t2 t3 : Janus.Arm64.FP.FPType} {op1 op2 op3 : BitVec N}
    (hen : ∀ r e, Janus.Arm64.FP.processNaNs3 (fmtN N) fpcr.toNat t1 t2 t3 op1.toNat op2.toNat op3.toNat = some (r, e) →
      NT fpcr.toNat e) (hs : t1 = .snan ∨ t2 = .snan ∨ t3 = .snan) : fpcr.getLsbD 8 = false := by
  obtain ⟨r, hr⟩ := processNaNs3_snan (fmtN N) fpcr.toNat t1 t2 t3 op1.toNat op2.toNat op3.toNat hs
  exact getLsbD_of_testBit (nt_raise_ioc (hen _ _ hr))

theorem run_FPProcessNaNs3 {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s)
    (t1 t2 t3 : Janus.Arm64.FP.FPType) (op1 op2 op3 : BitVec N) (fpcr v : BitVec 64)
    (hen : ∀ r e, Janus.Arm64.FP.processNaNs3 (fmtN N) fpcr.toNat t1 t2 t3 op1.toNat op2.toNat op3.toNat = some (r, e) →
      NT fpcr.toNat e) :
    (FPProcessNaNs3__1 (aslFPType t1) (aslFPType t2) (aslFPType t3) op1 op2 op3 fpcr true).run (s.set .FPSR v) =
      match Janus.Arm64.FP.processNaNs3 (fmtN N) fpcr.toNat t1 t2 t3 op1.toNat op2.toNat op3.toNat with
      | some (r, e) => .ok (true, BitVec.ofNat N r) (s.set .FPSR (v ||| BitVec.ofNat 64 e.proc))
      | none => .ok (false, 0#N) (s.set .FPSR v) := by
  have ha : (N == 16 || (N == 32 || N == 64)) = true := by rcases hN with rfl | rfl <;> decide
  have h8 := fun hs => nan3_ioc hen hs
  have hz : (Zeros : BitVec N) = 0#N := rfl
  unfold FPProcessNaNs3__1
  cfg_simp [HaveAltFP, run_IsFeatureImplemented (hc.set_FPSR v), run_UsingAArch32 (hc.set_FPSR v), get_AH,
    Sail.BitVec.length, ofBool_eq_one, ha, run_sail_assert_true, undefined_FPType, run_undefined_bool,
    run_internal_pick]
  have Lq1 := run_FPProcessNaN_q hN hc op1 fpcr v
  have Lq2 := run_FPProcessNaN_q hN hc op2 fpcr v
  have Lq3 := run_FPProcessNaN_q hN hc op3 fpcr v
  by_cases hb : fpcr.getLsbD 8 = false
  · have Ls1 := run_FPProcessNaN_s hN hc op1 fpcr v hb
    have Ls2 := run_FPProcessNaN_s hN hc op2 fpcr v hb
    have Ls3 := run_FPProcessNaN_s hN hc op3 fpcr v hb
    by_cases hah : fpcr.toNat / 2 % 2 = 1 <;> cases t1 <;> cases t2 <;> cases t3 <;>
    cfg_simp [aslFPType, Janus.Arm64.FP.processNaNs3, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah,
      Ls1, Ls2, Ls3, Lq1, Lq2, Lq3, hz]
  · have hns : ¬(t1 = .snan ∨ t2 = .snan ∨ t3 = .snan) := fun hs => hb (h8 hs)
    by_cases hah : fpcr.toNat / 2 % 2 = 1 <;> cases t1 <;> cases t2 <;> cases t3 <;> simp at hns <;>
    cfg_simp [aslFPType, Janus.Arm64.FP.processNaNs3, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah,
      Lq1, Lq2, Lq3, hz]


theorem processDenorms3_cases (fpcr : Nat) (t1 t2 t3 : Janus.Arm64.FP.FPType) :
    Janus.Arm64.FP.processDenorms3 fpcr t1 t2 t3 = Janus.Arm64.FP.raise Janus.Arm64.FP.IDC ∨
      Janus.Arm64.FP.processDenorms3 fpcr t1 t2 t3 = {} := by
  unfold Janus.Arm64.FP.processDenorms3; split <;> simp

theorem processDenorms3_direct (fpcr : Nat) (t1 t2 t3 : Janus.Arm64.FP.FPType) :
    (Janus.Arm64.FP.processDenorms3 fpcr t1 t2 t3).direct = 0 := by
  rcases processDenorms3_cases fpcr t1 t2 t3 with h | h <;> rw [h] <;> rfl

theorem nt_pd3 {fpcr : BitVec 64} {t1 t2 t3 : Janus.Arm64.FP.FPType}
    (h : NT fpcr.toNat (Janus.Arm64.FP.processDenorms3 fpcr.toNat t1 t2 t3)) :
    (Janus.Arm64.FP.processDenorms3 fpcr.toNat t1 t2 t3).proc ≠ 0 → fpcr.getLsbD 15 = false := by
  intro hne
  rcases processDenorms3_cases fpcr.toNat t1 t2 t3 with h1 | h1
  · rw [h1] at h; exact getLsbD_of_testBit (nt_idc h)
  · rw [h1] at hne; simp at hne

theorem run_FPProcessDenorms3 {s : SState} (hc : LinuxEL0Config s) (t1 t2 t3 : Janus.Arm64.FP.FPType) (N : Int)
    (hN : N ≠ 16) (fpcr v : BitVec 64)
    (hen : (Janus.Arm64.FP.processDenorms3 fpcr.toNat t1 t2 t3).proc ≠ 0 → fpcr.getLsbD 15 = false) :
    (FPProcessDenorms3 (aslFPType t1) (aslFPType t2) (aslFPType t3) N fpcr).run (s.set .FPSR v) =
      .ok () (s.set .FPSR (v ||| BitVec.ofNat 64 (Janus.Arm64.FP.processDenorms3 fpcr.toNat t1 t2 t3).proc)) := by
  unfold FPProcessDenorms3
  have hN' : (N != 16) = true := by simpa using hN
  by_cases hd : Janus.Arm64.FP.ah fpcr.toNat = true ∧ (t1 = .denormal ∨ t2 = .denormal ∨ t3 = .denormal)
  · have hpd : Janus.Arm64.FP.processDenorms3 fpcr.toNat t1 t2 t3 = Janus.Arm64.FP.raise Janus.Arm64.FP.IDC := by
      unfold Janus.Arm64.FP.processDenorms3
      rcases hd with ⟨h1, h2 | h2 | h2⟩ <;> simp [h1, h2]
    rw [hpd] at hen ⊢
    have h15 : fpcr.getLsbD 15 = false := hen (by simp [Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC])
    have hfpe : fpcr.getLsbD (fpExcBit .FPExc_InputDenorm + 8) = false := h15
    obtain ⟨hah, hden⟩ := hd
    have hah' : fpcr.toNat / 2 % 2 = 1 := by simpa [Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit] using hah
    rcases hden with rfl | rfl | rfl <;>
    cfg_simp [HaveAltFP, run_IsFeatureImplemented (hc.set_FPSR v), run_UsingAArch32 (hc.set_FPSR v), get_AH, hN',
      ofBool_eq_one, hah', run_PE_set hc _ fpcr hfpe, aslFPType, fpExcBit, Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC]
  · have hpd : Janus.Arm64.FP.processDenorms3 fpcr.toNat t1 t2 t3 = {} := by
      unfold Janus.Arm64.FP.processDenorms3
      by_cases h1 : Janus.Arm64.FP.ah fpcr.toNat = true
      · have : ¬ (t1 = .denormal ∨ t2 = .denormal ∨ t3 = .denormal) := fun h => hd ⟨h1, h⟩
        simp [h1] at this ⊢; simp [this]
      · simp [h1]
    rw [hpd]
    cfg_simp [HaveAltFP, run_IsFeatureImplemented (hc.set_FPSR v), run_UsingAArch32 (hc.set_FPSR v), get_AH, hN',
      ofBool_eq_one, asl_beq_den]
    have : ¬ (fpcr.toNat / 2 % 2 = 1 ∧ (t1 = .denormal ∨ t2 = .denormal ∨ t3 = .denormal)) := fun h =>
      hd ⟨by simpa [Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit] using h.1, h.2⟩
    simp only [or_assoc]
    simp [this]


set_option hygiene false in
macro "fp_or_close3" : tactic => `(tactic| (
  simp only [d0, d1, d2, de, raise_direct, raise_proc, exc_empty_direct, exc_empty_proc, processDenorms_direct, ofNat0,
    BitVec.or_zero, BitVec.zero_or, ofNat_or, fpExcBit, Janus.Arm64.FP.IOC, Nat.pow_zero, exc_append_proc,
    exc_append_direct] <;> ac_rfl))

set_option hygiene false in
macro "fp_or_close3n" : tactic => `(tactic| (
  simp only [d0, d1, d2, raise_direct, raise_proc, exc_empty_direct, exc_empty_proc, processDenorms_direct, ofNat0,
    BitVec.or_zero, BitVec.zero_or, ofNat_or, fpExcBit, Janus.Arm64.FP.IOC, Nat.pow_zero, exc_append_proc,
    exc_append_direct, processDenorms3_direct] <;> ac_rfl))

theorem asl_beq_qnan (t : Janus.Arm64.FP.FPType) :
    (aslFPType t == FPType.FPType_QNaN) = decide (t = .qnan) := by cases t <;> decide

theorem guard_iff (A1 A2 B1 B2 C1 C2 C3 D : Prop) :
    (((¬A1 ∨ ¬A2) ∧ (¬B1 ∨ ¬B2)) ∧ ((¬C1 ∨ ¬C2 ∧ ¬C3) ∨ D)) ↔
      ¬ ((A1 ∧ A2 ∨ B1 ∧ B2) ∨ (C1 ∧ (C2 ∨ C3)) ∧ ¬D) := by
  by_cases a1 : A1 <;> by_cases a2 : A2 <;> by_cases b1 : B1 <;> by_cases b2 : B2 <;> by_cases c1 : C1 <;>
    by_cases c2 : C2 <;> by_cases c3 : C3 <;> by_cases d : D <;> simp [*]

theorem run_FPMulAdd {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s)
    (a op1 op2 : BitVec N) (fpcr v : BitVec 64)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpMulAdd (fmtN N) fpcr.toNat a.toNat op1.toNat op2.toNat).2) :
    (FPMulAdd a op1 op2 fpcr).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpMulAdd (fmtN N) fpcr.toNat a.toNat op1.toNat op2.toNat
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have ha : (N == 16 || (N == 32 || N == 64)) = true := by rcases hN with rfl | rfl <;> decide
  obtain ⟨H0, H1, H2, H3⟩ := fpMulAdd_nt _ _ _ _ _ hnt
  have R0 := run_FPUnpackN hN hc a fpcr v (nt_unpack H0)
  have R1 := fun v' => run_FPUnpackN hN hc op1 fpcr v' (nt_unpack H1)
  have R2 := fun v' => run_FPUnpackN hN hc op2 fpcr v' (nt_unpack H2)
  have R3 := fun v' => run_FPProcessNaNs3 hN hc _ _ _ a op1 op2 fpcr v' H3
  unfold FPMulAdd FPMulAdd__1
  unfold Janus.Arm64.FP.fpMulAdd at hnt ⊢
  have RF : ∀ v' f, (IsFeatureImplemented f).run (s.set .FPSR v') = .ok (cfgFeat f) (s.set .FPSR v') :=
    fun v' f => run_IsFeatureImplemented (hc.set_FPSR v') f
  have RU := run_UsingAArch32_set hc
  generalize hU0 : Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true a.toNat = U0 at *
  generalize hU1 : Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op1.toNat = U1 at *
  generalize hU2 : Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op2.toNat = U2 at *
  have d0 := unpack_direct' (fmtN N) fpcr.toNat true a.toNat
  have d1 := unpack_direct' (fmtN N) fpcr.toNat true op1.toNat
  have d2 := unpack_direct' (fmtN N) fpcr.toNat true op2.toNat
  have sp0 := unpack_spec (fmtN N) fpcr.toNat true a.toNat
  have sp1 := unpack_spec (fmtN N) fpcr.toNat true op1.toNat
  have sp2 := unpack_spec (fmtN N) fpcr.toNat true op2.toNat
  have nz0 := unpack_nz (fmtN N) fpcr.toNat true a.toNat
  have nz1 := unpack_nz (fmtN N) fpcr.toNat true op1.toNat
  have nz2 := unpack_nz (fmtN N) fpcr.toNat true op2.toNat
  rw [hU0] at d0 sp0 nz0
  rw [hU1] at d1 sp1 nz1
  rw [hU2] at d2 sp2 nz2
  rcases U0 with ⟨⟨t0, s0, v0⟩, x0⟩
  rcases U1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases U2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at *
  have hNe : (N : Int) ≠ 16 := by rcases hN with rfl | rfl <;> decide
  rcases hp : Janus.Arm64.FP.processNaNs3 (fmtN N) fpcr.toNat t0 t1 t2 a.toNat op1.toNat op2.toNat with _ | ⟨r, e⟩
  · simp only [hp] at R3 hnt ⊢
    obtain ⟨hn0, hn0', hn1, hn1', hn2, hn2'⟩ := processNaNs3_none hp
    cfg_simp [undefined_FPType, undefined_real, run_internal_pick, Sail.BitVec.length, run_sail_assert_true, ha,
      run_undefined_bool, run_undefined_bitvector, run_FPRoundingMode, R0, R1, R2, R3, HaveAltFP,
      RF, RU, get_AH, ofBool_eq_one, asl_beq_inf, asl_beq_zero, asl_beq_qnan, hn0', xor_ofBool, ofBool_eq_zero, ofBool_eq_one', ofBool_eq_ofBool,
      eq_not_iff', bne_eq_xor']
    simp (config := { decide := true }) [bne_eq_xor', ofBool_eq_ofBool] at hnt
    have hG := guard_iff (t1 = .infinity) (t2 = .zero) (t1 = .zero) (t2 = .infinity) (t0 = .infinity)
      (t1 = .infinity) (t2 = .infinity) (s0 = (s1 ^^ s2))
    have hE := nt_right (nt_left hnt)
    have Rdn := fun v' => run_FPDefaultNaN hN (hc.set_FPSR v') fpcr
    by_cases c1 : (t1 = .infinity ∧ t2 = .zero ∨ t1 = .zero ∧ t2 = .infinity) ∨
        (t0 = .infinity ∧ (t1 = .infinity ∨ t2 = .infinity)) ∧ ¬ s0 = (s1 ^^ s2)
    · have hGn : ¬ (((¬t1 = .infinity ∨ ¬t2 = .zero) ∧ (¬t1 = .zero ∨ ¬t2 = .infinity)) ∧
          ((¬t0 = .infinity ∨ ¬t1 = .infinity ∧ ¬t2 = .infinity) ∨ s0 = (s1 ^^ s2))) := fun h => (hG.mp h) c1
      simp only [if_pos c1, if_neg hGn] at hnt hE ⊢
      have hbit : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false := getLsbD_of_testBit (nt_raise_ioc hE)
      have Rpe := fun v' => run_PE_set hc .FPExc_InvalidOp fpcr hbit v'
      cfg_simp [Rdn, Rpe]
      fp_or_close3n
    have nc1 := c1
    have hGp : ((¬t1 = .infinity ∨ ¬t2 = .zero) ∧ (¬t1 = .zero ∨ ¬t2 = .infinity)) ∧
          ((¬t0 = .infinity ∨ ¬t1 = .infinity ∧ ¬t2 = .infinity) ∨ s0 = (s1 ^^ s2)) := hG.mpr c1
    simp only [if_neg c1, if_pos hGp] at hnt hE ⊢
    have Rden := fun v' => run_FPProcessDenorms3 hc t0 t1 t2 (N : Int) hNe fpcr v' (nt_pd3 (nt_right hnt))
    by_cases c2 : t0 = .infinity ∧ s0 = false ∨ (t1 = .infinity ∨ t2 = .infinity) ∧ s1 = s2
    · simp only [if_pos c2] at hnt hE ⊢
      cfg_simp [FPInf_0 hN, Rden]
      fp_or_close3n
    simp only [if_neg c2] at hnt hE ⊢
    by_cases c3 : t0 = .infinity ∧ s0 = true ∨ (t1 = .infinity ∨ t2 = .infinity) ∧ ¬ s1 = s2
    · simp only [if_pos c3] at hnt hE ⊢
      cfg_simp [FPInf_1 hN, Rden]
      fp_or_close3n
    simp only [if_neg c3] at hnt hE ⊢
    by_cases c4 : (t0 = .zero ∧ (t1 = .zero ∨ t2 = .zero)) ∧ s0 = (s1 ^^ s2)
    · simp only [if_pos c4] at hnt hE ⊢
      cfg_simp [FPZero_ofBool hN, Rden]
      fp_or_close3n
    simp only [if_neg c4] at hnt hE ⊢
    have ht0 : t0 ≠ .infinity := fun h => by cases s0 <;> simp_all
    have ht12 : ¬ (t1 = .infinity ∨ t2 = .infinity) := fun h => by
      by_cases hs : s1 = s2 <;> simp_all
    have ht1 : t1 ≠ .infinity := fun h => ht12 (Or.inl h)
    have ht2 : t2 ≠ .infinity := fun h => ht12 (Or.inr h)
    obtain ⟨n0, e0, rfl⟩ := sp0.2.1 ht0
    obtain ⟨n1, e1, rfl⟩ := sp1.2.1 ht1
    obtain ⟨n2, e2, rfl⟩ := sp2.2.1 ht2
    simp only [Janus.Float.Val.n, Janus.Float.Val.e] at hE ⊢
    have hrmz : (aslRM (Janus.Arm64.FP.roundingMode fpcr.toNat) == FPRounding.FPRounding_NEGINF) =
        decide (Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi) := asl_beq_rmi _
    have hmz : mult_real ((n1 : Rat) * 2 ^ e1) ((n2 : Rat) * 2 ^ e2) =
        ((n1 * n2 : Int) : Rat) * 2 ^ (e1 + e2) := by
      simp only [mult_real, mul_zpow]
    have hrnd := roundingMode_ne_rna fpcr.toNat
    cases hx : Janus.Float.fmaExact n0 e0 n1 e1 n2 e2 with
    | none =>
      have hz := addExact_none hx
      simp only [hx] at hE ⊢
      have hq : eq_real (add_real (valRat (Janus.Float.Val.num n0 e0))
          (mult_real (valRat (Janus.Float.Val.num n1 e1)) (valRat (Janus.Float.Val.num n2 e2)))) 0 = true := by
        simp only [eq_real_zero_iff, add_real, valRat_num, hmz, decide_eq_true_eq]
        exact hz
      simp only [hq, ite_true, hrmz]
      have hFZ : FPZero (if Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi then 1#1 else 0#1) N =
          pure (BitVec.ofNat N (Janus.Float.zero (fmtN N) (decide (Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi)))) := by
        have := FPZero_pure hN (decide (Janus.Arm64.FP.roundingMode fpcr.toNat = .rmi))
        simpa using this
      cfg_simp [hFZ, Rden]
      fp_or_close3n
    | some p =>
      obtain ⟨neg, m, ex⟩ := p
      obtain ⟨hm, hs⟩ := addExact_some hx
      simp only [hx] at hE ⊢
      have hq : eq_real (sval neg m ex) 0 = false := by
        simp only [eq_real_zero_iff]
        simpa using sval_ne_zero neg m hm ex
      have hadd : add_real (valRat (Janus.Float.Val.num n0 e0))
          (mult_real (valRat (Janus.Float.Val.num n1 e1)) (valRat (Janus.Float.Val.num n2 e2))) = sval neg m ex := by
        simp only [add_real, valRat_num, hmz, hs]
      simp only [hq, hadd]
      have Rr := fun v' => run_FPRound hN hc hsm fpcr v' _ hrnd neg m hm ex hE
      cfg_simp [Rr, Rden]
      fp_or_close3n
  · simp only [hp] at R3 hnt ⊢
    cfg_simp [undefined_FPType, undefined_real, run_internal_pick, Sail.BitVec.length, run_sail_assert_true, ha,
      run_undefined_bool, run_undefined_bitvector, run_FPRoundingMode, R0, R1, R2, R3, HaveAltFP,
      RF, RU, get_AH, ofBool_eq_one, asl_beq_inf, asl_beq_zero, asl_beq_qnan]
    have de := processNaNs3_direct hp
    have Rdn := fun v' => run_FPDefaultNaN hN (hc.set_FPSR v') fpcr
    have hahb : Janus.Arm64.FP.ah fpcr.toNat = true ↔ fpcr.toNat / 2 % 2 = 1 := by
      simp [Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit]
    by_cases hA : fpcr.toNat / 2 % 2 = 0
    · have ha0 : Janus.Arm64.FP.ah fpcr.toNat = false := by
        cases h : Janus.Arm64.FP.ah fpcr.toNat
        · rfl
        · have := hahb.mp h; omega
      simp only [hA, ha0, ite_true, true_and]
      simp only [ha0, Bool.not_false, Bool.true_and] at hnt
      by_cases hqb : (decide (t0 = .qnan) && (decide (t1 = .infinity) && decide (t2 = .zero) ||
          decide (t1 = .zero) && decide (t2 = .infinity))) = true
      · have hq : t0 = .qnan ∧ (t1 = .infinity ∧ t2 = .zero ∨ t1 = .zero ∧ t2 = .infinity) := by simpa using hqb
        simp only [if_pos hqb] at hnt
        simp only [if_pos hq]
        have hbit : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false := getLsbD_of_testBit (nt_raise_ioc (nt_right hnt))
        have Rpe := fun v' => run_PE_set hc .FPExc_InvalidOp fpcr hbit v'
        cfg_simp [Rdn, Rpe]
        fp_or_close3
      · have hq : ¬ (t0 = .qnan ∧ (t1 = .infinity ∧ t2 = .zero ∨ t1 = .zero ∧ t2 = .infinity)) := by simpa using hqb
        simp only [if_neg hqb] at hnt
        simp only [if_neg hq]
        cfg_simp
        fp_or_close3
    · have ha1 : Janus.Arm64.FP.ah fpcr.toNat = true := hahb.mpr (by omega)
      simp only [hA, ha1, ite_false, Bool.not_true, Bool.false_and, Bool.true_eq_false, false_and, Bool.false_eq_true] at hnt ⊢
      cfg_simp
      fp_or_close3

end JanusASL.Proofs
