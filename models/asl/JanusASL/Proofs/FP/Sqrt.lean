import JanusASL.Proofs.FP.SqrtSide
import JanusASL.Proofs.FP.FPRoundSide
import JanusASL.Proofs.FP.Prim3

/-! # `FPSqrt` against Janus' `fpSqrt` -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem processDenorm_cases (fpcr : Nat) (t : Janus.Arm64.FP.FPType) :
    Janus.Arm64.FP.processDenorm fpcr t = Janus.Arm64.FP.raise Janus.Arm64.FP.IDC ∨
      Janus.Arm64.FP.processDenorm fpcr t = {} := by
  unfold Janus.Arm64.FP.processDenorm; split <;> simp

theorem processDenorm_direct (fpcr : Nat) (t : Janus.Arm64.FP.FPType) :
    (Janus.Arm64.FP.processDenorm fpcr t).direct = 0 := by
  rcases processDenorm_cases fpcr t with h | h <;> rw [h] <;> rfl

theorem nt_pd1 {fpcr : BitVec 64} {t : Janus.Arm64.FP.FPType}
    (h : NT fpcr.toNat (Janus.Arm64.FP.processDenorm fpcr.toNat t)) :
    (Janus.Arm64.FP.processDenorm fpcr.toNat t).proc ≠ 0 → fpcr.getLsbD 15 = false := by
  intro hne
  rcases processDenorm_cases fpcr.toNat t with h1 | h1
  · rw [h1] at h; exact getLsbD_of_testBit (nt_idc h)
  · rw [h1] at hne; simp at hne

theorem run_FPProcessDenorm {s : SState} (hc : LinuxEL0Config s) (t : Janus.Arm64.FP.FPType) (N : Int)
    (hN : N ≠ 16) (fpcr v : BitVec 64)
    (hen : (Janus.Arm64.FP.processDenorm fpcr.toNat t).proc ≠ 0 → fpcr.getLsbD 15 = false) :
    (FPProcessDenorm (aslFPType t) N fpcr).run (s.set .FPSR v) =
      .ok () (s.set .FPSR (v ||| BitVec.ofNat 64 (Janus.Arm64.FP.processDenorm fpcr.toNat t).proc)) := by
  unfold FPProcessDenorm
  have hN' : (N != 16) = true := by simpa using hN
  by_cases hd : Janus.Arm64.FP.ah fpcr.toNat = true ∧ t = .denormal
  · have hpd : Janus.Arm64.FP.processDenorm fpcr.toNat t = Janus.Arm64.FP.raise Janus.Arm64.FP.IDC := by
      unfold Janus.Arm64.FP.processDenorm
      obtain ⟨h1, h2⟩ := hd; simp [h1, h2]
    rw [hpd] at hen ⊢
    have h15 : fpcr.getLsbD 15 = false := hen (by simp [Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC])
    have hfpe : fpcr.getLsbD (fpExcBit .FPExc_InputDenorm + 8) = false := h15
    obtain ⟨hah, hden⟩ := hd
    have hah' : fpcr.toNat / 2 % 2 = 1 := by simpa [Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit] using hah
    subst hden
    cfg_simp [HaveAltFP, run_IsFeatureImplemented (hc.set_FPSR v), run_UsingAArch32 (hc.set_FPSR v), get_AH, hN',
      ofBool_eq_one, hah', run_PE_set hc _ fpcr hfpe, aslFPType, fpExcBit, Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC]
  · have hpd : Janus.Arm64.FP.processDenorm fpcr.toNat t = {} := by
      unfold Janus.Arm64.FP.processDenorm
      by_cases h1 : Janus.Arm64.FP.ah fpcr.toNat = true
      · have : ¬ t = .denormal := fun h => hd ⟨h1, h⟩
        simp [h1, this]
      · simp [h1]
    rw [hpd]
    cfg_simp [HaveAltFP, run_IsFeatureImplemented (hc.set_FPSR v), run_UsingAArch32 (hc.set_FPSR v), get_AH, hN',
      ofBool_eq_one, asl_beq_den]
    have : ¬ (fpcr.toNat / 2 % 2 = 1 ∧ t = .denormal) := fun h =>
      hd ⟨by simpa [Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit] using h.1, h.2⟩
    simp [this]

theorem fpSqrt_nt (f : Janus.Float.Fmt) (fpcr a : Nat)
    (h : NT fpcr (Janus.Arm64.FP.fpSqrt f fpcr a).2) : NT fpcr (Janus.Arm64.FP.unpack f fpcr true a).2 := by
  unfold Janus.Arm64.FP.fpSqrt at h
  generalize Janus.Arm64.FP.unpack f fpcr true a = u1 at *
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  simp only at h ⊢
  exact nt_left h


theorem ulpExpOf_lb (f : Janus.Float.Fmt) (x : Nat) : f.emin - f.fbits ≤ Janus.Float.ulpExpOf f x := by
  unfold Janus.Float.ulpExpOf
  by_cases h : Janus.Float.expOf f x = 0
  · simp [h]
  · have : 1 ≤ Janus.Float.expOf f x := Nat.pos_of_ne_zero h
    simp only [h, ite_false]
    unfold Janus.Float.Fmt.emin
    omega

theorem ulpExpOf_lbN (N : Nat) (hN : N = 32 ∨ N = 64) (x : Nat) : -1074 ≤ Janus.Float.ulpExpOf (fmtN N) x := by
  have := ulpExpOf_lb (fmtN N) x
  rcases hN with rfl | rfl <;> exact Int.le_trans (by decide) this

theorem fbits_le (N : Nat) (hN : N = 32 ∨ N = 64) : (fmtN N).fbits ≤ 52 := by
  rcases hN with rfl | rfl <;> decide

theorem hbig_of (m : Nat) (hm : m ≠ 0) (ex : Int) (h : -2200 ≤ ex) :
    1 ≤ ((m : Rat) * 2 ^ ex) * 4 ^ 1100 := by
  have h4 : (4 : Rat) ^ 1100 = (2 : Rat) ^ (2200 : Int) := by
    rw [four_pow, show (2200 : Int) = ((1100 : Nat) : Int) + ((1100 : Nat) : Int) from rfl,
      Rat.zpow_add two_ne_zero_rat, Rat.zpow_natCast]
  rw [h4, Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
  have hk : (2 : Rat) ^ (ex + 2200) = (((2 ^ (ex + 2200).toNat : Nat)) : Rat) := by
    rw [Rat.natCast_pow, Rat.natCast_ofNat, ← Rat.zpow_natCast]; congr 1; omega
  rw [hk]
  have h1 : 1 ≤ m := Nat.pos_of_ne_zero hm
  have h2 : 1 ≤ 2 ^ (ex + 2200).toNat := Nat.one_le_two_pow
  have : 1 ≤ m * 2 ^ (ex + 2200).toNat := Nat.mul_le_mul h1 h2
  have h3 : ((1 : Nat) : Rat) ≤ ((m * 2 ^ (ex + 2200).toNat : Nat) : Rat) := by
    exact Rat.natCast_le_natCast.mpr this
  rw [Rat.natCast_mul] at h3
  exact h3


theorem processNaN_direct' (f : Janus.Float.Fmt) (fpcr : Nat) (t : Janus.Arm64.FP.FPType) (op : Nat) :
    (Janus.Arm64.FP.processNaN f fpcr t op).2.direct = 0 := by
  unfold Janus.Arm64.FP.processNaN
  dsimp only
  split <;> simp [Janus.Arm64.FP.raise]

theorem valueOf_lb (f : Janus.Float.Fmt) (x : Nat) (n e' : Int) (h : Janus.Float.valueOf f x = .num n e') (hn : n ≠ 0) :
    f.emin - f.fbits ≤ e' := by
  unfold Janus.Float.valueOf at h
  split at h <;> simp at h
  all_goals first | (obtain ⟨-, rfl⟩ := h; exact ulpExpOf_lb f x) | (obtain ⟨rfl, -⟩ := h; contradiction)

theorem unpack_lb (f : Janus.Float.Fmt) (fpcr : Nat) (e : Bool) (x : Nat) (n e' : Int)
    (h : (Janus.Arm64.FP.unpack f fpcr e x).1.2.2 = .num n e') (hn : n ≠ 0) : f.emin - f.fbits ≤ e' := by
  unfold Janus.Arm64.FP.unpack at h
  split at h
  all_goals (try dsimp only at h); all_goals (try split at h)
  all_goals ((try dsimp only at h); first | exact valueOf_lb f x n e' h hn | (cases h; exact absurd rfl hn) | cases h)

set_option hygiene false in
macro "fp_or_closeS" : tactic => `(tactic| (
  simp only [d1, raise_direct, raise_proc, exc_empty_direct, exc_empty_proc, processDenorm_direct, ofNat0,
    BitVec.or_zero, BitVec.zero_or, ofNat_or, fpExcBit, Janus.Arm64.FP.IOC, Nat.pow_zero, Nat.pow_one,
    exc_append_proc, exc_append_direct] <;> ac_rfl))

theorem run_FPSqrt {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s)
    (op : BitVec N) (fpcr v : BitVec 64)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpSqrt (fmtN N) fpcr.toNat op.toNat).2) :
    (FPSqrt op fpcr).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpSqrt (fmtN N) fpcr.toNat op.toNat
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have ha : (N == 16 || (N == 32 || N == 64)) = true := by rcases hN with rfl | rfl <;> decide
  have H1 := fpSqrt_nt _ _ _ hnt
  have R1 : (FPUnpack op fpcr).run (s.set .FPSR v) = _ := run_FPUnpackN hN hc op fpcr v (nt_unpack H1)
  unfold FPSqrt
  cfg_simp [undefined_FPType, undefined_real, run_internal_pick, Sail.BitVec.length, run_sail_assert_true, ha,
    run_undefined_bool, run_undefined_bitvector, R1]
  unfold Janus.Arm64.FP.fpSqrt at hnt ⊢
  have d1 := unpack_direct' (fmtN N) fpcr.toNat true op.toNat
  have sp1 := unpack_spec (fmtN N) fpcr.toNat true op.toNat
  have nz1 := unpack_nzs (fmtN N) fpcr.toNat true op.toNat
  have lb := unpack_lb (fmtN N) fpcr.toNat true op.toNat
  generalize Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true op.toNat = U1 at hnt d1 sp1 nz1 lb ⊢
  rcases U1 with ⟨⟨t1, s1, v1⟩, x1⟩
  simp only at hnt d1 sp1 nz1 lb ⊢
  have hNe : (N : Int) ≠ 16 := by rcases hN with rfl | rfl <;> decide
  have hE := nt_right hnt
  by_cases hn : t1.isNaN = true
  · have ht : t1 = .snan ∨ t1 = .qnan := by cases t1 <;> simp_all [Janus.Arm64.FP.FPType.isNaN]
    have hc1 : (aslFPType t1 == FPType.FPType_SNaN) = true ∨ (aslFPType t1 == FPType.FPType_QNaN) = true := by
      rcases ht with rfl | rfl <;> simp only [aslFPType] <;> decide
    simp only [if_pos hn] at hE ⊢
    rw [if_pos hc1]
    have hen : t1 = .snan → fpcr.getLsbD 8 = false := by
      intro h; subst h
      exact getLsbD_of_testBit (nt_raise_ioc (by simpa [Janus.Arm64.FP.processNaN] using hE))
    have := run_FPProcessNaN hN hc t1 ht op fpcr (v ||| BitVec.ofNat 64 x1.proc) hen
    simp only [FPProcessNaN]
    rw [this]
    simp only [exc_append_proc, exc_append_direct, d1, BitVec.or_zero, ofNat_or, BitVec.or_assoc, processNaN_direct',
      ofNat0, BitVec.zero_or]
  simp only [if_neg hn] at hE ⊢
  have hc1 : ¬ ((aslFPType t1 == FPType.FPType_SNaN) = true ∨ (aslFPType t1 == FPType.FPType_QNaN) = true) := by
    intro h; apply hn; cases t1 <;> first | rfl | (simp only [aslFPType] at h; revert h; decide)
  rw [if_neg hc1]
  cfg_simp [asl_beq_inf, asl_beq_zero, ofBool_eq_zero, ofBool_eq_one']
  by_cases hz : t1 = .zero
  · simp only [if_pos hz] at hE ⊢
    rw [FPZero_ofBool hN]
    simp only [exc_append_proc, exc_append_direct, d1, exc_empty_proc, exc_empty_direct, BitVec.or_zero, ofNat_or,
      ofNat0, BitVec.zero_or]
    rfl
  simp only [if_neg hz] at hE ⊢
  by_cases hi : t1 = .infinity ∧ s1 = false
  · simp only [if_pos hi] at hE ⊢
    rw [FPInf_ofBool hN]
    simp only [exc_append_proc, exc_append_direct, d1, exc_empty_proc, exc_empty_direct, BitVec.or_zero, ofNat_or,
      ofNat0, BitVec.zero_or]
    rfl
  simp only [if_neg hi] at hE ⊢
  by_cases hs : s1 = true
  · simp only [if_pos hs] at hE ⊢
    have hbit : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false := getLsbD_of_testBit (nt_raise_ioc (by simpa [hs] using hE))
    have Rdn := run_FPDefaultNaN hN (hc.set_FPSR (v ||| BitVec.ofNat 64 x1.proc)) fpcr
    have Rpe := run_PE_set hc .FPExc_InvalidOp fpcr hbit
    cfg_simp [Rdn, Rpe]
    fp_or_closeS
  simp only [if_neg hs] at hE ⊢
  have hs0 : s1 = false := by simpa using hs
  have ht : t1 = .nonzero ∨ t1 = .denormal := by
    cases t1 <;> simp_all [Janus.Arm64.FP.FPType.isNaN]
  have hnc : ¬ ((decide (t1 = .infinity) && !s1) = true) := by rcases ht with rfl | rfl <;> simp
  simp only [if_neg hnc] at hE
  obtain ⟨n, e', hv, hn0, hsn⟩ := nz1 ht
  have hlb := lb n e' hv hn0
  have hlb' : -1074 ≤ e' := by
    have : -1074 ≤ (fmtN N).emin - ((fmtN N).fbits : Int) := by rcases hN with rfl | rfl <;> decide
    omega
  have hfb := fbits_le N hN
  subst hv
  have hpos : 0 < n := by
    rw [hs0] at hsn
    have : ¬ n < 0 := by simpa using hsn.symm
    omega
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hpos)
  have hk0 : k ≠ 0 := by omega
  simp only [Janus.Float.Val.mag, Int.natAbs_natCast] at hE ⊢
  have hbig := hbig_of k hk0 e' (by omega)
  have hrange : -1100 ≤ (Janus.Float.sqrtOdd (fmtN N).fbits k e').2 + 1 := by
    unfold Janus.Float.sqrtOdd; simp only []; omega
  obtain ⟨hside, hbg⟩ := sqrt_side (fmtN N).fbits k e' hk0 hbig hrange
  generalize hdo : Janus.Float.sqrtOdd (fmtN N).fbits k e' = dd at hside hbg hE ⊢
  have hMne : dd.1 ≠ 0 := by
    have := Nat.two_pow_pos ((fmtN N).fbits + 4); omega
  have hlog : ((fmtN N).fbits + 4 : Nat) ≤ Nat.log2 dd.1 := (Nat.le_log2 hMne).mpr hbg
  have hg : (dd.2 + 1) + ((fmtN N).fbits : Int) + 1 ≤ (Nat.log2 dd.1 : Int) + dd.2 := by omega
  have Rr := fun v' => run_FPRoundDefault_side hN hc hsm fpcr v' false dd.1 hMne dd.2 _ hside hg (nt_left hE)
  simp only [Bool.false_eq_true, ite_false] at Rr
  have Rden := fun v' => run_FPProcessDenorm hc t1 (N : Int) hNe fpcr v' (nt_pd1 (nt_right hE))
  have hq : valRat (Janus.Float.Val.num (k : Int) e') = (k : Rat) * 2 ^ e' := by
    rw [valRat_num, Rat.intCast_natCast]
  rw [hq]
  cfg_simp [Rr, Rden]
  fp_or_closeS

end JanusASL.Proofs
