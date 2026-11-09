import JanusASL.Proofs.FP.Unpack
import JanusASL.Proofs.FP.Prim
import JanusASL.Proofs.FP.ImpDef
import JanusASL.Proofs.FP.FPRoundSide

/-! # `FPUnpackCV` and `FPRoundCV`: `FPUnpack` and `FPRound` with `FPCR.FZ16` instead of `FPCR.AHP` cleared -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem upd19_bit (fpcr : BitVec 64) (i : Nat) (hi : i ≠ 19) :
    (Sail.BitVec.updateSubrange fpcr 19 19 0#1).toNat / 2 ^ i % 2 = fpcr.toNat / 2 ^ i % 2 := by
  have key : (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD i = fpcr.getLsbD i := by
    simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
    simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
    intro h
    have hi64 : i < 64 := by
      rcases Nat.lt_or_ge i 64 with h' | h'
      · exact h'
      · rw [BitVec.getLsbD_of_ge fpcr i h'] at h; cases h
    have key : ∀ j < 64, j ≠ 19 → (18446744073709027327#64).getLsbD j = true := by decide
    exact key i hi64 hi
  have h1 := toNat_bit_eq_getLsbD (Sail.BitVec.updateSubrange fpcr 19 19 0#1) i
  have h2 := toNat_bit_eq_getLsbD fpcr i
  have b1 : (Sail.BitVec.updateSubrange fpcr 19 19 0#1).toNat / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by decide)
  have b2 : fpcr.toNat / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [key] at h1
  cases hb : fpcr.getLsbD i <;> simp [hb] at h1 h2 <;> omega

theorem upd19_getLsbD (fpcr : BitVec 64) (i : Nat) (hi : i ≠ 19) :
    (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD i = fpcr.getLsbD i := by
  have h := upd19_bit fpcr i hi
  have h1 := toNat_bit_eq_getLsbD (Sail.BitVec.updateSubrange fpcr 19 19 0#1) i
  have h2 := toNat_bit_eq_getLsbD fpcr i
  rw [h] at h1
  cases hb : fpcr.getLsbD i <;> cases hb' : (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD i <;> simp_all

theorem fpRound_upd19 (f : Janus.Float.Fmt) (fpcr : BitVec 64) (rm : Janus.Float.RM) (neg : Bool) (m : Nat) (e : Int) :
    Janus.Arm64.FP.fpRound f (Sail.BitVec.updateSubrange fpcr 19 19 0#1).toNat rm neg m e =
      Janus.Arm64.FP.fpRound f fpcr.toNat rm neg m e := by
  unfold Janus.Arm64.FP.fpRound Janus.Arm64.FP.ah Janus.Arm64.FP.fz Janus.Arm64.FP.ufe Janus.Arm64.FP.fpcrBit
  rw [upd19_bit fpcr 1 (by decide), upd19_bit fpcr 24 (by decide), upd19_bit fpcr 11 (by decide)]

theorem run_FPUnpackCV32 {s : SState} (hc : LinuxEL0Config s) (x : BitVec 32) (fpcr : BitVec 64)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs) (hen : (Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true x.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false) :
    (FPUnpackCV x fpcr).run s =
      let r := Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2)
        (if r.2.proc = 0 then s else s.set .FPSR (Sail.BitVec.update xs 7 1#1)) := by
  by_cases hb : fpcr.getLsbD 15 = false
  · have hen := hb
    cfg_simp [FPUnpackCV, FPUnpackBase, FPUnpackBase__1, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
      undefined_FPType, undefined_real, Sail.BitVec.length, run_internal_pick]
    simp only [isZero_toNat, isOnes_eq, extractLsb_toNat', access_eq x 31 (by decide),
      access_eq (w := 23) _ 22 (by decide), get_FZ, get_AH, get_FIZ,
      upd19_bit fpcr 24 (by decide), upd19_bit fpcr 1 (by decide), upd19_bit fpcr 0 (by decide), ofBool_eq_one,
      Janus.Arm64.FP.unpack, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
      Janus.Float.binary32, Janus.Float.Fmt.expMax, Janus.Float.Fmt.quietBit, Janus.Float.Fmt.signBit,
      Janus.Arm64.FP.fz, Janus.Arm64.FP.fiz, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit]
    generalize hn : x.toNat = n
    have hn32 : n < 2 ^ 32 := hn ▸ x.isLt
    have hen1' : (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD (fpExcBit .FPExc_InputDenorm + 8) = false := by
      have h1 := toNat_bit_eq_getLsbD (Sail.BitVec.updateSubrange fpcr 19 19 0#1) 15
      have h2 := toNat_bit_eq_getLsbD fpcr 15
      rw [upd19_bit fpcr 15 (by decide)] at h1
      simp only [fpExcBit]
      cases hb : (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD 15 <;> simp_all
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.pow_zero, Nat.div_one,
      Janus.Float.valueOf, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
      Janus.Float.mantOf, Janus.Float.ulpExpOf, Janus.Float.binary32, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias,
      Janus.Float.Fmt.expMax, Janus.Float.Fmt.signBit, Janus.Float.Fmt.quietBit]
    by_cases he0 : n / 8388608 % 256 = 0
    · by_cases hm0 : n % 8388608 = 0
      · simp [he0, hm0, aslFPType, valRat, neg_real]; rfl
      · by_cases hfz : fpcr.toNat / 16777216 % 2 = 1 <;> by_cases hah : fpcr.toNat / 2 % 2 = 1 <;>
        by_cases hfiz : fpcr.toNat % 2 = 1 <;>
        simp [he0, hm0, hfz, hah, hfiz, aslFPType, valRat, neg_real, run_map,
          run_FPProcessException hc _ _ hen1' hx, Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC, fpExcBit] <;>
        first | rfl | (constructor; rfl; (by_cases hs : n / 2147483648 % 2 = 1 <;>
          simp [hs, subnormal_val, Rat.intCast_neg, Rat.neg_mul]))
    · by_cases he1 : n / 8388608 % 256 = 255
      · by_cases hm0 : n % 8388608 = 0
        · by_cases hs : n / 2147483648 % 2 = 1 <;> simp [he0, he1, hm0, hs, aslFPType, valRat, neg_real] <;>
          first | rfl
        · by_cases hq : n % 8388608 / 4194304 % 2 = 1 <;>
          simp [he0, he1, hm0, hq, aslFPType, valRat, neg_real] <;> first | rfl
      · by_cases hs : n / 2147483648 % 2 = 1 <;>
        simp [he0, he1, hs, aslFPType, valRat, neg_real, normal_val32, Rat.neg_mul,
          show (↑n / 8388608 % 256 - 127 - 23 : Int) = ↑n / 8388608 % 256 - 127 - 23 from rfl] <;>
        first | rfl
  · have hp0 : (Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true x.toNat).2.proc = 0 :=
      Classical.byContradiction fun h => hb (hen h)
    cfg_simp [FPUnpackCV, FPUnpackBase, FPUnpackBase__1, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
      undefined_FPType, undefined_real, Sail.BitVec.length, run_internal_pick]
    simp only [isZero_toNat, isOnes_eq, extractLsb_toNat', access_eq x 31 (by decide),
      access_eq (w := 23) _ 22 (by decide), get_FZ, get_AH, get_FIZ,
      upd19_bit fpcr 24 (by decide), upd19_bit fpcr 1 (by decide), upd19_bit fpcr 0 (by decide), ofBool_eq_one,
      Janus.Arm64.FP.unpack, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
      Janus.Float.binary32, Janus.Float.Fmt.expMax, Janus.Float.Fmt.quietBit, Janus.Float.Fmt.signBit,
      Janus.Arm64.FP.fz, Janus.Arm64.FP.fiz, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit] at hp0 ⊢
    generalize hn : x.toNat = n at hp0 ⊢
    have hn32 : n < 2 ^ 32 := hn ▸ x.isLt
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.pow_zero, Nat.div_one,
      Janus.Float.valueOf, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
      Janus.Float.mantOf, Janus.Float.ulpExpOf, Janus.Float.binary32, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias,
      Janus.Float.Fmt.expMax, Janus.Float.Fmt.signBit, Janus.Float.Fmt.quietBit] at hp0 ⊢
    by_cases he0 : n / 8388608 % 256 = 0
    · by_cases hm0 : n % 8388608 = 0
      · simp [he0, hm0, aslFPType, valRat, neg_real]; rfl
      · by_cases hfz : fpcr.toNat / 16777216 % 2 = 1 <;> by_cases hah : fpcr.toNat / 2 % 2 = 1 <;>
        by_cases hfiz : fpcr.toNat % 2 = 1 <;>
        simp [he0, hm0, hfz, hah, hfiz, aslFPType, valRat, neg_real, run_map,
          Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC, fpExcBit] at hp0 ⊢ <;>
        first | rfl | (constructor; rfl; (by_cases hs : n / 2147483648 % 2 = 1 <;>
          simp [hs, subnormal_val, Rat.intCast_neg, Rat.neg_mul]))
    · by_cases he1 : n / 8388608 % 256 = 255
      · by_cases hm0 : n % 8388608 = 0
        · by_cases hs : n / 2147483648 % 2 = 1 <;> simp [he0, he1, hm0, hs, aslFPType, valRat, neg_real] <;>
          first | rfl
        · by_cases hq : n % 8388608 / 4194304 % 2 = 1 <;>
          simp [he0, he1, hm0, hq, aslFPType, valRat, neg_real] <;> first | rfl
      · by_cases hs : n / 2147483648 % 2 = 1 <;>
        simp [he0, he1, hs, aslFPType, valRat, neg_real, normal_val32, Rat.neg_mul,
          show (↑n / 8388608 % 256 - 127 - 23 : Int) = ↑n / 8388608 % 256 - 127 - 23 from rfl] <;>
        first | rfl


theorem run_FPUnpackCV64 {s : SState} (hc : LinuxEL0Config s) (x : BitVec 64) (fpcr : BitVec 64)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs) (hen : (Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true x.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false) :
    (FPUnpackCV x fpcr).run s =
      let r := Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2)
        (if r.2.proc = 0 then s else s.set .FPSR (Sail.BitVec.update xs 7 1#1)) := by
  by_cases hb : fpcr.getLsbD 15 = false
  · have hen := hb
    cfg_simp [FPUnpackCV, FPUnpackBase, FPUnpackBase__1, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
      undefined_FPType, undefined_real, Sail.BitVec.length, run_internal_pick]
    simp only [isZero_toNat, isOnes_eq, extractLsb_toNat', access_eq x 63 (by decide),
      access_eq (w := 52) _ 51 (by decide), get_FZ, get_AH, get_FIZ,
      upd19_bit fpcr 24 (by decide), upd19_bit fpcr 1 (by decide), upd19_bit fpcr 0 (by decide), ofBool_eq_one,
      Janus.Arm64.FP.unpack, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
      Janus.Float.binary64, Janus.Float.Fmt.expMax, Janus.Float.Fmt.quietBit, Janus.Float.Fmt.signBit,
      Janus.Arm64.FP.fz, Janus.Arm64.FP.fiz, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit]
    generalize hn : x.toNat = n
    have hn64 : n < 2 ^ 64 := hn ▸ x.isLt
    have hen1' : (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD (fpExcBit .FPExc_InputDenorm + 8) = false := by
      have h1 := toNat_bit_eq_getLsbD (Sail.BitVec.updateSubrange fpcr 19 19 0#1) 15
      have h2 := toNat_bit_eq_getLsbD fpcr 15
      rw [upd19_bit fpcr 15 (by decide)] at h1
      simp only [fpExcBit]
      cases hb : (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD 15 <;> simp_all
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.pow_zero, Nat.div_one,
      Janus.Float.valueOf, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
      Janus.Float.mantOf, Janus.Float.ulpExpOf, Janus.Float.binary64, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias,
      Janus.Float.Fmt.expMax, Janus.Float.Fmt.signBit, Janus.Float.Fmt.quietBit]
    by_cases he0 : n / 4503599627370496 % 2048 = 0
    · by_cases hm0 : n % 4503599627370496 = 0
      · simp [he0, hm0, aslFPType, valRat, neg_real]; rfl
      · by_cases hfz : fpcr.toNat / 16777216 % 2 = 1 <;> by_cases hah : fpcr.toNat / 2 % 2 = 1 <;>
        by_cases hfiz : fpcr.toNat % 2 = 1 <;>
        simp [he0, hm0, hfz, hah, hfiz, aslFPType, valRat, neg_real, run_map,
          run_FPProcessException hc _ _ hen1' hx, Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC, fpExcBit] <;>
        first | rfl | (constructor; rfl; (by_cases hs : n / 9223372036854775808 % 2 = 1 <;>
          simp [hs, subnormal_val, Rat.intCast_neg, Rat.neg_mul]))
    · by_cases he1 : n / 4503599627370496 % 2048 = 2047
      · by_cases hm0 : n % 4503599627370496 = 0
        · by_cases hs : n / 9223372036854775808 % 2 = 1 <;> simp [he0, he1, hm0, hs, aslFPType, valRat, neg_real] <;>
          first | rfl
        · by_cases hq : n % 4503599627370496 / 2251799813685248 % 2 = 1 <;>
          simp [he0, he1, hm0, hq, aslFPType, valRat, neg_real] <;> first | rfl
      · by_cases hs : n / 9223372036854775808 % 2 = 1 <;>
        simp [he0, he1, hs, aslFPType, valRat, neg_real, normal_val64, Rat.neg_mul,
          show (↑n / 4503599627370496 % 2048 - 1023 - 52 : Int) = ↑n / 4503599627370496 % 2048 - 1023 - 52 from rfl] <;>
        first | rfl
  · have hp0 : (Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true x.toNat).2.proc = 0 :=
      Classical.byContradiction fun h => hb (hen h)
    cfg_simp [FPUnpackCV, FPUnpackBase, FPUnpackBase__1, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
      undefined_FPType, undefined_real, Sail.BitVec.length, run_internal_pick]
    simp only [isZero_toNat, isOnes_eq, extractLsb_toNat', access_eq x 63 (by decide),
      access_eq (w := 52) _ 51 (by decide), get_FZ, get_AH, get_FIZ,
      upd19_bit fpcr 24 (by decide), upd19_bit fpcr 1 (by decide), upd19_bit fpcr 0 (by decide), ofBool_eq_one,
      Janus.Arm64.FP.unpack, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
      Janus.Float.binary64, Janus.Float.Fmt.expMax, Janus.Float.Fmt.quietBit, Janus.Float.Fmt.signBit,
      Janus.Arm64.FP.fz, Janus.Arm64.FP.fiz, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit] at hp0 ⊢
    generalize hn : x.toNat = n at hp0 ⊢
    have hn64 : n < 2 ^ 64 := hn ▸ x.isLt
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.pow_zero, Nat.div_one,
      Janus.Float.valueOf, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
      Janus.Float.mantOf, Janus.Float.ulpExpOf, Janus.Float.binary64, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias,
      Janus.Float.Fmt.expMax, Janus.Float.Fmt.signBit, Janus.Float.Fmt.quietBit] at hp0 ⊢
    by_cases he0 : n / 4503599627370496 % 2048 = 0
    · by_cases hm0 : n % 4503599627370496 = 0
      · simp [he0, hm0, aslFPType, valRat, neg_real]; rfl
      · by_cases hfz : fpcr.toNat / 16777216 % 2 = 1 <;> by_cases hah : fpcr.toNat / 2 % 2 = 1 <;>
        by_cases hfiz : fpcr.toNat % 2 = 1 <;>
        simp [he0, hm0, hfz, hah, hfiz, aslFPType, valRat, neg_real, run_map,
          Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC, fpExcBit] at hp0 ⊢ <;>
        first | rfl | (constructor; rfl; (by_cases hs : n / 9223372036854775808 % 2 = 1 <;>
          simp [hs, subnormal_val, Rat.intCast_neg, Rat.neg_mul]))
    · by_cases he1 : n / 4503599627370496 % 2048 = 2047
      · by_cases hm0 : n % 4503599627370496 = 0
        · by_cases hs : n / 9223372036854775808 % 2 = 1 <;> simp [he0, he1, hm0, hs, aslFPType, valRat, neg_real] <;>
          first | rfl
        · by_cases hq : n % 4503599627370496 / 2251799813685248 % 2 = 1 <;>
          simp [he0, he1, hm0, hq, aslFPType, valRat, neg_real] <;> first | rfl
      · by_cases hs : n / 9223372036854775808 % 2 = 1 <;>
        simp [he0, he1, hs, aslFPType, valRat, neg_real, normal_val64, Rat.neg_mul,
          show (↑n / 4503599627370496 % 2048 - 1023 - 52 : Int) = ↑n / 4503599627370496 % 2048 - 1023 - 52 from rfl] <;>
        first | rfl




theorem run_FPUnpackCV32' {s : SState} (hc : LinuxEL0Config s) (x : BitVec 32) (fpcr : BitVec 64)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs) (hen : (Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true x.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false) :
    (FPUnpackCV x fpcr).run s =
      let r := Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2) (s.set .FPSR (xs ||| BitVec.ofNat 64 r.2.proc)) := by
  rw [run_FPUnpackCV32 hc x fpcr hx hen]; dsimp only; rw [fpsr_state s hx _ (unpack_proc _ _ _ _)]

theorem run_FPUnpackCV64' {s : SState} (hc : LinuxEL0Config s) (x : BitVec 64) (fpcr : BitVec 64)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs) (hen : (Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true x.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false) :
    (FPUnpackCV x fpcr).run s =
      let r := Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2) (s.set .FPSR (xs ||| BitVec.ofNat 64 r.2.proc)) := by
  rw [run_FPUnpackCV64 hc x fpcr hx hen]; dsimp only; rw [fpsr_state s hx _ (unpack_proc _ _ _ _)]

theorem run_FPUnpackCVN {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (x : BitVec N)
    (fpcr v : BitVec 64)
    (hen : (Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true x.toNat).2.proc ≠ 0 → fpcr.getLsbD 15 = false) :
    (FPUnpackCV x fpcr).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2) (s.set .FPSR (v ||| BitVec.ofNat 64 r.2.proc)) := by
  rcases hN with rfl | rfl
  · rw [fmtN32] at hen ⊢
    have := run_FPUnpackCV32' (hc.set_FPSR v) x fpcr (get?_set_FPSR s v) hen
    exact this.trans (by simp only [set_set_FPSR])
  · rw [fmtN64] at hen ⊢
    have := run_FPUnpackCV64' (hc.set_FPSR v) x fpcr (get?_set_FPSR s v) hen
    exact this.trans (by simp only [set_set_FPSR])

theorem run_FPRoundCV_side {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s)
    (fpcr v : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (M : Nat) (hM : M ≠ 0) (x : Int)
    (q : Rat) {g : Int} (hS : Side g q ((M : Rat) * 2 ^ x))
    (hg : g + ((fmtN N).fbits : Int) + 1 ≤ (Nat.log2 M : Int) + x)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat rm neg M x).2) :
    (FPRoundCV (if neg then -q else q) fpcr (aslRM rm) N).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat rm neg M x
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have hism := run_InStreamingMode (hc.set_FPSR v) (hsm.set_FPSR v)
  unfold FPRoundCV
  simp only [run_bind, run_pure]
  have hb : ∀ k, (k = 2 ∨ k = 3 ∨ k = 4) →
      Nat.testBit (Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat rm neg M x).2.proc k = true →
      (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD (k + 8) = false := by
    intro k hk hp
    rw [upd19_getLsbD fpcr _ (by omega)]
    exact getLsbD_of_testBit (nt_bit hnt (by omega) hp)
  rcases hN with rfl | rfl
  · have hg' : g + 24 ≤ (Nat.log2 M : Int) + x := by
      have := hg; simp [fmtN, Janus.Float.binary32] at this; omega
    have hoF : Nat.testBit (rb32Of (Sail.BitVec.updateSubrange fpcr 19 19 0#1).toNat rm neg M x).2.1 2 = true →
        (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD 10 = false := by
      rw [rb32Of_eq _ rm hrm neg M hM x, fpRound_upd19]; exact hb 2 (by decide)
    have hoU : Nat.testBit (rb32Of (Sail.BitVec.updateSubrange fpcr 19 19 0#1).toNat rm neg M x).2.1 3 = true →
        (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD 11 = false := by
      rw [rb32Of_eq _ rm hrm neg M hM x, fpRound_upd19]; exact hb 3 (by decide)
    have hoI : Nat.testBit (rb32Of (Sail.BitVec.updateSubrange fpcr 19 19 0#1).toNat rm neg M x).2.1 4 = true →
        (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD 12 = false := by
      rw [rb32Of_eq _ rm hrm neg M hM x, fpRound_upd19]; exact hb 4 (by decide)
    have h1 := run_FPRoundBase32_side (hc.set_FPSR v) hism (Sail.BitVec.updateSubrange fpcr 19 19 0#1) rm hrm neg M hM x q
      hS hg' (get?_set_FPSR s v) hoF hoU hoI
    have h2 := run_FPRoundBase32 (hc.set_FPSR v) hism (Sail.BitVec.updateSubrange fpcr 19 19 0#1) rm hrm neg M hM x
      (get?_set_FPSR s v) (by rw [fpRound_upd19]; exact hb 2 (by decide)) (by rw [fpRound_upd19]; exact hb 3 (by decide))
      (by rw [fpRound_upd19]; exact hb 4 (by decide))
    rw [h1, h2]
    simp only [fpRound_upd19, set_set_FPSR, fmtN32]
  · have hg' : g + 53 ≤ (Nat.log2 M : Int) + x := by
      have := hg; simp [fmtN, Janus.Float.binary64] at this; omega
    have hoF : Nat.testBit (rb64Of (Sail.BitVec.updateSubrange fpcr 19 19 0#1).toNat rm neg M x).2.1 2 = true →
        (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD 10 = false := by
      rw [rb64Of_eq _ rm hrm neg M hM x, fpRound_upd19]; exact hb 2 (by decide)
    have hoU : Nat.testBit (rb64Of (Sail.BitVec.updateSubrange fpcr 19 19 0#1).toNat rm neg M x).2.1 3 = true →
        (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD 11 = false := by
      rw [rb64Of_eq _ rm hrm neg M hM x, fpRound_upd19]; exact hb 3 (by decide)
    have hoI : Nat.testBit (rb64Of (Sail.BitVec.updateSubrange fpcr 19 19 0#1).toNat rm neg M x).2.1 4 = true →
        (Sail.BitVec.updateSubrange fpcr 19 19 0#1).getLsbD 12 = false := by
      rw [rb64Of_eq _ rm hrm neg M hM x, fpRound_upd19]; exact hb 4 (by decide)
    have h1 := run_FPRoundBase64_side (hc.set_FPSR v) hism (Sail.BitVec.updateSubrange fpcr 19 19 0#1) rm hrm neg M hM x q
      hS hg' (get?_set_FPSR s v) hoF hoU hoI
    have h2 := run_FPRoundBase64 (hc.set_FPSR v) hism (Sail.BitVec.updateSubrange fpcr 19 19 0#1) rm hrm neg M hM x
      (get?_set_FPSR s v) (by rw [fpRound_upd19]; exact hb 2 (by decide)) (by rw [fpRound_upd19]; exact hb 3 (by decide))
      (by rw [fpRound_upd19]; exact hb 4 (by decide))
    rw [h1, h2]
    simp only [fpRound_upd19, set_set_FPSR, fmtN64]

end JanusASL.Proofs
