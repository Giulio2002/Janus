import JanusASL.Proofs.FP.Config
import JanusASL.Proofs.FP.Value

/-! # `FPUnpack` against Janus' `FP.unpack` -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-! ## Bits -/

theorem extractLsb_toNat' {w : Nat} (x : BitVec w) (hi lo : Nat) :
    (Sail.BitVec.extractLsb x hi lo).toNat = x.toNat / 2 ^ lo % 2 ^ (hi - lo + 1) := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]

theorem access_eq {w : Nat} (x : BitVec w) (i : Nat) (hi : i < w) :
    Sail.BitVec.access x i = BitVec.ofBool (x.toNat / 2 ^ i % 2 = 1) := by
  simp only [Sail.BitVec.access]; rw [getElem!_pos x i hi]
  congr 1
  rw [← BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
  simp [Nat.one_and_eq_mod_two]
  by_cases h : x.toNat / 2 ^ i % 2 = 1 <;> simp [h]

theorem isZero_toNat {w : Nat} (x : BitVec w) : IsZero x = decide (x.toNat = 0) := by
  simp only [IsZero, Sail.BitVec.length]
  by_cases h : x.toNat = 0
  · have : x = BitVec.zero w := BitVec.eq_of_toNat_eq (by simp [h])
    simp [this, h]
  · have : x ≠ 0#w := fun e => h (by rw [e]; simp)
    simp [this, h]

theorem isOnes_eq {w : Nat} (x : BitVec w) : IsOnes x = decide (x.toNat = 2 ^ w - 1) := by
  simp only [IsOnes, Sail.BitVec.length, sail_ones]
  by_cases h : x.toNat = 2 ^ w - 1
  · have : x = BitVec.allOnes w := BitVec.eq_of_toNat_eq (by simp [h])
    simp [this, h]
  · have : x ≠ BitVec.allOnes w := fun e => h (by rw [e]; simp)
    simp [this, h]

theorem ofBool_eq_one (b : Bool) : (BitVec.ofBool b = 1#1) = (b = true) := by
  cases b <;> decide

theorem toNat_bit_eq_getLsbD {w : Nat} (x : BitVec w) (i : Nat) :
    (x.toNat / 2 ^ i % 2 = 1) ↔ x.getLsbD i = true := by
  rw [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
  simp [Nat.one_and_eq_mod_two]

theorem upd26_bit (fpcr : BitVec 64) (i : Nat) (hi : i ≠ 26) :
    (Sail.BitVec.updateSubrange fpcr 26 26 0#1).toNat / 2 ^ i % 2 = fpcr.toNat / 2 ^ i % 2 := by
  have key : (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD i = fpcr.getLsbD i := by
    simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
    simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
    intro h
    have hi64 : i < 64 := by
      rcases Nat.lt_or_ge i 64 with h' | h'
      · exact h'
      · rw [BitVec.getLsbD_of_ge fpcr i h'] at h; cases h
    have key : ∀ j < 64, j ≠ 26 → (18446744073642442751#64).getLsbD j = true := by decide
    exact key i hi64 hi
  have h1 := toNat_bit_eq_getLsbD (Sail.BitVec.updateSubrange fpcr 26 26 0#1) i
  have h2 := toNat_bit_eq_getLsbD fpcr i
  have b1 : (Sail.BitVec.updateSubrange fpcr 26 26 0#1).toNat / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by decide)
  have b2 : fpcr.toNat / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [key] at h1
  cases hb : fpcr.getLsbD i <;> simp [hb] at h1 h2 <;> omega

theorem extract1_eq_one {w : Nat} (v : BitVec w) (i : Nat) :
    (Sail.BitVec.extractLsb v i i = 1#1) ↔ v.toNat / 2 ^ i % 2 = 1 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; rw [extractLsb_toNat'] at this; simpa using this
  · intro h; apply BitVec.eq_of_toNat_eq; rw [extractLsb_toNat']; simpa using h

theorem get_FZ (v : BitVec 64) : _get_FPCRType_FZ v = BitVec.ofBool (v.toNat / 2 ^ 24 % 2 = 1) := by
  apply BitVec.eq_of_toNat_eq
  show (Sail.BitVec.extractLsb v 24 24).toNat = _
  rw [extractLsb_toNat']
  rcases (by omega : v.toNat / 2 ^ 24 % 2 = 0 ∨ v.toNat / 2 ^ 24 % 2 = 1) with h | h <;> rw [h] <;> decide

theorem get_AH (v : BitVec 64) : _get_FPCRType_AH v = BitVec.ofBool (v.toNat / 2 ^ 1 % 2 = 1) := by
  apply BitVec.eq_of_toNat_eq
  show (Sail.BitVec.extractLsb v 1 1).toNat = _
  rw [extractLsb_toNat']
  rcases (by omega : v.toNat / 2 ^ 1 % 2 = 0 ∨ v.toNat / 2 ^ 1 % 2 = 1) with h | h <;> rw [h] <;> decide

theorem get_FIZ (v : BitVec 64) : _get_FPCRType_FIZ v = BitVec.ofBool (v.toNat / 2 ^ 0 % 2 = 1) := by
  apply BitVec.eq_of_toNat_eq
  show (Sail.BitVec.extractLsb v 0 0).toNat = _
  rw [extractLsb_toNat']
  rcases (by omega : v.toNat / 2 ^ 0 % 2 = 0 ∨ v.toNat / 2 ^ 0 % 2 = 1) with h | h <;> rw [h] <;> decide

theorem get_DN (v : BitVec 64) : _get_FPCRType_DN v = BitVec.ofBool (v.toNat / 2 ^ 25 % 2 = 1) := by
  apply BitVec.eq_of_toNat_eq
  show (Sail.BitVec.extractLsb v 25 25).toNat = _
  rw [extractLsb_toNat']
  rcases (by omega : v.toNat / 2 ^ 25 % 2 = 0 ∨ v.toNat / 2 ^ 25 % 2 = 1) with h | h <;> rw [h] <;> decide

/-! ## Values -/

theorem two_pow_inv (F : Nat) : (2 : Rat) ^ F * (2 : Rat) ^ (-(F : Int)) = 1 := by
  have h2 : (2 : Rat) ≠ 0 := by decide
  rw [← Rat.zpow_natCast, ← Rat.zpow_add h2, Int.add_right_neg, Rat.zpow_zero]

theorem normal_val (a : Int) (m F : Nat) :
    (2 : Rat) ^ a * (1 + (m : Rat) * 2 ^ (-(F : Int))) = ((2 ^ F + m : Nat) : Rat) * 2 ^ (a - F) := by
  have h2 : (2 : Rat) ≠ 0 := by decide
  rw [show a - F = a + (-(F : Int)) by omega, Rat.zpow_add h2, Rat.natCast_add, Rat.natCast_pow,
    ← Rat.mul_assoc, Rat.mul_comm _ ((2 : Rat) ^ a), Rat.mul_assoc, Rat.add_mul, Rat.natCast_ofNat, two_pow_inv]

theorem subnormal_val (k : Int) (a b : Int) :
    mult_real (real_power 2 a) (mult_real (to_real k) (real_power 2 b)) = (k : Rat) * 2 ^ (a + b) := by
  have h2 : (2 : Rat) ≠ 0 := by decide
  simp only [mult_real, real_power, to_real, Rat.zpow_add h2]
  rw [Rat.mul_comm, Rat.mul_assoc, Rat.mul_comm ((2 : Rat) ^ b)]
  rfl

theorem normal_valI (a : Int) (m : Int) (F : Nat) :
    (2 : Rat) ^ a * (1 + (m : Rat) * 2 ^ (-(F : Int))) = (((2 : Int) ^ F + m : Int) : Rat) * 2 ^ (a - F) := by
  have h2 : (2 : Rat) ≠ 0 := by decide
  rw [show a - F = a + (-(F : Int)) by omega, Rat.zpow_add h2, Rat.intCast_add, Rat.intCast_pow,
    ← Rat.mul_assoc, Rat.mul_comm _ ((2 : Rat) ^ a), Rat.mul_assoc, Rat.add_mul, Rat.intCast_ofNat, two_pow_inv]

theorem normal_val' (e m : Int) (F : Nat) :
    mult_real (real_power 2 e) (add_real 1 (mult_real (to_real m) (real_power 2 (-(F : Int))))) =
      (((2 : Int) ^ F + m : Int) : Rat) * 2 ^ (e - F) :=
  normal_valI e m F

theorem normal_val32 (e m : Int) :
    mult_real (real_power 2 e) (add_real 1 (mult_real (to_real m) (real_power 2 (-23)))) =
      (8388608 + (m : Rat)) * 2 ^ (e - 23) := by
  have := normal_valI e m 23
  rw [Rat.intCast_add, Rat.intCast_pow] at this
  exact this

theorem normal_val64 (e m : Int) :
    mult_real (real_power 2 e) (add_real 1 (mult_real (to_real m) (real_power 2 (-52)))) =
      (4503599627370496 + (m : Rat)) * 2 ^ (e - 52) := by
  have := normal_valI e m 52
  rw [Rat.intCast_add, Rat.intCast_pow] at this
  exact this

/-- Janus' `FPType` as the ASL's. -/
def aslFPType : Janus.Arm64.FP.FPType → ArmASL.FPType
  | .zero => .FPType_Zero
  | .denormal => .FPType_Denormal
  | .nonzero => .FPType_Nonzero
  | .infinity => .FPType_Infinity
  | .qnan => .FPType_QNaN
  | .snan => .FPType_SNaN

theorem run_FPUnpack32 {s : SState} (hc : LinuxEL0Config s) (x : BitVec 32) (fpcr : BitVec 64)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs) (hen : (Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true x.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false) :
    (FPUnpack x fpcr).run s =
      let r := Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2)
        (if r.2.proc = 0 then s else s.set .FPSR (Sail.BitVec.update xs 7 1#1)) := by
  by_cases hb : fpcr.getLsbD 15 = false
  · have hen := hb
    cfg_simp [FPUnpack, FPUnpackBase, FPUnpackBase__1, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
      undefined_FPType, undefined_real, Sail.BitVec.length, run_internal_pick]
    simp only [isZero_toNat, isOnes_eq, extractLsb_toNat', access_eq x 31 (by decide),
      access_eq (w := 23) _ 22 (by decide), get_FZ, get_AH, get_FIZ,
      upd26_bit fpcr 24 (by decide), upd26_bit fpcr 1 (by decide), upd26_bit fpcr 0 (by decide), ofBool_eq_one,
      Janus.Arm64.FP.unpack, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
      Janus.Float.binary32, Janus.Float.Fmt.expMax, Janus.Float.Fmt.quietBit, Janus.Float.Fmt.signBit,
      Janus.Arm64.FP.fz, Janus.Arm64.FP.fiz, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit]
    generalize hn : x.toNat = n
    have hn32 : n < 2 ^ 32 := hn ▸ x.isLt
    have hen1' : (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD (fpExcBit .FPExc_InputDenorm + 8) = false := by
      have h1 := toNat_bit_eq_getLsbD (Sail.BitVec.updateSubrange fpcr 26 26 0#1) 15
      have h2 := toNat_bit_eq_getLsbD fpcr 15
      rw [upd26_bit fpcr 15 (by decide)] at h1
      simp only [fpExcBit]
      cases hb : (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD 15 <;> simp_all
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
    cfg_simp [FPUnpack, FPUnpackBase, FPUnpackBase__1, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
      undefined_FPType, undefined_real, Sail.BitVec.length, run_internal_pick]
    simp only [isZero_toNat, isOnes_eq, extractLsb_toNat', access_eq x 31 (by decide),
      access_eq (w := 23) _ 22 (by decide), get_FZ, get_AH, get_FIZ,
      upd26_bit fpcr 24 (by decide), upd26_bit fpcr 1 (by decide), upd26_bit fpcr 0 (by decide), ofBool_eq_one,
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

theorem run_FPUnpack64 {s : SState} (hc : LinuxEL0Config s) (x : BitVec 64) (fpcr : BitVec 64)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs) (hen : (Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true x.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false) :
    (FPUnpack x fpcr).run s =
      let r := Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2)
        (if r.2.proc = 0 then s else s.set .FPSR (Sail.BitVec.update xs 7 1#1)) := by
  by_cases hb : fpcr.getLsbD 15 = false
  · have hen := hb
    cfg_simp [FPUnpack, FPUnpackBase, FPUnpackBase__1, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
      undefined_FPType, undefined_real, Sail.BitVec.length, run_internal_pick]
    simp only [isZero_toNat, isOnes_eq, extractLsb_toNat', access_eq x 63 (by decide),
      access_eq (w := 52) _ 51 (by decide), get_FZ, get_AH, get_FIZ,
      upd26_bit fpcr 24 (by decide), upd26_bit fpcr 1 (by decide), upd26_bit fpcr 0 (by decide), ofBool_eq_one,
      Janus.Arm64.FP.unpack, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
      Janus.Float.binary64, Janus.Float.Fmt.expMax, Janus.Float.Fmt.quietBit, Janus.Float.Fmt.signBit,
      Janus.Arm64.FP.fz, Janus.Arm64.FP.fiz, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit]
    generalize hn : x.toNat = n
    have hn64 : n < 2 ^ 64 := hn ▸ x.isLt
    have hen1' : (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD (fpExcBit .FPExc_InputDenorm + 8) = false := by
      have h1 := toNat_bit_eq_getLsbD (Sail.BitVec.updateSubrange fpcr 26 26 0#1) 15
      have h2 := toNat_bit_eq_getLsbD fpcr 15
      rw [upd26_bit fpcr 15 (by decide)] at h1
      simp only [fpExcBit]
      cases hb : (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD 15 <;> simp_all
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
    cfg_simp [FPUnpack, FPUnpackBase, FPUnpackBase__1, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
      undefined_FPType, undefined_real, Sail.BitVec.length, run_internal_pick]
    simp only [isZero_toNat, isOnes_eq, extractLsb_toNat', access_eq x 63 (by decide),
      access_eq (w := 52) _ 51 (by decide), get_FZ, get_AH, get_FIZ,
      upd26_bit fpcr 24 (by decide), upd26_bit fpcr 1 (by decide), upd26_bit fpcr 0 (by decide), ofBool_eq_one,
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

end JanusASL.Proofs
namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem unpack_proc (f : Janus.Float.Fmt) (fpcr : Nat) (e : Bool) (x : Nat) :
    (Janus.Arm64.FP.unpack f fpcr e x).2.proc = 0 ∨ (Janus.Arm64.FP.unpack f fpcr e x).2.proc = 128 := by
  unfold Janus.Arm64.FP.unpack
  split <;> (try simp) <;>
  cases Janus.Arm64.FP.fz fpcr <;> cases Janus.Arm64.FP.ah fpcr <;> cases Janus.Arm64.FP.fiz fpcr <;> cases e <;>
    simp [Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC]

theorem fpsr_state (s : SState) {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs) (p : Nat)
    (hp : p = 0 ∨ p = 128) :
    (if p = 0 then s else s.set .FPSR (Sail.BitVec.update xs 7 1#1)) = s.set .FPSR (xs ||| BitVec.ofNat 64 p) := by
  rcases hp with rfl | rfl
  · simp [SState.set_same s .FPSR xs hx]
  · simp [update_one_or xs 7 (by decide)]

theorem run_FPUnpack32' {s : SState} (hc : LinuxEL0Config s) (x : BitVec 32) (fpcr : BitVec 64)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs) (hen : (Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true x.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false) :
    (FPUnpack x fpcr).run s =
      let r := Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat true x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2) (s.set .FPSR (xs ||| BitVec.ofNat 64 r.2.proc)) := by
  rw [run_FPUnpack32 hc x fpcr hx hen]; dsimp only; rw [fpsr_state s hx _ (unpack_proc _ _ _ _)]

theorem run_FPUnpack64' {s : SState} (hc : LinuxEL0Config s) (x : BitVec 64) (fpcr : BitVec 64)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs) (hen : (Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true x.toNat).2.proc ≠ 0 →
      fpcr.getLsbD 15 = false) :
    (FPUnpack x fpcr).run s =
      let r := Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat true x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2) (s.set .FPSR (xs ||| BitVec.ofNat 64 r.2.proc)) := by
  rw [run_FPUnpack64 hc x fpcr hx hen]; dsimp only; rw [fpsr_state s hx _ (unpack_proc _ _ _ _)]

end JanusASL.Proofs
