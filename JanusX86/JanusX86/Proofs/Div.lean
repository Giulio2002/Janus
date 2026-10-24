import JanusX86.Proofs.Xchg

/-! # DIV and IDIV (`F6/F7 /6,/7`), including the divide-error (`#DE`) conditions -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem cslice16 (A B : Nat) (hA : A < 2 ^ 16) (hB : B < 2 ^ 16) :
    Sail.BitVec.truncate (bits_of_int (changeSlice_int (A : Int) (ash_left_int ((2 : Nat) : Int) 3)
      (ash_left_int ((2 : Nat) : Int) 4) (B : Int)) 128) 32 = BitVec.ofNat 32 (2 ^ 16 * B + A) := by
  have e3 : ash_left_int ((2 : Nat) : Int) 3 = ((16 : Nat) : Int) := by decide
  have e4 : ash_left_int ((2 : Nat) : Int) 4 = ((32 : Nat) : Int) := by decide
  rw [e3, e4]
  unfold changeSlice_int Sail.set_slice_int
  rw [show (128 : Nat) = 32 + 96 from rfl, trunc_bits_ofInt, BitVec.ofInt_toInt]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Int.toNat_natCast, Sail.BitVec.updateSubrange', Sail.get_slice_int, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, BitVec.ofInt_natCast]
  rw [Nat.testBit_two_pow_mul_add _ hA]
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat]
  have hAi : ∀ j, 16 ≤ j → A.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) hj))
  by_cases h16 : i < 16
  · simp [h16, hi]
  · have e1 : decide (i - 16 < 32) = true := by simp; omega
    have e2 : decide (i - 16 < 33) = true := by simp; omega
    simp [h16, hAi i (by omega), e1, e2]

theorem cslice32 (A B : Nat) (hA : A < 2 ^ 32) (hB : B < 2 ^ 32) :
    Sail.BitVec.truncate (bits_of_int (changeSlice_int (A : Int) (ash_left_int ((4 : Nat) : Int) 3)
      (ash_left_int ((4 : Nat) : Int) 4) (B : Int)) 128) 64 = BitVec.ofNat 64 (2 ^ 32 * B + A) := by
  have e3 : ash_left_int ((4 : Nat) : Int) 3 = ((32 : Nat) : Int) := by decide
  have e4 : ash_left_int ((4 : Nat) : Int) 4 = ((64 : Nat) : Int) := by decide
  rw [e3, e4]
  unfold changeSlice_int Sail.set_slice_int
  rw [show (128 : Nat) = 64 + 64 from rfl, trunc_bits_ofInt, BitVec.ofInt_toInt]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Int.toNat_natCast, Sail.BitVec.updateSubrange', Sail.get_slice_int, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, BitVec.ofInt_natCast]
  rw [Nat.testBit_two_pow_mul_add _ hA]
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat]
  have hAi : ∀ j, 32 ≤ j → A.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) hj))
  by_cases h16 : i < 32
  · simp [h16, hi]
  · have e1 : decide (i - 32 < 64) = true := by simp; omega
    have e2 : decide (i - 32 < 65) = true := by simp; omega
    simp [h16, hAi i (by omega), e1, e2]

theorem cslice64 (A B : Nat) (hA : A < 2 ^ 64) (hB : B < 2 ^ 64) :
    Sail.BitVec.truncate (bits_of_int (changeSlice_int (A : Int) (ash_left_int ((8 : Nat) : Int) 3)
      (ash_left_int ((8 : Nat) : Int) 4) (B : Int)) 128) 128 = BitVec.ofNat 128 (2 ^ 64 * B + A) := by
  have e3 : ash_left_int ((8 : Nat) : Int) 3 = ((64 : Nat) : Int) := by decide
  have e4 : ash_left_int ((8 : Nat) : Int) 4 = ((128 : Nat) : Int) := by decide
  rw [e3, e4]
  unfold changeSlice_int Sail.set_slice_int
  rw [show (128 : Nat) = 128 + 0 from rfl, trunc_bits_ofInt, BitVec.ofInt_toInt]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Int.toNat_natCast, Sail.BitVec.updateSubrange', Sail.get_slice_int, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, BitVec.ofInt_natCast]
  rw [Nat.testBit_two_pow_mul_add _ hA]
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat]
  have hAi : ∀ j, 64 ≤ j → A.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) hj))
  by_cases h16 : i < 64
  · simp [h16, hi]
  · have e1 : decide (i - 64 < 128) = true := by simp; omega
    have e2 : decide (i - 64 < 129) = true := by simp; omega
    simp [h16, hAi i (by omega), e1, e2]

theorem floor2_nat (a b : Nat) (hb : 0 < b) : floor2 (a : Int) (b : Int) = ((a / b : Nat) : Int) := by
  unfold floor2
  have h1 : Int.tdiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := by simp [Int.tdiv]
  have h2 : Int.tmod (a : Int) (b : Int) = ((a % b : Nat) : Int) := by simp [Int.tmod]
  rw [h1, h2]
  have h3 : ((((b : Int) >b 0)) && ((((a % b : Nat) : Int)) ≥b 0) || ((b : Int) <b 0) && (((a % b : Nat) : Int) ≤b 0)) = true := by
    simp; omega
  simp only [h3, ↓reduceIte]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem toNatInt_sw64 {w : Nat} (hw : w ≤ 64) (A : BitVec w) : Sail.BitVec.toNatInt (A.setWidth 64) = (A.toNat : Int) := by
  have : A.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le A.isLt (Nat.pow_le_pow_right (by decide) hw)
  simp [Sail.BitVec.toNatInt, Nat.mod_eq_of_lt this]

theorem div_val16 (A B V : BitVec 16) (hV : V ≠ 0) :
    div_spec 2 (bits_of_int (changeSlice_int (Sail.BitVec.toNatInt (A.setWidth 64)) (ash_left_int ((2 : Nat) : Int) 3)
      (ash_left_int ((2 : Nat) : Int) 4) (Sail.BitVec.toNatInt (B.setWidth 64))) 128) (V.setWidth 64) =
      if 2 ^ 16 ≤ (2 ^ 16 * B.toNat + A.toNat) / V.toNat then (true, 0#128, 0#64)
      else (false, BitVec.ofNat 128 ((2 ^ 16 * B.toNat + A.toNat) / V.toNat),
        BitVec.ofNat 64 ((2 ^ 16 * B.toNat + A.toNat) % V.toNat)) := by
  have hv0 : 0 < V.toNat := by
    have : V.toNat ≠ 0 := fun h => hV (BitVec.eq_of_toNat_eq (by simpa using h)); omega
  have hA := A.isLt; have hB := B.isLt; have hVl := V.isLt
  generalize hD : 2 ^ 16 * B.toNat + A.toNat = D
  have hDl : D < 2 ^ 32 := by rw [← hD]; omega
  simp only [div_spec, toNatInt_sw64 (w := 16) (by decide), cslice16 _ _ hA hB, hD, div_spec_16]
  have hvt : Sail.BitVec.truncate (V.setWidth 64) 16 = V := by
    apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate]
  have hq : Sail.BitVec.toNatInt (BitVec.ofNat 32 D) = (D : Int) := by simp [Sail.BitVec.toNatInt]; omega
  have hvn : Sail.BitVec.toNatInt V = (V.toNat : Int) := rfl
  simp only [hvt, hq, hvn, floor2_nat D V.toNat hv0, mod_nat D V.toNat hv0]
  have hqd : D / V.toNat ≤ D := Nat.div_le_self _ _
  have e1 : Sail.BitVec.toNatInt (bits_of_int ((D / V.toNat : Nat) : Int) 32) = ((D / V.toNat : Nat) : Int) := by
    simp only [Sail.BitVec.toNatInt, bits_of_int_natCast_toNat]; rw [Nat.mod_eq_of_lt (by omega)]; rfl
  rw [e1]
  have hr : D % V.toNat < V.toNat := Nat.mod_lt _ hv0
  by_cases hov : 2 ^ 16 ≤ D / V.toNat
  · have : ((65535 : Int) <b ((D / V.toNat : Nat) : Int)) = true := by simp; omega
    simp only [this, ↓reduceIte, if_pos hov]; rfl
  · have : ((65535 : Int) <b ((D / V.toNat : Nat) : Int)) = false := by simp; omega
    simp only [this, Bool.false_eq_true, ↓reduceIte, if_neg hov]
    congr 1
    · congr 1 <;> apply BitVec.eq_of_toNat_eq <;>
        simp only [Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
          bits_of_int_natCast_toNat, BitVec.toNat_ofNat]
      · have h1 : D / V.toNat < 2 ^ 32 := by omega
        have h2 : D / V.toNat < 2 ^ 128 := by omega
        simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
      · have h1 : D % V.toNat < 2 ^ 16 := by omega
        have h2 : D % V.toNat < 2 ^ 64 := by omega
        simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]

theorem div_val32 (A B V : BitVec 32) (hV : V ≠ 0) :
    div_spec 4 (bits_of_int (changeSlice_int (Sail.BitVec.toNatInt (A.setWidth 64)) (ash_left_int ((4 : Nat) : Int) 3)
      (ash_left_int ((4 : Nat) : Int) 4) (Sail.BitVec.toNatInt (B.setWidth 64))) 128) (V.setWidth 64) =
      if 2 ^ 32 ≤ (2 ^ 32 * B.toNat + A.toNat) / V.toNat then (true, 0#128, 0#64)
      else (false, BitVec.ofNat 128 ((2 ^ 32 * B.toNat + A.toNat) / V.toNat),
        BitVec.ofNat 64 ((2 ^ 32 * B.toNat + A.toNat) % V.toNat)) := by
  have hv0 : 0 < V.toNat := by
    have : V.toNat ≠ 0 := fun h => hV (BitVec.eq_of_toNat_eq (by simpa using h)); omega
  have hA := A.isLt; have hB := B.isLt; have hVl := V.isLt
  generalize hD : 2 ^ 32 * B.toNat + A.toNat = D
  have hDl : D < 2 ^ 64 := by rw [← hD]; omega
  simp only [div_spec, toNatInt_sw64 (w := 32) (by decide), cslice32 _ _ hA hB, hD, div_spec_32]
  have hvt : Sail.BitVec.truncate (V.setWidth 64) 32 = V := by
    apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate]
  have hq : Sail.BitVec.toNatInt (BitVec.ofNat 64 D) = (D : Int) := by simp [Sail.BitVec.toNatInt]; omega
  have hvn : Sail.BitVec.toNatInt V = (V.toNat : Int) := rfl
  simp only [hvt, hq, hvn, floor2_nat D V.toNat hv0, mod_nat D V.toNat hv0]
  have hqd : D / V.toNat ≤ D := Nat.div_le_self _ _
  have e1 : Sail.BitVec.toNatInt (bits_of_int ((D / V.toNat : Nat) : Int) 64) = ((D / V.toNat : Nat) : Int) := by
    simp only [Sail.BitVec.toNatInt, bits_of_int_natCast_toNat]; rw [Nat.mod_eq_of_lt (by omega)]; rfl
  rw [e1]
  have hr : D % V.toNat < V.toNat := Nat.mod_lt _ hv0
  by_cases hov : 2 ^ 32 ≤ D / V.toNat
  · have : ((4294967295 : Int) <b ((D / V.toNat : Nat) : Int)) = true := by simp; omega
    simp only [this, ↓reduceIte, if_pos hov]; rfl
  · have : ((4294967295 : Int) <b ((D / V.toNat : Nat) : Int)) = false := by simp; omega
    simp only [this, Bool.false_eq_true, ↓reduceIte, if_neg hov]
    congr 1
    · congr 1 <;> apply BitVec.eq_of_toNat_eq <;>
        simp only [Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
          bits_of_int_natCast_toNat, BitVec.toNat_ofNat]
      · have h1 : D / V.toNat < 2 ^ 64 := by omega
        have h2 : D / V.toNat < 2 ^ 128 := by omega
        simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
      · have h1 : D % V.toNat < 2 ^ 32 := by omega
        have h2 : D % V.toNat < 2 ^ 64 := by omega
        simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem div_val64 (A B V : BitVec 64) (hV : V ≠ 0) :
    div_spec 8 (bits_of_int (changeSlice_int (Sail.BitVec.toNatInt (A.setWidth 64)) (ash_left_int ((8 : Nat) : Int) 3)
      (ash_left_int ((8 : Nat) : Int) 4) (Sail.BitVec.toNatInt (B.setWidth 64))) 128) (V.setWidth 64) =
      if 2 ^ 64 ≤ (2 ^ 64 * B.toNat + A.toNat) / V.toNat then (true, 0#128, 0#64)
      else (false, BitVec.ofNat 128 ((2 ^ 64 * B.toNat + A.toNat) / V.toNat),
        BitVec.ofNat 64 ((2 ^ 64 * B.toNat + A.toNat) % V.toNat)) := by
  have hv0 : 0 < V.toNat := by
    have : V.toNat ≠ 0 := fun h => hV (BitVec.eq_of_toNat_eq (by simpa using h)); omega
  have hA := A.isLt; have hB := B.isLt; have hVl := V.isLt
  have hc := cslice64 A.toNat B.toNat hA hB
  rw [show ∀ X : BitVec 128, Sail.BitVec.truncate X 128 = X from fun X => by simp [Sail.BitVec.truncate]] at hc
  generalize hD : 2 ^ 64 * B.toNat + A.toNat = D at hc
  have hDl : D < 2 ^ 128 := by rw [← hD]; omega
  simp only [div_spec, toNatInt_sw64 (w := 64) (by decide), hc, div_spec_64]
  have hq : Sail.BitVec.toNatInt (BitVec.ofNat 128 D) = (D : Int) := by simp [Sail.BitVec.toNatInt]; omega
  have hvn : Sail.BitVec.toNatInt V = (V.toNat : Int) := rfl
  simp only [hq, hvn, floor2_nat D V.toNat hv0, mod_nat D V.toNat hv0]
  have hqd : D / V.toNat ≤ D := Nat.div_le_self _ _
  have e1 : Sail.BitVec.toNatInt (bits_of_int ((D / V.toNat : Nat) : Int) 128) = ((D / V.toNat : Nat) : Int) := by
    simp only [Sail.BitVec.toNatInt, bits_of_int_natCast_toNat]; rw [Nat.mod_eq_of_lt (by omega)]; rfl
  rw [e1]
  have hr : D % V.toNat < V.toNat := Nat.mod_lt _ hv0
  by_cases hov : 2 ^ 64 ≤ D / V.toNat
  · have : ((18446744073709551615 : Int) <b ((D / V.toNat : Nat) : Int)) = true := by simp; omega
    simp only [this, ↓reduceIte, if_pos hov]
  · have : ((18446744073709551615 : Int) <b ((D / V.toNat : Nat) : Int)) = false := by simp; omega
    simp only [this, Bool.false_eq_true, ↓reduceIte, if_neg hov]
    congr 1
    · congr 1 <;> apply BitVec.eq_of_toNat_eq <;> simp only [bits_of_int_natCast_toNat, BitVec.toNat_ofNat]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem div_val8 (AX : BitVec 16) (V : BitVec 8) (hV : V ≠ 0) :
    div_spec 1 (bits_of_int (Sail.BitVec.toNatInt (AX.setWidth 64)) 128) (V.setWidth 64) =
      if 2 ^ 8 ≤ AX.toNat / V.toNat then (true, 0#128, 0#64)
      else (false, BitVec.ofNat 128 (AX.toNat / V.toNat), BitVec.ofNat 64 (AX.toNat % V.toNat)) := by
  have hv0 : 0 < V.toNat := by
    have : V.toNat ≠ 0 := fun h => hV (BitVec.eq_of_toNat_eq (by simpa using h)); omega
  have hA := AX.isLt; have hVl := V.isLt
  simp only [div_spec, toNatInt_sw64 (w := 16) (by decide), div_spec_8]
  have hdt : Sail.BitVec.truncate (bits_of_int ((AX.toNat : Nat) : Int) 128) 16 = AX := by
    apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate, bits_of_int_natCast_toNat]; omega
  have hvt : Sail.BitVec.truncate (V.setWidth 64) 8 = V := by
    apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate]
  have hq : Sail.BitVec.toNatInt AX = (AX.toNat : Int) := rfl
  have hvn : Sail.BitVec.toNatInt V = (V.toNat : Int) := rfl
  simp only [hdt, hvt, hq, hvn]
  generalize hD : AX.toNat = D at hA ⊢
  simp only [floor2_nat D V.toNat hv0, mod_nat D V.toNat hv0]
  have hqd : D / V.toNat ≤ D := Nat.div_le_self _ _
  have e1 : Sail.BitVec.toNatInt (bits_of_int ((D / V.toNat : Nat) : Int) 16) = ((D / V.toNat : Nat) : Int) := by
    simp only [Sail.BitVec.toNatInt, bits_of_int_natCast_toNat]; rw [Nat.mod_eq_of_lt (by omega)]; rfl
  rw [e1]
  have hr : D % V.toNat < V.toNat := Nat.mod_lt _ hv0
  by_cases hov : 2 ^ 8 ≤ D / V.toNat
  · have : ((255 : Int) <b ((D / V.toNat : Nat) : Int)) = true := by simp; omega
    simp only [this, ↓reduceIte, if_pos hov]; rfl
  · have : ((255 : Int) <b ((D / V.toNat : Nat) : Int)) = false := by simp; omega
    simp only [this, Bool.false_eq_true, ↓reduceIte, if_neg hov]
    congr 1
    · congr 1 <;> apply BitVec.eq_of_toNat_eq <;>
        simp only [Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
          bits_of_int_natCast_toNat, BitVec.toNat_ofNat]
      · have h1 : D / V.toNat < 2 ^ 16 := by omega
        have h2 : D / V.toNat < 2 ^ 128 := by omega
        simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
      · have h1 : D % V.toNat < 2 ^ 8 := by omega
        have h2 : D % V.toNat < 2 ^ 64 := by omega
        simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]

theorem res8 (Q R : Nat) (hQ : Q < 256) (hR : R < 256) :
    Sail.BitVec.truncate (changeSlice_bits (BitVec.ofNat 128 Q) 8 8 (Sail.BitVec.truncate (BitVec.ofNat 64 R) 8)) 64 =
      (BitVec.ofNat 16 (R * 256 + Q)).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [changeSlice_bits, Sail.BitVec.updateSubrange, Sail.BitVec.truncate, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ofNat]
  simp (config := {decide := true}) only [Sail.BitVec.updateSubrange', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_ofNat, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, Int.reduceAdd, Int.reduceSub,
    Int.reduceToNat, Nat.reduceSub, Nat.reduceAdd]
  rw [show R * 256 + Q = 2 ^ 8 * R + Q by omega, Nat.testBit_two_pow_mul_add _ (show Q < 2 ^ 8 by omega)]
  have hQi : ∀ j, 8 ≤ j → Q.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show Q < 2 ^ 8 by omega) (Nat.pow_le_pow_right (by decide) hj))
  have hRi : ∀ j, 8 ≤ j → R.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show R < 2 ^ 8 by omega) (Nat.pow_le_pow_right (by decide) hj))
  by_cases h8 : i < 8
  · have e1 : decide (i < 128) = true := by simp; omega
    have e2 : decide (i < 16) = true := by simp; omega
    simp [h8, e1, e2]
  · by_cases h16 : i < 16
    · have e1 : decide (i < 128) = true := by simp; omega
      have e2 : decide (i - 8 < 128) = true := by simp; omega
      have e3 : decide (i - 8 < 8) = true := by simp; omega
      have e4 : decide (i - 8 < 64) = true := by simp; omega
      simp [h8, h16, hQi i (by omega), e1, e2, e3, e4]
    · simp [h8, h16, hQi i (by omega), hRi (i - 8) (by omega)]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_div (opc : Nat) (hopc : opc = 0xF6 ∨ opc = 0xF7) (signed : Bool)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hm : _get_modr_m_reg m = BitVec.ofNat 3 (if signed then 7 else 6)) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (if signed then x86_idiv .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib
       else x86_div .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  cases signed <;> rcases hopc with rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, hm, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

/-- Janus' flags after `DIV`/`IDIV`: all undefined. -/
def undefFlags : Janus.Amd64.Flags := ⟨none, none, none, none, none, none⟩

/-- The model's `rflags` after `DIV`/`IDIV`: the six status flags from the undefined source. -/
def divfl (r : BitVec 32) (u : Nat) : BitVec 32 :=
  _update_rflagsbits_of (_update_rflagsbits_sf (_update_rflagsbits_zf (_update_rflagsbits_af (_update_rflagsbits_pf
    (_update_rflagsbits_cf r (bits_of_int (u : Int) 1)) (bits_of_int (u : Int) 1)) (bits_of_int (u : Int) 1))
    (bits_of_int (u : Int) 1)) (bits_of_int (u : Int) 1)) (bits_of_int (u : Int) 1)

theorem flagsRel_div {f0 : Janus.Amd64.Flags} {df : Bool} {r : BitVec 32} (hr : FlagsRel f0 df r) (u : Nat) :
    FlagsRel undefFlags df (divfl r u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [divfl, undefFlags, rf_get_df_upd_cf, rf_get_df_upd_pf, rf_get_df_upd_af, rf_get_df_upd_zf,
    rf_get_df_upd_sf, rf_get_df_upd_of, rf_get_ac_upd_cf, rf_get_ac_upd_pf, rf_get_ac_upd_af, rf_get_ac_upd_zf,
    rf_get_ac_upd_sf, rf_get_ac_upd_of]
  all_goals first | exact hr.df | exact hr.ac | (intro v hv; cases hv)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- Janus' `DIV`/`IDIV` dividend `hi:lo` (`AH:AL` at 8 bits). -/
def divD (js : Janus.Amd64.State) (w : Nat) : Nat :=
  (if w = 8 then (js.getHigh 0).toNat else (js.getReg w 2).toNat) * 2 ^ w +
    (if w = 8 then (js.getReg 8 0).toNat else (js.getReg w 0).toNat)

/-- Janus' state after `DIV`/`IDIV` with quotient `q` and remainder `r`. -/
def divJ (js : Janus.Amd64.State) (w q r : Nat) : Janus.Amd64.State :=
  if w = 8 then js.putReg 16 0 (BitVec.ofNat 16 (r * 256 + q))
  else (js.putReg w 0 (BitVec.ofNat w q)).putReg w 2 (BitVec.ofNat w r)

theorem ax_split (js : Janus.Amd64.State) :
    (js.getReg 16 0).toNat = (js.getHigh 0).toNat * 2 ^ 8 + (js.getReg 8 0).toNat := by
  simp only [Janus.Amd64.State.getReg, Janus.Amd64.State.getHigh, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  generalize (js.regs 0).toNat = a
  rw [Nat.shiftRight_eq_div_pow]; omega

theorem run_divflags {u : Nat} (t : SState) (rt : BitVec 32)
    (hrt : t.regs.get? .rflags = some rt) (hut : t.regs.get? .janus_undef = some u) :
    (do
      let rflags_var ← readReg Register.rflags
      let sailval ← undef_flg ()
      writeReg Register.rflags (_update_rflagsbits_cf rflags_var sailval)
      let rflags_var ← readReg Register.rflags
      let sailval ← undef_flg ()
      writeReg Register.rflags (_update_rflagsbits_pf rflags_var sailval)
      let rflags_var ← readReg Register.rflags
      let sailval ← undef_flg ()
      writeReg Register.rflags (_update_rflagsbits_af rflags_var sailval)
      let rflags_var ← readReg Register.rflags
      let sailval ← undef_flg ()
      writeReg Register.rflags (_update_rflagsbits_zf rflags_var sailval)
      let rflags_var ← readReg Register.rflags
      let sailval ← undef_flg ()
      writeReg Register.rflags (_update_rflagsbits_sf rflags_var sailval)
      let rflags_var ← readReg Register.rflags
      let sailval ← undef_flg ()
      writeReg Register.rflags (_update_rflagsbits_of rflags_var sailval) : SailM Unit).run t =
      .ok () (t.set .rflags (divfl rt u)) := by
  have hu' : ∀ v : BitVec 32, (t.set .rflags v).regs.get? .janus_undef = some u := fun v => by
    rw [get?_set_ne _ _ (by decide)]; exact hut
  rw [← set_self hrt]
  simp only [run_bind, run_readReg (get?_set_same _ _ _), run_writeReg, set_set, run_undef_flg (hu' _), divfl,
    run_undef_flg hut, run_readReg hrt]

set_option maxHeartbeats 8000000 in
theorem run_div {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0xF6 ∨ opc = 0xF7) {w : Nat} (hw : w = if opc = 0xF6 then 8 else osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (V : BitVec w) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    (V = 0 → (x86_div .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s =
        .error (.User (.Efault "(!!FAULT-FRESH :DE NIL :DE-EXCEPTION-SOURCE-OPERAND-ZERO REG/MEM)")) s) ∧
    (V ≠ 0 → 2 ^ w ≤ divD js w / V.toNat → ∃ s1, (x86_div .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex
      (BitVec.ofNat 8 opc) (BitVec.ofNat 8 m) sib).run s =
        .error (.User (.Emsg "Model error: :UNSIGNED-DIVIDE-ERROR-OVERFLOW")) s1) ∧
    (V ≠ 0 → divD js w / V.toNat < 2 ^ w → ∃ s', (x86_div .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex
      (BitVec.ofNat 8 opc) (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (((divJ js w (divD js w / V.toNat) (divD js w % V.toNat)).setFlags undefFlags).setRip
        (BitVec.ofNat 64 (tr + inc))) s' ∧ X86Config s') := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hl := hc.log
  have hw64 : w ≤ 64 := by rw [hw]; split <;> (try rcases osz_cases p with e | e | e) <;> omega
  have hz : ((V.setWidth 64).setWidth 128 == 0#128) = decide (V = 0) := by
    have hlt := V.isLt
    have : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw64
    have ht : ((V.setWidth 64).setWidth 128).toNat = V.toNat := by
      simp only [BitVec.toNat_setWidth]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro e; apply BitVec.eq_of_toNat_eq; rw [← ht, e]; simp
    · intro e; subst e; simp
  rcases hopc with rfl | rfl
  · simp only [↓reduceIte] at hw; subst hw
    simp only [x86_div, h1, h2, h3, run_bind, run_select_operand_size hp hrv,
      show (BitVec.ofNat 8 0xF6 == 0xF6#8) = true by decide, ↓reduceIte, hsg, Int.toNat_natCast,
      show ((1 : Int)).toNat = 8 / 8 from rfl, ← bits3_zero, hX sg hsg4 hsg5, hz]
    refine ⟨fun h0 => ?_, fun h0 hov => ?_, fun h0 hok => ?_⟩
    · simp only [h0, decide_true, ↓reduceIte, x86_fault, run_throw]
    all_goals simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, run_pure, run_add_inc tr inc hinc htr,
      hlen, is_some, show (2#4 : BitVec 4) = BitVec.ofNat 4 (16 / 8) from rfl,
      show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl,
      run_rgfi_size h (w := 16) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide)), regLocOf_zero,
      regVal, trunc128, Nat.reduceDiv, div_val8 _ V h0]
    all_goals have hdD : divD js 8 = (js.getReg 16 0).toNat := by simp [divD, ax_split]
    · rw [hdD] at hov
      simp only [if_pos hov, ↓reduceIte, x86_model_error, run_throw]
      exact ⟨_, rfl⟩
    · rw [hdD] at hok ⊢
      have hv0 : 0 < V.toNat := by
        have : V.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by simpa using e)); omega
      have hr8 : (js.getReg 16 0).toNat % V.toNat < 256 := Nat.lt_trans (Nat.mod_lt _ hv0) V.isLt
      simp only [if_neg (show ¬ 2 ^ 8 ≤ (js.getReg 16 0).toNat / V.toNat by omega), Bool.false_eq_true, ↓reduceIte,
        run_pure, res8 _ _ (show (js.getReg 16 0).toNat / V.toNat < 256 by omega) hr8,
        show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl]
      have hwr := run_write_rgfi_size h hl (w := 16) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide))
        (BitVec.ofNat 16 ((js.getReg 16 0).toNat % V.toNat * 256 + (js.getReg 16 0).toNat / V.toNat))
      rw [regLocOf_zero] at hwr
      rw [hwr]
      simp only []
      have hn' : locReg (Janus.Amd64.Loc.reg 0) < 16 := by decide
      generalize hS1 : setGpr s _ (locReg (Janus.Amd64.Loc.reg 0)) = S1
      have hr1 : S1.regs.get? .rflags = some rf := by rw [← hS1, get?_setGpr_of_not s _ hn' rfl]; exact hr
      have hu1 : S1.regs.get? .janus_undef = some u := by rw [← hS1, get?_setGpr_of_not s _ hn' rfl]; exact hu
      have hl1 : S1.regs.get? .log_register_writes = some false := by
        rw [← hS1, get?_setGpr_of_not s _ hn' rfl]; exact hl
      have hu1' : ∀ v : BitVec 32, (S1.set .rflags v).regs.get? .janus_undef = some u := fun v => by
        rw [get?_set_ne _ _ (by decide)]; exact hu1
      simp only [run_readReg hr1, run_writeReg, run_readReg (get?_set_same _ _ _), set_set, run_undef_flg (hu1' _),
        run_undef_flg hu1, run_bind]
      refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl1) _ htr, ?_, ?_⟩
      · have hrel1 := h.writeReg p.rex.isSome (n := 0) (by decide)
          (BitVec.ofNat 16 ((js.getReg 16 0).toNat % V.toNat * 256 + (js.getReg 16 0).toNat / V.toNat))
        rw [regLocOf_zero, hS1] at hrel1
        have := hrel1.flagsRip undefFlags (divfl rf u) (flagsRel_div hfr u) (BitVec.ofNat 64 (tr + inc))
        simp only [divJ, ↓reduceIte, regWrite] at this ⊢
        exact this
      · rw [← hS1]; exact ((hc.setGpr hn' _).set (by decide) _).set (by decide) _
  · simp only [show ¬ ((0xF7 : Nat) = 0xF6) by decide, ↓reduceIte] at hw
    have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
      rw [hw]; unfold osz; cases rexW p <;> cases p.opsize <;> simp
    have hW3 : w = 16 ∨ w = 32 ∨ w = 64 := by rw [hw]; exact osz_cases p
    rcases hW3 with rfl | rfl | rfl
    · have hA := run_rgfi_size h (w := 16) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) (s := s)
      have hB := run_rgfi_size h (w := 16) (by decide) _ rex hrex (n := 2) (by decide) (Or.inl (by decide)) (s := s)
      rw [regLocOf_zero] at hA
      rw [show regLocOf p.rex.isSome 16 2 = .reg 2 from rfl] at hB
      simp only [regVal] at hA hB
      simp only [x86_div, h1, h2, h3, run_bind, run_select_operand_size hp hrv,
        show (BitVec.ofNat 8 0xF7 == 0xF6#8) = false by decide, Bool.false_eq_true, ↓reduceIte, hsz, hsg,
        Int.toNat_natCast, ← bits3_zero, hX sg hsg4 hsg5, hz]
      have hdD : divD js 16 = 2 ^ 16 * (js.getReg 16 2).toNat + (js.getReg 16 0).toNat := by
        simp only [divD, show ¬ (16 = 8) by decide, ↓reduceIte]; rw [Nat.mul_comm]
      rw [hdD]
      refine ⟨fun h0 => ?_, fun h0 hov => ?_, fun h0 hok => ?_⟩
      · simp only [h0, decide_true, ↓reduceIte, x86_fault, run_throw]
      all_goals simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, run_pure, run_add_inc tr inc hinc htr,
        hlen, is_some, nbytes_eq 16 (by decide), show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl,
        show (0x2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl, hA, hB, trunc128, Nat.reduceDiv,
        div_val16 _ _ V h0]
      · simp only [if_pos hov, ↓reduceIte, x86_model_error, run_throw]
        exact ⟨_, rfl⟩
      · have hv0 : 0 < V.toNat := by
          have : V.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by simpa using e)); omega
        generalize hDD : 2 ^ 16 * (js.getReg 16 2).toNat + (js.getReg 16 0).toNat = D at hok ⊢
        have hrm : D % V.toNat < 2 ^ 16 := Nat.lt_trans (Nat.mod_lt _ hv0) V.isLt
        have hq1 : D / V.toNat < 2 ^ 16 := hok
        have hq' : Sail.BitVec.truncate (BitVec.ofNat 128 (D / V.toNat)) 64 = (BitVec.ofNat 16 (D / V.toNat)).setWidth 64 := by
          apply BitVec.eq_of_toNat_eq
          simp only [Sail.BitVec.truncate, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          simp only [Nat.mod_eq_of_lt (show D / V.toNat < 2 ^ 128 by omega), Nat.mod_eq_of_lt (show D / V.toNat < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt hq1]
        have hr' : BitVec.ofNat 64 (D % V.toNat) = (BitVec.ofNat 16 (D % V.toNat)).setWidth 64 := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          simp only [Nat.mod_eq_of_lt (show D % V.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt hrm]
        simp only [if_neg (show ¬ 2 ^ 16 ≤ D / V.toNat by omega), Bool.false_eq_true, ↓reduceIte, run_pure, hq', hr']
        have hwr := run_write_rgfi_size h hl (w := 16) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide))
          (BitVec.ofNat 16 (D / V.toNat))
        rw [regLocOf_zero] at hwr
        try simp only [show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl, show (2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl]
        rw [hwr]
        simp only []
        have hn0 : locReg (Janus.Amd64.Loc.reg 0) < 16 := by decide
        have hn2 : locReg (Janus.Amd64.Loc.reg 2) < 16 := by decide
        have hrel1 := h.writeReg p.rex.isSome (n := 0) (by decide) (BitVec.ofNat 16 (D / V.toNat))
        rw [regLocOf_zero] at hrel1
        have hl0 : (setGpr s ((regWrite js 16 (Janus.Amd64.Loc.reg 0) (BitVec.ofNat 16 (D / V.toNat))).regs
            (locReg (Janus.Amd64.Loc.reg 0))) (locReg (Janus.Amd64.Loc.reg 0))).regs.get? .log_register_writes =
            some false := by rw [get?_setGpr_of_not s _ hn0 rfl]; exact hl
        have hwr2 := run_write_rgfi_size hrel1 hl0 (w := 16) (by decide) _ rex hrex (n := 2) (by decide)
          (Or.inl (by decide)) (BitVec.ofNat 16 (D % V.toNat))
        rw [show regLocOf p.rex.isSome 16 2 = .reg 2 from rfl] at hwr2

        rw [hwr2]
        simp only []
        generalize hS1 : setGpr (setGpr s _ (locReg (Janus.Amd64.Loc.reg 0))) _ (locReg (Janus.Amd64.Loc.reg 2)) = S1
        have hr1 : S1.regs.get? .rflags = some rf := by
          rw [← hS1, get?_setGpr_of_not _ _ hn2 rfl, get?_setGpr_of_not s _ hn0 rfl]; exact hr
        have hu1 : S1.regs.get? .janus_undef = some u := by
          rw [← hS1, get?_setGpr_of_not _ _ hn2 rfl, get?_setGpr_of_not s _ hn0 rfl]; exact hu
        have hl1 : S1.regs.get? .log_register_writes = some false := by
          rw [← hS1, get?_setGpr_of_not _ _ hn2 rfl]; exact hl0
        have hu1' : ∀ v : BitVec 32, (S1.set .rflags v).regs.get? .janus_undef = some u := fun v => by
          rw [get?_set_ne _ _ (by decide)]; exact hu1
        simp only [run_readReg hr1, run_writeReg, run_readReg (get?_set_same _ _ _), set_set, run_undef_flg (hu1' _),
          run_undef_flg hu1, run_bind]
        refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl1) _ htr, ?_, ?_⟩
        · have hrel2 := hrel1.writeReg p.rex.isSome (n := 2) (by decide) (BitVec.ofNat 16 (D % V.toNat))
          rw [show regLocOf p.rex.isSome 16 2 = .reg 2 from rfl, hS1] at hrel2
          have := hrel2.flagsRip undefFlags (divfl rf u) (flagsRel_div hfr u) (BitVec.ofNat 64 (tr + inc))
          simp only [divJ, show ¬ (16 = 8) by decide, ↓reduceIte, regWrite] at this ⊢
          exact this
        · rw [← hS1]; exact (((hc.setGpr hn0 _).setGpr hn2 _).set (by decide) _).set (by decide) _
    · have hA := run_rgfi_size h (w := 32) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) (s := s)
      have hB := run_rgfi_size h (w := 32) (by decide) _ rex hrex (n := 2) (by decide) (Or.inl (by decide)) (s := s)
      rw [regLocOf_zero] at hA
      rw [show regLocOf p.rex.isSome 32 2 = .reg 2 from rfl] at hB
      simp only [regVal] at hA hB
      simp only [x86_div, h1, h2, h3, run_bind, run_select_operand_size hp hrv,
        show (BitVec.ofNat 8 0xF7 == 0xF6#8) = false by decide, Bool.false_eq_true, ↓reduceIte, hsz, hsg,
        Int.toNat_natCast, ← bits3_zero, hX sg hsg4 hsg5, hz]
      have hdD : divD js 32 = 2 ^ 32 * (js.getReg 32 2).toNat + (js.getReg 32 0).toNat := by
        simp only [divD, show ¬ (32 = 8) by decide, ↓reduceIte]; rw [Nat.mul_comm]
      rw [hdD]
      refine ⟨fun h0 => ?_, fun h0 hov => ?_, fun h0 hok => ?_⟩
      · simp only [h0, decide_true, ↓reduceIte, x86_fault, run_throw]
      all_goals simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, run_pure, run_add_inc tr inc hinc htr,
        hlen, is_some, nbytes_eq 32 (by decide), show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl,
        show (0x2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl, hA, hB, trunc128, Nat.reduceDiv,
        div_val32 _ _ V h0]
      · simp only [if_pos hov, ↓reduceIte, x86_model_error, run_throw]
        exact ⟨_, rfl⟩
      · have hv0 : 0 < V.toNat := by
          have : V.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by simpa using e)); omega
        generalize hDD : 2 ^ 32 * (js.getReg 32 2).toNat + (js.getReg 32 0).toNat = D at hok ⊢
        have hrm : D % V.toNat < 2 ^ 32 := Nat.lt_trans (Nat.mod_lt _ hv0) V.isLt
        have hq1 : D / V.toNat < 2 ^ 32 := hok
        have hq' : Sail.BitVec.truncate (BitVec.ofNat 128 (D / V.toNat)) 64 = (BitVec.ofNat 32 (D / V.toNat)).setWidth 64 := by
          apply BitVec.eq_of_toNat_eq
          simp only [Sail.BitVec.truncate, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          simp only [Nat.mod_eq_of_lt (show D / V.toNat < 2 ^ 128 by omega), Nat.mod_eq_of_lt (show D / V.toNat < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt hq1]
        have hr' : BitVec.ofNat 64 (D % V.toNat) = (BitVec.ofNat 32 (D % V.toNat)).setWidth 64 := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          simp only [Nat.mod_eq_of_lt (show D % V.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt hrm]
        simp only [if_neg (show ¬ 2 ^ 32 ≤ D / V.toNat by omega), Bool.false_eq_true, ↓reduceIte, run_pure, hq', hr']
        have hwr := run_write_rgfi_size h hl (w := 32) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide))
          (BitVec.ofNat 32 (D / V.toNat))
        rw [regLocOf_zero] at hwr
        try simp only [show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl, show (2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl]
        rw [hwr]
        simp only []
        have hn0 : locReg (Janus.Amd64.Loc.reg 0) < 16 := by decide
        have hn2 : locReg (Janus.Amd64.Loc.reg 2) < 16 := by decide
        have hrel1 := h.writeReg p.rex.isSome (n := 0) (by decide) (BitVec.ofNat 32 (D / V.toNat))
        rw [regLocOf_zero] at hrel1
        have hl0 : (setGpr s ((regWrite js 32 (Janus.Amd64.Loc.reg 0) (BitVec.ofNat 32 (D / V.toNat))).regs
            (locReg (Janus.Amd64.Loc.reg 0))) (locReg (Janus.Amd64.Loc.reg 0))).regs.get? .log_register_writes =
            some false := by rw [get?_setGpr_of_not s _ hn0 rfl]; exact hl
        have hwr2 := run_write_rgfi_size hrel1 hl0 (w := 32) (by decide) _ rex hrex (n := 2) (by decide)
          (Or.inl (by decide)) (BitVec.ofNat 32 (D % V.toNat))
        rw [show regLocOf p.rex.isSome 32 2 = .reg 2 from rfl] at hwr2

        rw [hwr2]
        simp only []
        generalize hS1 : setGpr (setGpr s _ (locReg (Janus.Amd64.Loc.reg 0))) _ (locReg (Janus.Amd64.Loc.reg 2)) = S1
        have hr1 : S1.regs.get? .rflags = some rf := by
          rw [← hS1, get?_setGpr_of_not _ _ hn2 rfl, get?_setGpr_of_not s _ hn0 rfl]; exact hr
        have hu1 : S1.regs.get? .janus_undef = some u := by
          rw [← hS1, get?_setGpr_of_not _ _ hn2 rfl, get?_setGpr_of_not s _ hn0 rfl]; exact hu
        have hl1 : S1.regs.get? .log_register_writes = some false := by
          rw [← hS1, get?_setGpr_of_not _ _ hn2 rfl]; exact hl0
        have hu1' : ∀ v : BitVec 32, (S1.set .rflags v).regs.get? .janus_undef = some u := fun v => by
          rw [get?_set_ne _ _ (by decide)]; exact hu1
        simp only [run_readReg hr1, run_writeReg, run_readReg (get?_set_same _ _ _), set_set, run_undef_flg (hu1' _),
          run_undef_flg hu1, run_bind]
        refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl1) _ htr, ?_, ?_⟩
        · have hrel2 := hrel1.writeReg p.rex.isSome (n := 2) (by decide) (BitVec.ofNat 32 (D % V.toNat))
          rw [show regLocOf p.rex.isSome 32 2 = .reg 2 from rfl, hS1] at hrel2
          have := hrel2.flagsRip undefFlags (divfl rf u) (flagsRel_div hfr u) (BitVec.ofNat 64 (tr + inc))
          simp only [divJ, show ¬ (32 = 8) by decide, ↓reduceIte, regWrite] at this ⊢
          exact this
        · rw [← hS1]; exact (((hc.setGpr hn0 _).setGpr hn2 _).set (by decide) _).set (by decide) _
    · have hA := run_rgfi_size h (w := 64) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) (s := s)
      have hB := run_rgfi_size h (w := 64) (by decide) _ rex hrex (n := 2) (by decide) (Or.inl (by decide)) (s := s)
      rw [regLocOf_zero] at hA
      rw [show regLocOf p.rex.isSome 64 2 = .reg 2 from rfl] at hB
      simp only [regVal] at hA hB
      simp only [x86_div, h1, h2, h3, run_bind, run_select_operand_size hp hrv,
        show (BitVec.ofNat 8 0xF7 == 0xF6#8) = false by decide, Bool.false_eq_true, ↓reduceIte, hsz, hsg,
        Int.toNat_natCast, ← bits3_zero, hX sg hsg4 hsg5, hz]
      have hdD : divD js 64 = 2 ^ 64 * (js.getReg 64 2).toNat + (js.getReg 64 0).toNat := by
        simp only [divD, show ¬ (64 = 8) by decide, ↓reduceIte]; rw [Nat.mul_comm]
      rw [hdD]
      refine ⟨fun h0 => ?_, fun h0 hov => ?_, fun h0 hok => ?_⟩
      · simp only [h0, decide_true, ↓reduceIte, x86_fault, run_throw]
      all_goals simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, run_pure, run_add_inc tr inc hinc htr,
        hlen, is_some, nbytes_eq 64 (by decide), show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl,
        show (0x2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl, hA, hB, trunc128, Nat.reduceDiv,
        div_val64 _ _ V h0]
      · simp only [if_pos hov, ↓reduceIte, x86_model_error, run_throw]
        exact ⟨_, rfl⟩
      · have hv0 : 0 < V.toNat := by
          have : V.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by simpa using e)); omega
        generalize hDD : 2 ^ 64 * (js.getReg 64 2).toNat + (js.getReg 64 0).toNat = D at hok ⊢
        have hrm : D % V.toNat < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ hv0) V.isLt
        have hq1 : D / V.toNat < 2 ^ 64 := hok
        have hq' : Sail.BitVec.truncate (BitVec.ofNat 128 (D / V.toNat)) 64 = (BitVec.ofNat 64 (D / V.toNat)).setWidth 64 := by
          apply BitVec.eq_of_toNat_eq
          simp only [Sail.BitVec.truncate, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          simp only [Nat.mod_eq_of_lt (show D / V.toNat < 2 ^ 128 by omega), Nat.mod_eq_of_lt (show D / V.toNat < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt hq1]
        have hr' : BitVec.ofNat 64 (D % V.toNat) = (BitVec.ofNat 64 (D % V.toNat)).setWidth 64 := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          simp only [Nat.mod_eq_of_lt (show D % V.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt hrm]
        simp only [if_neg (show ¬ 2 ^ 64 ≤ D / V.toNat by omega), Bool.false_eq_true, ↓reduceIte, run_pure, hq']
        have hwr := run_write_rgfi_size h hl (w := 64) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide))
          (BitVec.ofNat 64 (D / V.toNat))
        rw [regLocOf_zero] at hwr
        try simp only [show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl, show (2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl]
        rw [hwr]
        simp only []
        have hn0 : locReg (Janus.Amd64.Loc.reg 0) < 16 := by decide
        have hn2 : locReg (Janus.Amd64.Loc.reg 2) < 16 := by decide
        have hrel1 := h.writeReg p.rex.isSome (n := 0) (by decide) (BitVec.ofNat 64 (D / V.toNat))
        rw [regLocOf_zero] at hrel1
        have hl0 : (setGpr s ((regWrite js 64 (Janus.Amd64.Loc.reg 0) (BitVec.ofNat 64 (D / V.toNat))).regs
            (locReg (Janus.Amd64.Loc.reg 0))) (locReg (Janus.Amd64.Loc.reg 0))).regs.get? .log_register_writes =
            some false := by rw [get?_setGpr_of_not s _ hn0 rfl]; exact hl
        have hwr2 := run_write_rgfi_size hrel1 hl0 (w := 64) (by decide) _ rex hrex (n := 2) (by decide)
          (Or.inl (by decide)) (BitVec.ofNat 64 (D % V.toNat))
        rw [show regLocOf p.rex.isSome 64 2 = .reg 2 from rfl, BitVec.setWidth_eq] at hwr2

        rw [hwr2]
        simp only []
        generalize hS1 : setGpr (setGpr s _ (locReg (Janus.Amd64.Loc.reg 0))) _ (locReg (Janus.Amd64.Loc.reg 2)) = S1
        have hr1 : S1.regs.get? .rflags = some rf := by
          rw [← hS1, get?_setGpr_of_not _ _ hn2 rfl, get?_setGpr_of_not s _ hn0 rfl]; exact hr
        have hu1 : S1.regs.get? .janus_undef = some u := by
          rw [← hS1, get?_setGpr_of_not _ _ hn2 rfl, get?_setGpr_of_not s _ hn0 rfl]; exact hu
        have hl1 : S1.regs.get? .log_register_writes = some false := by
          rw [← hS1, get?_setGpr_of_not _ _ hn2 rfl]; exact hl0
        have hu1' : ∀ v : BitVec 32, (S1.set .rflags v).regs.get? .janus_undef = some u := fun v => by
          rw [get?_set_ne _ _ (by decide)]; exact hu1
        simp only [run_readReg hr1, run_writeReg, run_readReg (get?_set_same _ _ _), set_set, run_undef_flg (hu1' _),
          run_undef_flg hu1, run_bind]
        refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl1) _ htr, ?_, ?_⟩
        · have hrel2 := hrel1.writeReg p.rex.isSome (n := 2) (by decide) (BitVec.ofNat 64 (D % V.toNat))
          rw [show regLocOf p.rex.isSome 64 2 = .reg 2 from rfl, hS1] at hrel2
          have := hrel2.flagsRip undefFlags (divfl rf u) (flagsRel_div hfr u) (BitVec.ofNat 64 (tr + inc))
          simp only [divJ, show ¬ (64 = 8) by decide, ↓reduceIte, regWrite] at this ⊢
          exact this
        · rw [← hS1]; exact (((hc.setGpr hn0 _).setGpr hn2 _).set (by decide) _).set (by decide) _

end JanusX86.Proofs
