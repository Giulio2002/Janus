import Janus.Float.Spec

/-!
# Facts about the IEEE core (proved, not trusted)

Bounds (every encoding the core produces is below `2^width`), and the NaN facts the
architecture lemmas need. `Fmt.Std f` restricts to the two formats of the model.
-/

namespace Janus.Float

/-- The formats the model uses. -/
def Fmt.Std (f : Fmt) : Prop := f = binary32 ∨ f = binary64

theorem Fmt.Std.ebits {f : Fmt} (h : f.Std) : 1 ≤ f.ebits := by rcases h with rfl | rfl <;> decide
theorem Fmt.Std.fbits {f : Fmt} (h : f.Std) : 1 ≤ f.fbits := by rcases h with rfl | rfl <;> decide

theorem two_pow_width (f : Fmt) : 2 ^ f.width = 2 * f.signBit := by
  unfold Fmt.width Fmt.signBit
  rw [show 1 + f.ebits + f.fbits = (f.ebits + f.fbits) + 1 by omega, Nat.pow_succ]; omega

theorem pack_lt (f : Fmt) (s : Bool) (e fr : Nat) (he : e < 2 ^ f.ebits) (hf : fr < 2 ^ f.fbits) :
    pack f s e fr < 2 ^ f.width := by
  rw [two_pow_width]
  have h1 : e * 2 ^ f.fbits + fr < f.signBit := by
    unfold Fmt.signBit
    have : (e + 1) * 2 ^ f.fbits ≤ 2 ^ f.ebits * 2 ^ f.fbits := Nat.mul_le_mul_right _ he
    rw [Nat.pow_add]; rw [Nat.add_mul, Nat.one_mul] at this; omega
  unfold pack; cases s <;> simp <;> omega

theorem expMax_lt (f : Fmt) : f.expMax < 2 ^ f.ebits := by
  unfold Fmt.expMax; have := Nat.two_pow_pos f.ebits; omega

theorem zero_lt (f : Fmt) (s : Bool) : zero f s < 2 ^ f.width :=
  pack_lt f s 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _)

theorem inf_lt (f : Fmt) (s : Bool) : inf f s < 2 ^ f.width :=
  pack_lt f s _ 0 (expMax_lt f) (Nat.two_pow_pos _)

theorem maxNormal_lt (f : Fmt) (s : Bool) : maxNormal f s < 2 ^ f.width :=
  pack_lt f s _ _ (by have := expMax_lt f; omega) (by have := Nat.two_pow_pos f.fbits; omega)

/-- Every rounded result is an encoding of the format. -/
theorem round_bits_lt (f : Fmt) (rm : RM) (neg : Bool) (m : Nat) (e : Int) :
    (round f rm neg m e).bits < 2 ^ f.width := by
  unfold round
  simp only
  split
  · split <;> simp [inf_lt, maxNormal_lt]
  · rename_i h
    apply pack_lt _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))
    have := expMax_lt f
    omega

theorem isNaN_iff (f : Fmt) (hE : 1 ≤ f.ebits) (x : Nat) :
    isNaN f x = true ↔ expOf f x = f.expMax ∧ fracOf f x ≠ 0 := by
  have : 1 ≤ f.expMax := by
    unfold Fmt.expMax; have := Nat.one_lt_two_pow (n := f.ebits) (by omega); omega
  unfold isNaN classify
  by_cases h1 : expOf f x = 0 <;> by_cases h2 : expOf f x = f.expMax <;>
    by_cases h3 : fracOf f x = 0 <;> by_cases h4 : fracOf f x / f.quietBit % 2 = 1 <;>
    simp_all <;> omega

theorem quietBit_lt (f : Fmt) (hf : 1 ≤ f.fbits) : f.quietBit < 2 ^ f.fbits :=
  Nat.pow_lt_pow_right (by omega) (by omega)

/-- Setting the quiet bit of a NaN gives a NaN. -/
theorem isNaN_or_quiet (f : Fmt) (hf : f.Std) (x : Nat) (h : isNaN f x = true) :
    isNaN f (x ||| f.quietBit) = true := by
  rw [isNaN_iff f hf.ebits] at *
  have hq := quietBit_lt f hf.fbits
  have e1 : expOf f (x ||| f.quietBit) = expOf f x := by
    simp only [expOf, Nat.or_div_two_pow, Nat.div_eq_of_lt hq, Nat.or_zero]
  have e2 : f.quietBit ≤ fracOf f (x ||| f.quietBit) := by
    simp only [fracOf, Nat.or_mod_two_pow, Nat.mod_eq_of_lt hq]
    exact Nat.right_le_or
  have : 0 < f.quietBit := Nat.two_pow_pos _
  exact ⟨e1 ▸ h.1, by omega⟩

theorem or_quiet_lt (f : Fmt) (hf : f.Std) (x : Nat) (h : x < 2 ^ f.width) :
    x ||| f.quietBit < 2 ^ f.width :=
  Nat.or_lt_two_pow h (Nat.lt_trans (quietBit_lt f hf.fbits)
    (Nat.pow_lt_pow_right (by omega) (by unfold Fmt.width; omega)))

theorem isNaN_of_classify {f : Fmt} {x : Nat} (h : classify f x = .qnan ∨ classify f x = .snan) :
    isNaN f x = true := by
  unfold isNaN; rcases h with h | h <;> rw [h]

theorem not_isNaN_of_classify {f : Fmt} {x : Nat} {k : Kind} (h : classify f x = k)
    (hk : k ≠ .qnan ∧ k ≠ .snan) : isNaN f x = false := by
  unfold isNaN; rw [h]; cases k <;> simp_all

theorem valueOf_of_zero {f : Fmt} {x : Nat} (h : classify f x = .zero) : valueOf f x = .num 0 0 := by
  unfold valueOf; rw [h]

theorem addExact_zero : addExact 0 0 0 0 = none := by decide

theorem mul_comm (f : Fmt) (rm : RM) (a b : Nat) : mul f rm a b = mul f rm b a := by
  unfold mul
  have hx : mulExact (valueOf f a).n (valueOf f a).e (valueOf f b).n (valueOf f b).e =
      mulExact (valueOf f b).n (valueOf f b).e (valueOf f a).n (valueOf f a).e := by
    simp [mulExact, Int.mul_comm, Int.add_comm]
  rw [hx]
  cases isNaN f a <;> cases isNaN f b <;> cases signOf f a <;> cases signOf f b <;>
    cases classify f a <;> cases classify f b <;> simp

theorem fma_nan (f : Fmt) (rm : RM) (a b c : Nat) (h : isNaN f c = true) : fma f rm a b c = none := by
  simp [fma, h]

theorem add_nan_left (f : Fmt) (rm : RM) (a b : Nat) (h : isNaN f a = true) : add f rm a b = none := by
  simp [add, h]

theorem add_nan_right (f : Fmt) (rm : RM) (a b : Nat) (h : isNaN f b = true) : add f rm a b = none := by
  simp [add, h]

theorem resultIs_bind (f : Fmt) (o : Option Nat) (x y : Nat) (k : Nat → Option Nat)
    (hk : ∀ y, isNaN f y = true → k y = none) (ho : ResultIs f o x) :
    ResultIs f (o.bind k) y ↔ ResultIs f (k x) y := by
  cases o with
  | none => simp [ResultIs] at ho; simp [ResultIs, hk x ho]
  | some r => simp [ResultIs] at ho; subst ho; rfl

/-- `abs` is the encoding with the sign cleared, a value below `2^width` for every input. -/
theorem abs_lt (f : Fmt) (x : Nat) : abs f x < f.signBit := Nat.mod_lt _ (Nat.two_pow_pos _)

/-! ## Exact conversions (for the conversion proofs) -/


theorem b64_emin : binary64.emin = -1022 := by decide
theorem b64_bias : binary64.bias = 1023 := by decide
theorem b64_fbits : binary64.fbits = 52 := rfl

theorem round_exact64 (rm : RM) (f : Nat) (hf0 : 0 < f) (hf : f < 2 ^ 52) :
    (round binary64 rm false f 11).bits =
      (Nat.log2 f + 1034) * 2 ^ 52 + (f * 2 ^ (52 - Nat.log2 f) - 2 ^ 52) := by
  have hL1 : 2 ^ Nat.log2 f ≤ f := Nat.log2_self_le (by omega)
  have hL2 : f < 2 ^ (Nat.log2 f + 1) := Nat.lt_log2_self
  have hL : Nat.log2 f < 52 := (Nat.log2_lt (by omega)).2 hf
  unfold round roundUnits biasedExp roundAt
  simp only [b64_emin]
  generalize Nat.log2 f = L at *
  have hk1 : 2 ^ 52 ≤ f * 2 ^ (52 - L) := by
    calc 2 ^ 52 = 2 ^ L * 2 ^ (52 - L) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ f * 2 ^ (52 - L) := Nat.mul_le_mul_right _ hL1
  have hk2 : f * 2 ^ (52 - L) < 2 ^ 53 := by
    calc f * 2 ^ (52 - L) < 2 ^ (L + 1) * 2 ^ (52 - L) := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
      _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
  have hq : max ((L : Int) + 11) (-1022) - 52 = (L : Int) - 41 := by omega
  have hs : ((11 : Int) - ((L : Int) - 41)).toNat = 52 - L := by omega
  simp [binary64, Fmt.bias, Fmt.expMax, hq, hs, show ((L : Int) - 41 ≤ 11) by omega]
  generalize f * 2 ^ (52 - L) = k at *
  have e1 : (k = 9007199254740992) = False := by simp; omega
  have e2 : (k < 4503599627370496) = False := by simp; omega
  have e3 : ((2047 : Int) ≤ (L : Int) - 41 + 52 + 1023) = False := by simp; omega
  simp only [e1, e2, e3, ite_false, pack, Bool.false_eq_true]
  have e4 : ((L : Int) - 41 + 52 + 1023).toNat = L + 1034 := by omega
  rw [e4]; omega

theorem valueOf_normal {f : Fmt} {x : Nat} (h : classify f x = .normal) :
    valueOf f x = .num (if signOf f x then -(mantOf f x : Int) else mantOf f x) (ulpExpOf f x) := by
  unfold valueOf; rw [h]



theorem cast_lt {a b c d : Nat} (h : (a : Int) * 2 ^ b < (c : Int) * 2 ^ d) : a * 2 ^ b < c * 2 ^ d := by
  have : ((a * 2 ^ b : Nat) : Int) < ((c * 2 ^ d : Nat) : Int) := by push_cast; exact h
  exact_mod_cast this

/-- The truncation of a non-negative `m·2^e` below `2^63` when `m·2^e < 2^52·2^11`. -/
theorem trunc_lt_of_lt (m : Nat) (e : Int)
    (h : (m : Int) * 2 ^ (e - min e 11).toNat < ((2 ^ 52 : Nat) : Int) * 2 ^ ((11 : Int) - min e 11).toNat) :
    (roundToInt .rz false m e).1 < 2 ^ 63 := by
  have h := cast_lt h
  unfold roundToInt
  by_cases he : 0 ≤ e
  · simp only [he, ite_true]
    obtain ⟨k, rfl⟩ : ∃ k : Nat, e = k := ⟨e.toNat, by omega⟩
    simp only [Int.toNat_natCast, Bool.false_eq_true, ite_false, Int.one_mul]
    by_cases hk : 11 ≤ k
    · have h1 : ((k : Int) - min (k : Int) 11).toNat = k - 11 := by omega
      have h2 : ((11 : Int) - min (k : Int) 11).toNat = 0 := by omega
      rw [h1, h2, Nat.pow_zero, Nat.mul_one] at h
      have : m * 2 ^ k = m * 2 ^ (k - 11) * 2 ^ 11 := by
        rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
      have : m * 2 ^ k < 2 ^ 63 := by
        rw [this, show (2:Nat) ^ 63 = 2 ^ 52 * 2 ^ 11 from rfl]
        exact Nat.mul_lt_mul_of_pos_right h (by decide)
      exact_mod_cast this
    · have h1 : ((k : Int) - min (k : Int) 11).toNat = 0 := by omega
      have h2 : ((11 : Int) - min (k : Int) 11).toNat = 11 - k := by omega
      rw [h1, h2, Nat.pow_zero, Nat.mul_one] at h
      have : m * 2 ^ k < 2 ^ 63 := by
        calc m * 2 ^ k < 2 ^ 52 * 2 ^ (11 - k) * 2 ^ k := Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _)
          _ = 2 ^ 63 := by rw [Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      exact_mod_cast this
  · simp only [he, ite_false]
    have h1 : (e - min e 11).toNat = 0 := by omega
    have h2 : ((11 : Int) - min e 11).toNat = 11 + (-e).toNat := by omega
    rw [h1, h2, Nat.pow_zero, Nat.mul_one,
      show (2 : Nat) ^ 52 * 2 ^ (11 + (-e).toNat) = 2 ^ 63 * 2 ^ (-e).toNat by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega] at h
    generalize (-e).toNat = s at *
    have hq : m / 2 ^ s < 2 ^ 63 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 h
    have : (if roundUp RM.rz false (m / 2 ^ s) (m % 2 ^ s) s = true then m / 2 ^ s + 1 else m / 2 ^ s) = m / 2 ^ s := by
      simp [roundUp]
    rw [this]; simp only [Bool.false_eq_true, ite_false, Int.one_mul]
    exact_mod_cast hq


theorem cast_not_lt {a b c d : Nat} (h : ¬ (a : Int) * 2 ^ b < (c : Int) * 2 ^ d) : c * 2 ^ d ≤ a * 2 ^ b := by
  have : ¬ ((a * 2 ^ b : Nat) : Int) < ((c * 2 ^ d : Nat) : Int) := by push_cast; exact h
  omega

theorem e_ge_of_not_lt (m : Nat) (e : Int) (hm : m < 2 ^ 53)
    (h : ¬ (m : Int) * 2 ^ (e - min e 11).toNat < ((2 ^ 52 : Nat) : Int) * 2 ^ ((11 : Int) - min e 11).toNat) :
    11 ≤ e := by
  apply Classical.byContradiction; intro he
  have h1 : (e - min e 11).toNat = 0 := by omega
  have h2 : ((11 : Int) - min e 11).toNat = (11 - e).toNat := by omega
  have h := cast_not_lt h
  rw [h1, h2, Nat.pow_zero, Nat.mul_one] at h
  have : (2 ^ 53 : Nat) ≤ 2 ^ 52 * 2 ^ (11 - e).toNat := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem trunc_ge (m : Nat) (e : Int) (hm : 2 ^ 52 ≤ m) (he : 12 ≤ e) :
    2 ^ 64 ≤ (roundToInt .rz false m e).1 := by
  unfold roundToInt
  simp only [show 0 ≤ e by omega, ite_true, Bool.false_eq_true, ite_false, Int.one_mul]
  have : 2 ^ 64 ≤ m * 2 ^ e.toNat := by
    calc 2 ^ 64 = 2 ^ 52 * 2 ^ 12 := rfl
      _ ≤ m * 2 ^ e.toNat := Nat.mul_le_mul hm (Nat.pow_le_pow_right (by decide) (by omega))
  exact_mod_cast this

/-- The fields of the positive normal binary64 encoding `E·2^52 + f`. -/
theorem b64_normal (E fr : Nat) (hE1 : 1 ≤ E) (hE2 : E ≤ 2046) (hf : fr < 2 ^ 52) :
    classify binary64 (E * 2 ^ 52 + fr) = .normal ∧ signOf binary64 (E * 2 ^ 52 + fr) = false ∧
    valueOf binary64 (E * 2 ^ 52 + fr) = .num ((2 ^ 52 + fr : Nat) : Int) ((E : Int) - 1075) ∧
    mantOf binary64 (E * 2 ^ 52 + fr) = 2 ^ 52 + fr ∧
    ulpExpOf binary64 (E * 2 ^ 52 + fr) = (E : Int) - 1075 := by
  generalize hX : E * 2 ^ 52 + fr = X
  have hlt : X < 2 ^ 63 := by omega
  have hexp : expOf binary64 X = E := by unfold expOf; simp only [binary64]; omega
  have hfrac : fracOf binary64 X = fr := by unfold fracOf; simp only [binary64]; omega
  have hsign : signOf binary64 X = false := by
    have : X / 2 ^ 63 = 0 := Nat.div_eq_of_lt hlt
    simp [signOf, Fmt.signBit, binary64, this]
  have hcl : classify binary64 X = .normal := by
    unfold classify; rw [hexp]
    simp only [show E ≠ 0 by omega, show ¬ E = binary64.expMax by simp [Fmt.expMax, binary64]; omega,
      ite_false]
  have hm : mantOf binary64 X = 2 ^ 52 + fr := by
    unfold mantOf; rw [hexp, hfrac, b64_fbits]; simp only [show E ≠ 0 by omega, ite_false]
  have hu : ulpExpOf binary64 X = (E : Int) - 1075 := by
    unfold ulpExpOf; rw [hexp, b64_bias, b64_fbits]; simp only [show E ≠ 0 by omega, ite_false]
    omega
  refine ⟨hcl, hsign, ?_, hm, hu⟩
  rw [valueOf_normal hcl, hm, hu, hsign]; rfl


end Janus.Float
