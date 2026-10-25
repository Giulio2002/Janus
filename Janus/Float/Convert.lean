import Janus.Float.Lemmas

/-!
# Conversions, `minimum` and `maximum` as IEEE 754 specifications

Architecture-independent statements of the IEEE 754-2019 operations behind Go's numeric
conversions and its float `min`/`max` builtins, in the style of `Janus.Float.Spec` (built from
the same core as the architecture models, so a theorem stated with them says: the machine
computed exactly the IEEE result), and the facts about them the example proofs use.

* `fromInt f rm i`: `convertFromInt` (§5.4.1), the integer `i` rounded to `f` by `rm`
  (Go's `float64(i)`, `float32(i)` for integer `i`).
* `convertFormat f g rm x`: `convertFormat` (§5.4.2) from `f` to `g`, `none` for a NaN (Go's
  `float32(x)`, `float64(x)` between float types; the NaN delivered differs between
  architectures).
* `minimum`, `maximum`: IEEE 754-2019 §9.6 `minimum`/`maximum`: a NaN if either operand is a NaN,
  and `-0 < +0`, exactly the rules the Go specification gives `min` and `max` on floats.

Truncation toward zero (`int64(x)`, `uint64(x)`) is `truncInt` (`Janus.Float.Spec`).

Lemmas: `fromInt_b64` (the encoding of an integer of magnitude below `2^53`, the same in every
rounding direction), `truncInt_fromInt` (the conversion is exact: truncating gives the integer
back), `round_self64` (rounding the exact value of a finite binary64 number gives its encoding
back), `convertFormat_32_64` (widening is exact and the same in every rounding direction).
-/

namespace Janus.Float

/-- `convertFromInt` (IEEE 754 §5.4.1): the integer `i` rounded to `f` in direction `rm`; `0`
converts to `+0` (§6.3). -/
def fromInt (f : Fmt) (rm : RM) (i : Int) : Nat :=
  if i = 0 then zero f false else (round f rm (decide (i < 0)) i.natAbs 0).bits

/-- `convertFormat` (IEEE 754 §5.4.2) of the `f` encoding `x` to `g`, in direction `rm`: an
infinity or a zero keeps its sign, a finite non-zero value is rounded; `none` for a NaN (the
result is a NaN, which one is not specified, §6.2.3). -/
def convertFormat (f g : Fmt) (rm : RM) (x : Nat) : Option Nat :=
  match classify f x with
  | .qnan | .snan => none
  | .inf => some (inf g (signOf f x))
  | .zero => some (zero g (signOf f x))
  | _ => some (round g rm (signOf f x) (mantOf f x) (ulpExpOf f x)).bits

/-- `minimum(a, b)` (IEEE 754-2019 §9.6): `none` (a NaN) if either operand is a NaN, `-0` for two
zeros of which one is `-0`, otherwise the smaller operand (the second one when they are equal,
which then have the same encoding). -/
def minimum (f : Fmt) (a b : Nat) : Option Nat :=
  if isNaN f a || isNaN f b then none
  else if classify f a = .zero && classify f b = .zero then some (zero f (signOf f a || signOf f b))
  else if Val.lt (valueOf f a) (valueOf f b) then some a else some b

/-- `maximum(a, b)` (IEEE 754-2019 §9.6): `none` (a NaN) if either operand is a NaN, `+0` for two
zeros of which one is `+0`, otherwise the larger operand. -/
def maximum (f : Fmt) (a b : Nat) : Option Nat :=
  if isNaN f a || isNaN f b then none
  else if classify f a = .zero && classify f b = .zero then some (zero f (signOf f a && signOf f b))
  else if Val.lt (valueOf f b) (valueOf f a) then some a else some b

/-! ## binary64 encodings -/

/-- The fields of the normal binary64 encoding with sign `s`, biased exponent `E` and fraction
`fr`. -/
theorem b64_normal_s (s : Bool) (E fr : Nat) (hE1 : 1 ≤ E) (hE2 : E ≤ 2046) (hf : fr < 2 ^ 52) :
    classify binary64 ((if s then 2 ^ 63 else 0) + E * 2 ^ 52 + fr) = .normal ∧
    signOf binary64 ((if s then 2 ^ 63 else 0) + E * 2 ^ 52 + fr) = s ∧
    mantOf binary64 ((if s then 2 ^ 63 else 0) + E * 2 ^ 52 + fr) = 2 ^ 52 + fr ∧
    ulpExpOf binary64 ((if s then 2 ^ 63 else 0) + E * 2 ^ 52 + fr) = (E : Int) - 1075 := by
  generalize hX : (if s then 2 ^ 63 else 0) + E * 2 ^ 52 + fr = X
  have hlo : X % 2 ^ 63 = E * 2 ^ 52 + fr := by
    rw [← hX]; cases s <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> omega
  have hexp : expOf binary64 X = E := by
    unfold expOf; simp only [binary64]
    have : X / 2 ^ 52 % 2 ^ 11 = (X % 2 ^ 63) / 2 ^ 52 := by omega
    rw [this, hlo]; omega
  have hfrac : fracOf binary64 X = fr := by
    unfold fracOf; simp only [binary64]
    have : X % 2 ^ 52 = (X % 2 ^ 63) % 2 ^ 52 := by omega
    rw [this, hlo]; omega
  have hsign : signOf binary64 X = s := by
    have hq : X / 2 ^ 63 = if s then 1 else 0 := by
      rw [← hX]; cases s <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> omega
    simp only [signOf, Fmt.signBit, binary64, show 11 + 52 = 63 from rfl, hq]
    cases s <;> decide
  have hcl : classify binary64 X = .normal := by
    unfold classify; rw [hexp]
    simp only [show E ≠ 0 by omega, show ¬ E = binary64.expMax by simp [Fmt.expMax, binary64]; omega,
      ite_false]
  have hm : mantOf binary64 X = 2 ^ 52 + fr := by
    unfold mantOf; rw [hexp, hfrac, b64_fbits]; simp only [show E ≠ 0 by omega, ite_false]
  have hu : ulpExpOf binary64 X = (E : Int) - 1075 := by
    unfold ulpExpOf; rw [hexp, b64_bias, b64_fbits]; simp only [show E ≠ 0 by omega, ite_false]
    omega
  exact ⟨hcl, hsign, hm, hu⟩

/-! ## Exact rounding -/

theorem roundAt_exact (rm : RM) (neg : Bool) (m : Nat) (e q : Int) (h : q ≤ e) :
    roundAt rm neg m e q = (m * 2 ^ (e - q).toNat, false) := by
  unfold roundAt; simp only [h, ite_true]

/-- Rounding `m·2^e` to binary64 is exact when `m` has at most 53 significant bits and the value
is in the normal range: the encoding with exponent `⌊log₂ m⌋ + e + 1023` and the significand
`m` shifted to 53 bits. -/
theorem round_b64_normal (rm : RM) (neg : Bool) (m : Nat) (e : Int) (hm : 0 < m)
    (hL : Nat.log2 m ≤ 52) (hE1 : -1022 ≤ (Nat.log2 m : Int) + e) (hE2 : (Nat.log2 m : Int) + e ≤ 1023) :
    (round binary64 rm neg m e).bits =
      pack binary64 neg ((Nat.log2 m : Int) + e + 1023).toNat (m * 2 ^ (52 - Nat.log2 m) - 2 ^ 52) ∧
    (round binary64 rm neg m e).inexact = false := by
  have hL1 : 2 ^ Nat.log2 m ≤ m := Nat.log2_self_le (by omega)
  have hL2 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  have hmax : max ((Nat.log2 m : Int) + e) binary64.emin = (Nat.log2 m : Int) + e := by
    rw [b64_emin]; omega
  have hra : roundAt rm neg m e ((Nat.log2 m : Int) + e - (binary64.fbits : Int)) =
      (m * 2 ^ (52 - Nat.log2 m), false) := by
    rw [roundAt_exact rm neg m e _ (by rw [b64_fbits]; omega), b64_fbits]
    congr 3; omega
  simp only [round, roundUnits, biasedExp, hmax, hra]
  generalize Nat.log2 m = L at *
  have hk1 : 2 ^ 52 ≤ m * 2 ^ (52 - L) := by
    calc 2 ^ 52 = 2 ^ L * 2 ^ (52 - L) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ m * 2 ^ (52 - L) := Nat.mul_le_mul_right _ hL1
  have hk2 : m * 2 ^ (52 - L) < 2 ^ 53 := by
    calc m * 2 ^ (52 - L) < 2 ^ (L + 1) * 2 ^ (52 - L) := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
      _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
  generalize m * 2 ^ (52 - L) = k at *
  have e1 : ¬ k = 2 ^ (binary64.fbits + 1) := by rw [b64_fbits]; omega
  have e2 : ¬ k < 2 ^ binary64.fbits := by rw [b64_fbits]; omega
  simp only [e1, e2, ite_false]
  simp only [b64_fbits, b64_bias]
  split
  · rename_i hc; exfalso; simp only [Fmt.expMax, binary64] at hc; omega
  refine ⟨?_, rfl⟩
  simp only
  rw [show k % 2 ^ 52 = k - 2 ^ 52 by omega,
    show (L : Int) + e - ((52 : Nat) : Int) + ((52 : Nat) : Int) + ((1023 : Nat) : Int) = (L : Int) + e + 1023 by omega]
/-- Rounding the subnormal-range value `m·2^-1074` (`m < 2^52`) to binary64 is exact: the
subnormal encoding with fraction `m`. -/
theorem round_b64_sub (rm : RM) (neg : Bool) (m : Nat) (hm : 0 < m) (h : m < 2 ^ 52) :
    (round binary64 rm neg m (-1074)).bits = pack binary64 neg 0 m := by
  have hL : Nat.log2 m < 52 := (Nat.log2_lt (by omega)).2 h
  have hmax : max ((Nat.log2 m : Int) + -1074) binary64.emin = -1022 := by
    rw [b64_emin]; omega
  have hra : roundAt rm neg m (-1074) ((-1022 : Int) - (binary64.fbits : Int)) = (m, false) := by
    rw [roundAt_exact rm neg m _ _ (by rw [b64_fbits]; omega), b64_fbits]
    simp
  simp only [round, roundUnits, biasedExp, hmax, hra]
  have e1 : ¬ m = 2 ^ (binary64.fbits + 1) := by rw [b64_fbits]; omega
  have e2 : m < 2 ^ binary64.fbits := by rw [b64_fbits]; omega
  simp only [e1, e2, ite_false, ite_true]
  split
  · rename_i hc; exfalso; simp only [Fmt.expMax, binary64] at hc; omega
  simp only [b64_fbits]
  rw [Nat.mod_eq_of_lt h]; rfl

/-- The binary64 encoding of a non-zero integer of magnitude `n < 2^53`: exponent
`⌊log₂ n⌋ + 1023`, the significand `n` shifted to 53 bits; the same in every rounding direction
(the conversion is exact). -/
theorem fromInt_b64 (rm : RM) (i : Int) (h0 : i ≠ 0) (h : i.natAbs < 2 ^ 53) :
    fromInt binary64 rm i =
      (if decide (i < 0) then 2 ^ 63 else 0) + (Nat.log2 i.natAbs + 1023) * 2 ^ 52 +
        (i.natAbs * 2 ^ (52 - Nat.log2 i.natAbs) - 2 ^ 52) := by
  unfold fromInt
  simp only [h0, ite_false]
  have hn0 : i.natAbs ≠ 0 := by omega
  have hL : Nat.log2 i.natAbs < 53 := (Nat.log2_lt hn0).2 h
  rw [(round_b64_normal rm _ i.natAbs 0 (by omega) (by omega) (by omega) (by omega)).1]
  simp only [pack, Fmt.signBit, binary64]
  rw [show ((Nat.log2 i.natAbs : Int) + 0 + 1023).toNat = Nat.log2 i.natAbs + 1023 by omega]

/-- `fromInt` to binary64 does not depend on the rounding direction for `|i| < 2^53`. -/
theorem fromInt_b64_rm (rm rm' : RM) (i : Int) (h : i.natAbs < 2 ^ 53) :
    fromInt binary64 rm i = fromInt binary64 rm' i := by
  by_cases h0 : i = 0
  · simp [fromInt, h0]
  · rw [fromInt_b64 rm i h0 h, fromInt_b64 rm' i h0 h]

/-- `truncInt` of a normal encoding. -/
theorem truncInt_normal (f : Fmt) (x : Nat) (hc : classify f x = .normal) :
    truncInt f x = some (roundToInt .rz (signOf f x) (mantOf f x) (ulpExpOf f x)).1 := by
  unfold truncInt; rw [hc]

/-- `truncInt` of the normal binary64 encoding with sign `s`, exponent `E` and fraction `fr`. -/
theorem truncInt_b64_normal (s : Bool) (E fr : Nat) (hE1 : 1 ≤ E) (hE2 : E ≤ 2046) (hf : fr < 2 ^ 52) :
    truncInt binary64 ((if s then 2 ^ 63 else 0) + E * 2 ^ 52 + fr) =
      some (roundToInt .rz s (2 ^ 52 + fr) ((E : Int) - 1075)).1 := by
  obtain ⟨hc, hs, hm, hu⟩ := b64_normal_s s E fr hE1 hE2 hf
  rw [truncInt_normal _ _ hc, hs, hm, hu]
/-- The conversion of an integer of magnitude below `2^53` to binary64 is exact: truncating the
result gives the integer back. -/
theorem truncInt_fromInt (rm : RM) (i : Int) (h : i.natAbs < 2 ^ 53) :
    truncInt binary64 (fromInt binary64 rm i) = some i := by
  by_cases h0 : i = 0
  · subst h0; simp only [fromInt, ite_true]; unfold truncInt
    rw [show classify binary64 (zero binary64 false) = .zero by decide]
  rw [fromInt_b64 rm i h0 h]
  have hi : i = if decide (i < 0) then -(i.natAbs : Int) else (i.natAbs : Int) := by
    by_cases hn : i < 0 <;> simp [hn] <;> omega
  generalize hn : i.natAbs = n at *
  generalize decide (i < 0) = s at hi ⊢
  subst hi
  have hn0 : n ≠ 0 := by intro h'; subst h'; cases s <;> simp at h0
  have hL1 : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn0
  have hL2 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have hL : Nat.log2 n < 53 := (Nat.log2_lt hn0).2 h
  generalize hL' : Nat.log2 n = L at *
  have hk1 : 2 ^ 52 ≤ n * 2 ^ (52 - L) := by
    calc 2 ^ 52 = 2 ^ L * 2 ^ (52 - L) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hL1
  have hk2 : n * 2 ^ (52 - L) < 2 ^ 53 := by
    calc n * 2 ^ (52 - L) < 2 ^ (L + 1) * 2 ^ (52 - L) := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
      _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
  have hdiv : n * 2 ^ (52 - L) / 2 ^ (52 - L) = n := Nat.mul_div_cancel _ (Nat.two_pow_pos _)
  have hmod : n * 2 ^ (52 - L) % 2 ^ (52 - L) = 0 := Nat.mul_mod_left _ _
  generalize hK : n * 2 ^ (52 - L) = k at *
  rw [truncInt_b64_normal s (L + 1023) (k - 2 ^ 52) (by omega) (by omega) (by omega),
    show 2 ^ 52 + (k - 2 ^ 52) = k by omega,
    show ((L + 1023 : Nat) : Int) - 1075 = (L : Int) - 52 by omega]
  simp only [Option.some.injEq]
  unfold roundToInt
  by_cases hL52 : L = 52
  · subst hL52
    have hk : k = n := by rw [← hdiv]; simp
    subst hk
    simp only [show (0 : Int) ≤ ((52 : Nat) : Int) - 52 by omega, ite_true,
      show (((52 : Nat) : Int) - 52).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one]
    cases s <;> simp
  · have hs' : (-((L : Int) - 52)).toNat = 52 - L := by omega
    simp only [show ¬ (0 : Int) ≤ (L : Int) - 52 by omega, ite_false, hs', hdiv, hmod]
    simp only [roundUp, ite_true, Bool.false_eq_true, ite_false]
    cases s <;> simp

/-- Every encoding below `2^64` is `sign : exp : frac`. -/
theorem b64_decomp (x : Nat) (hx : x < 2 ^ 64) :
    x = pack binary64 (signOf binary64 x) (expOf binary64 x) (fracOf binary64 x) := by
  have h63 : signOf binary64 x = decide (x / 2 ^ 63 % 2 = 1) := rfl
  have hE : expOf binary64 x = x / 2 ^ 52 % 2 ^ 11 := rfl
  have hF : fracOf binary64 x = x % 2 ^ 52 := rfl
  simp only [pack, h63, hE, hF, b64_fbits, show binary64.signBit = 2 ^ 63 from rfl]
  by_cases h : x / 2 ^ 63 % 2 = 1 <;> simp only [h, decide_true, decide_false, ite_true, ite_false,
    Bool.false_eq_true] <;> omega

/-- Rounding the exact value of a finite non-zero binary64 encoding gives the encoding back, in
every rounding direction. -/
theorem round_self64 (rm : RM) (x : Nat) (hx : x < 2 ^ 64)
    (h : classify binary64 x = .normal ∨ classify binary64 x = .subnormal) :
    (round binary64 rm (signOf binary64 x) (mantOf binary64 x) (ulpExpOf binary64 x)).bits = x := by
  have hF : fracOf binary64 x < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hEl : expOf binary64 x < 2 ^ 11 := Nat.mod_lt _ (Nat.two_pow_pos _)
  conv => rhs; rw [b64_decomp x hx]
  rcases h with h | h
  · have he0 : expOf binary64 x ≠ 0 := by
      intro h0; unfold classify at h; simp [h0] at h; split at h <;> simp at h
    have hemax : expOf binary64 x ≠ 2047 := by
      intro h1; revert h; unfold classify; rw [h1]
      simp only [show (2047 : Nat) = binary64.expMax from rfl, ite_true]
      split <;> (try split) <;> (try split) <;> simp
    have hm : mantOf binary64 x = 2 ^ 52 + fracOf binary64 x := by
      unfold mantOf; rw [b64_fbits]; simp [he0]
    have hu : ulpExpOf binary64 x = (expOf binary64 x : Int) - 1075 := by
      unfold ulpExpOf; rw [b64_bias, b64_fbits]; simp only [he0, ite_false]; omega
    have hL : Nat.log2 (mantOf binary64 x) = 52 := by
      rw [hm]
      have h1 : Nat.log2 (2 ^ 52 + fracOf binary64 x) < 53 := (Nat.log2_lt (by omega)).2 (by omega)
      have h2 : 52 ≤ Nat.log2 (2 ^ 52 + fracOf binary64 x) := (Nat.le_log2 (by omega)).2 (by omega)
      omega
    rw [(round_b64_normal rm _ _ _ (by rw [hm]; omega) (by omega) (by rw [hL, hu]; omega)
      (by rw [hL, hu]; omega)).1, hL, hu, hm]
    simp only [pack, b64_fbits, show binary64.signBit = 2 ^ 63 from rfl, Nat.sub_self, Nat.pow_zero,
      Nat.mul_one]
    split <;> omega
  · have he0 : expOf binary64 x = 0 := by
      apply Classical.byContradiction; intro he
      unfold classify at h; simp only [he, ite_false] at h
      split at h <;> (try split at h) <;> (try split at h) <;> simp at h
    have hf0 : fracOf binary64 x ≠ 0 := by
      intro hf; unfold classify at h; simp [he0, hf] at h
    have hm : mantOf binary64 x = fracOf binary64 x := by unfold mantOf; simp [he0]
    have hu : ulpExpOf binary64 x = -1074 := by
      unfold ulpExpOf; rw [he0, b64_emin, b64_fbits]; rfl
    rw [hm, hu, round_b64_sub rm _ _ (by omega) hF, he0]


/-- A zero encoding is `zero` of its sign. -/
theorem zero_self64 (x : Nat) (hx : x < 2 ^ 64) (h : classify binary64 x = .zero) :
    zero binary64 (signOf binary64 x) = x := by
  have he : expOf binary64 x = 0 ∧ fracOf binary64 x = 0 := by
    revert h; unfold classify
    by_cases h1 : expOf binary64 x = 0 <;> by_cases h2 : fracOf binary64 x = 0 <;> simp [h1, h2] <;>
      (try split) <;> (try split) <;> simp
  conv => rhs; rw [b64_decomp x hx, he.1, he.2]
  rfl

/-- An infinite encoding is `inf` of its sign. -/
theorem inf_self64 (x : Nat) (hx : x < 2 ^ 64) (h : classify binary64 x = .inf) :
    inf binary64 (signOf binary64 x) = x := by
  have he : expOf binary64 x = binary64.expMax ∧ fracOf binary64 x = 0 := by
    unfold classify at h
    by_cases h1 : expOf binary64 x = 0 <;> by_cases h2 : expOf binary64 x = binary64.expMax <;>
      by_cases h3 : fracOf binary64 x = 0 <;> simp_all
    all_goals (split at h <;> simp at h)
  conv => rhs; rw [b64_decomp x hx, he.1, he.2]
  rfl

/-- The value of a finite non-zero encoding and the zero value: `0 < v` iff the sign is clear. -/
theorem lt_zero_finite (f : Fmt) (x : Nat)
    (h : classify f x = .normal ∨ classify f x = .subnormal) (hm : 0 < mantOf f x) :
    Val.lt (.num 0 0) (valueOf f x) = !signOf f x ∧ Val.lt (valueOf f x) (.num 0 0) = signOf f x := by
  have hv : valueOf f x = .num (if signOf f x then -(mantOf f x : Int) else mantOf f x) (ulpExpOf f x) := by
    unfold valueOf; rcases h with h | h <;> rw [h]
  rw [hv]
  have hp : ∀ k : Nat, (0 : Int) < (mantOf f x : Int) * 2 ^ k := fun k =>
    Int.mul_pos (by omega) (Int.pow_pos (by decide))
  simp only [Val.lt, align, Int.min_comm (0 : Int) (ulpExpOf f x)]
  have := hp ((ulpExpOf f x - min (ulpExpOf f x) 0).toNat)
  cases signOf f x <;> simp [Int.neg_mul] <;> omega

theorem valueOf_inf {f : Fmt} {x : Nat} (h : classify f x = .inf) : valueOf f x = .inf (signOf f x) := by
  unfold valueOf; rw [h]

theorem mant_pos64 (x : Nat) (h : classify binary64 x = .normal ∨ classify binary64 x = .subnormal) :
    0 < mantOf binary64 x := by
  unfold mantOf
  by_cases he : expOf binary64 x = 0
  · have : fracOf binary64 x ≠ 0 := by
      intro hf
      have : classify binary64 x = .zero := by unfold classify; simp only [he, hf, ite_true]
      rcases h with h | h <;> simp_all
    simp only [he, ite_true]; omega
  · simp only [he, ite_false]; have := Nat.two_pow_pos binary64.fbits; omega

/-- The fields of a finite non-zero binary64 encoding. -/
theorem b64_fin_fields (x : Nat)
    (h : classify binary64 x = .normal ∨ classify binary64 x = .subnormal) :
    fracOf binary64 x < 2 ^ 52 ∧ expOf binary64 x < 2047 ∧
    ((1 ≤ expOf binary64 x ∧ mantOf binary64 x = 2 ^ 52 + fracOf binary64 x ∧
        ulpExpOf binary64 x = (expOf binary64 x : Int) - 1075) ∨
     (expOf binary64 x = 0 ∧ 0 < fracOf binary64 x ∧ mantOf binary64 x = fracOf binary64 x ∧
        ulpExpOf binary64 x = -1074)) := by
  have hF : fracOf binary64 x < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hE : expOf binary64 x < 2 ^ 11 := Nat.mod_lt _ (Nat.two_pow_pos _)
  refine ⟨hF, ?_, ?_⟩
  · apply Classical.byContradiction; intro hne
    have h2047 : expOf binary64 x = binary64.expMax := by
      have : binary64.expMax = 2047 := rfl
      omega
    revert h; unfold classify
    simp only [h2047, show binary64.expMax ≠ 0 by decide, ite_false, ite_true]
    split <;> (try split) <;> simp
  · by_cases he : expOf binary64 x = 0
    · right
      have hf0 : fracOf binary64 x ≠ 0 := by
        intro hf; revert h; unfold classify; simp [he, hf]
      refine ⟨he, by omega, by unfold mantOf; simp [he], ?_⟩
      unfold ulpExpOf; rw [he, b64_emin, b64_fbits]; rfl
    · left
      refine ⟨by omega, by unfold mantOf; rw [b64_fbits]; simp [he], ?_⟩
      unfold ulpExpOf; rw [b64_bias, b64_fbits]; simp only [he, ite_false]; omega

/-- Two finite non-zero binary64 encodings neither of whose values is below the other's are the
same encoding. -/
theorem b64_eq_of_not_lt (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hca : classify binary64 a = .normal ∨ classify binary64 a = .subnormal)
    (hcb : classify binary64 b = .normal ∨ classify binary64 b = .subnormal)
    (h1 : Val.lt (valueOf binary64 a) (valueOf binary64 b) = false)
    (h2 : Val.lt (valueOf binary64 b) (valueOf binary64 a) = false) : a = b := by
  have hva : valueOf binary64 a = .num (if signOf binary64 a then -(mantOf binary64 a : Int)
      else mantOf binary64 a) (ulpExpOf binary64 a) := by
    unfold valueOf; rcases hca with hc | hc <;> rw [hc]
  have hvb : valueOf binary64 b = .num (if signOf binary64 b then -(mantOf binary64 b : Int)
      else mantOf binary64 b) (ulpExpOf binary64 b) := by
    unfold valueOf; rcases hcb with hc | hc <;> rw [hc]
  obtain ⟨hFa, hEa, hfa⟩ := b64_fin_fields a hca
  obtain ⟨hFb, hEb, hfb⟩ := b64_fin_fields b hcb
  have hma := mant_pos64 a hca
  have hmb := mant_pos64 b hcb
  rw [hva, hvb] at h1 h2
  simp only [Val.lt, align] at h1 h2
  replace h1 := Int.not_lt.mp (of_decide_eq_false h1)
  replace h2 := Int.not_lt.mp (of_decide_eq_false h2)
  simp only [Int.min_comm (ulpExpOf binary64 b)] at h2
  -- the common scaling
  generalize hm : min (ulpExpOf binary64 a) (ulpExpOf binary64 b) = m at h1 h2
  have hka : (2 : Int) ^ (ulpExpOf binary64 a - m).toNat = ((2 ^ (ulpExpOf binary64 a - m).toNat : Nat) : Int) := by simp
  have hkb : (2 : Int) ^ (ulpExpOf binary64 b - m).toNat = ((2 ^ (ulpExpOf binary64 b - m).toNat : Nat) : Int) := by simp
  rw [hka, hkb] at h1 h2
  have hpa : 0 < 2 ^ (ulpExpOf binary64 a - m).toNat := Nat.two_pow_pos _
  have hpb : 0 < 2 ^ (ulpExpOf binary64 b - m).toNat := Nat.two_pow_pos _
  -- equal magnitudes and signs
  have hA : mantOf binary64 a * 2 ^ (ulpExpOf binary64 a - m).toNat =
      mantOf binary64 b * 2 ^ (ulpExpOf binary64 b - m).toNat ∧ signOf binary64 a = signOf binary64 b := by
    have p1 : 0 < mantOf binary64 a * 2 ^ (ulpExpOf binary64 a - m).toNat := Nat.mul_pos hma hpa
    have p2 : 0 < mantOf binary64 b * 2 ^ (ulpExpOf binary64 b - m).toNat := Nat.mul_pos hmb hpb
    cases hsa : signOf binary64 a <;> cases hsb : signOf binary64 b <;>
      simp only [hsa, hsb, ite_true, ite_false, Bool.false_eq_true, Int.neg_mul, ← Int.natCast_mul] at h1 h2 <;>
      refine ⟨?_, ?_⟩ <;> (try rfl) <;> omega
  obtain ⟨hA, hs⟩ := hA
  -- equal exponents
  have he : ulpExpOf binary64 a = ulpExpOf binary64 b := by
    apply Classical.byContradiction; intro hne
    rcases Int.lt_or_gt_of_ne hne with hl | hl
    · have hma' : (ulpExpOf binary64 a - m).toNat = 0 := by omega
      have hd : 1 ≤ (ulpExpOf binary64 b - m).toNat := by omega
      rw [hma', Nat.pow_zero, Nat.mul_one] at hA
      have : 2 ≤ 2 ^ (ulpExpOf binary64 b - m).toNat := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ _ := Nat.pow_le_pow_right (by decide) hd
      have : 2 * mantOf binary64 b ≤ mantOf binary64 a := by
        rw [hA, Nat.mul_comm]; exact Nat.mul_le_mul_left _ this
      rcases hfa with ⟨_, hma2, hua⟩ | ⟨_, _, hma2, hua⟩ <;>
        rcases hfb with ⟨_, hmb2, hub⟩ | ⟨_, _, hmb2, hub⟩ <;> omega
    · have hmb' : (ulpExpOf binary64 b - m).toNat = 0 := by omega
      have hd : 1 ≤ (ulpExpOf binary64 a - m).toNat := by omega
      rw [hmb', Nat.pow_zero, Nat.mul_one] at hA
      have : 2 ≤ 2 ^ (ulpExpOf binary64 a - m).toNat := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ _ := Nat.pow_le_pow_right (by decide) hd
      have : 2 * mantOf binary64 a ≤ mantOf binary64 b := by
        rw [← hA, Nat.mul_comm]; exact Nat.mul_le_mul_left _ this
      rcases hfa with ⟨_, hma2, hua⟩ | ⟨_, _, hma2, hua⟩ <;>
        rcases hfb with ⟨_, hmb2, hub⟩ | ⟨_, _, hmb2, hub⟩ <;> omega
  have hm' : mantOf binary64 a = mantOf binary64 b := by
    rw [he] at hA; exact Nat.eq_of_mul_eq_mul_right hpb hA
  have hfields : expOf binary64 a = expOf binary64 b ∧ fracOf binary64 a = fracOf binary64 b := by
    rcases hfa with ⟨_, hma2, hua⟩ | ⟨_, _, hma2, hua⟩ <;>
      rcases hfb with ⟨_, hmb2, hub⟩ | ⟨_, _, hmb2, hub⟩ <;> omega
  rw [b64_decomp a ha, b64_decomp b hb, hs, hfields.1, hfields.2]

/-- The sign of a finite non-zero or infinite value against zero. -/
theorem sign_vs_zero64 (x : Nat)
    (h : classify binary64 x = .normal ∨ classify binary64 x = .subnormal ∨ classify binary64 x = .inf) :
    Val.lt (.num 0 0) (valueOf binary64 x) = !signOf binary64 x ∧
    Val.lt (valueOf binary64 x) (.num 0 0) = signOf binary64 x := by
  rcases h with h | h | h
  · exact lt_zero_finite binary64 x (Or.inl h) (mant_pos64 x (Or.inl h))
  · exact lt_zero_finite binary64 x (Or.inr h) (mant_pos64 x (Or.inr h))
  · rw [valueOf_inf h]; cases signOf binary64 x <;> simp [Val.lt]

/-- Two non-NaN binary64 encodings, not both zeros, neither of whose values is below the
other's, are the same encoding. -/
theorem b64_eq_of_not_lt' (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hna : isNaN binary64 a = false) (hnb : isNaN binary64 b = false)
    (hz : ¬ (classify binary64 a = .zero ∧ classify binary64 b = .zero))
    (h1 : Val.lt (valueOf binary64 a) (valueOf binary64 b) = false)
    (h2 : Val.lt (valueOf binary64 b) (valueOf binary64 a) = false) : a = b := by
  cases hca : classify binary64 a <;> cases hcb : classify binary64 b <;>
    simp only [isNaN, hca, hcb] at hna hnb hz <;> simp at hna hnb hz
  all_goals first
    | (have fa : classify binary64 a = .normal ∨ classify binary64 a = .subnormal := by
         first | exact Or.inl hca | exact Or.inr hca
       have fb : classify binary64 b = .normal ∨ classify binary64 b = .subnormal := by
         first | exact Or.inl hcb | exact Or.inr hcb
       exact b64_eq_of_not_lt a b ha hb fa fb h1 h2)
    | (have fb : classify binary64 b = .normal ∨ classify binary64 b = .subnormal ∨
           classify binary64 b = .inf := by
         first | exact Or.inl hcb | exact Or.inr (Or.inl hcb) | exact Or.inr (Or.inr hcb)
       rw [valueOf_of_zero hca, (sign_vs_zero64 b fb).1] at h1
       rw [valueOf_of_zero hca, (sign_vs_zero64 b fb).2] at h2
       simp_all)
    | (have fa : classify binary64 a = .normal ∨ classify binary64 a = .subnormal ∨
           classify binary64 a = .inf := by
         first | exact Or.inl hca | exact Or.inr (Or.inl hca) | exact Or.inr (Or.inr hca)
       rw [valueOf_of_zero hcb, (sign_vs_zero64 a fa).1] at h2
       rw [valueOf_of_zero hcb, (sign_vs_zero64 a fa).2] at h1
       simp_all)
    | (rw [valueOf_inf hca, valueOf_inf hcb] at h1 h2
       rw [← inf_self64 a ha hca, ← inf_self64 b hb hcb]
       cases hsa : signOf binary64 a <;> cases hsb : signOf binary64 b <;> simp_all [Val.lt])
    | (rw [valueOf_inf hcb] at h1 h2
       unfold valueOf at h1 h2; rw [hca] at h1 h2
       cases hsb : signOf binary64 b <;> simp_all [Val.lt])
    | (rw [valueOf_inf hca] at h1 h2
       unfold valueOf at h1 h2; rw [hcb] at h1 h2
       cases hsa : signOf binary64 a <;> simp_all [Val.lt])

/-- No value is below itself. -/
@[simp] theorem Val.lt_irrefl (v : Val) : Val.lt v v = false := by
  cases v with
  | num n e => simp [Val.lt, align]
  | inf s => cases s <;> rfl

/-! ## Negation by the sign bit -/

/-- Flipping the sign bit of a 64-bit encoding. -/
theorem flip64 (x : Nat) (hx : x < 2 ^ 64) :
    x ^^^ 2 ^ 63 = if x < 2 ^ 63 then x + 2 ^ 63 else x - 2 ^ 63 := by
  have hm : (x ^^^ 2 ^ 63) % 2 ^ 63 = x % 2 ^ 63 := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  have hd : (x ^^^ 2 ^ 63) / 2 ^ 63 = x / 2 ^ 63 ^^^ 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self (Nat.two_pow_pos _)]
  have hq : x / 2 ^ 63 = 0 ∨ x / 2 ^ 63 = 1 := by omega
  have := Nat.div_add_mod (x ^^^ 2 ^ 63) (2 ^ 63)
  generalize x ^^^ 2 ^ 63 = y at hm hd this ⊢
  rcases hq with hq | hq
  · rw [hq, show (0 : Nat) ^^^ 1 = 1 by decide] at hd; split <;> omega
  · rw [hq, show (1 : Nat) ^^^ 1 = 0 by decide] at hd; split <;> omega

theorem flip_fields (x : Nat) (hx : x < 2 ^ 64) :
    expOf binary64 (x ^^^ 2 ^ 63) = expOf binary64 x ∧ fracOf binary64 (x ^^^ 2 ^ 63) = fracOf binary64 x ∧
    signOf binary64 (x ^^^ 2 ^ 63) = !signOf binary64 x := by
  rw [flip64 x hx]
  simp only [expOf, fracOf, signOf, b64_fbits, show binary64.ebits = 11 from rfl,
    show binary64.signBit = 2 ^ 63 from rfl]
  refine ⟨by split <;> omega, by split <;> omega, ?_⟩
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  split <;> omega

theorem flip_lt (x : Nat) (hx : x < 2 ^ 64) : x ^^^ 2 ^ 63 < 2 ^ 64 := by
  rw [flip64 x hx]; split <;> omega

theorem flip64_flip (x : Nat) : x ^^^ 2 ^ 63 ^^^ 2 ^ 63 = x := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem classify_flip (x : Nat) (hx : x < 2 ^ 64) :
    classify binary64 (x ^^^ 2 ^ 63) = classify binary64 x := by
  obtain ⟨he, hf, -⟩ := flip_fields x hx
  unfold classify; rw [he, hf]

theorem isNaN_flip (x : Nat) (hx : x < 2 ^ 64) :
    isNaN binary64 (x ^^^ 2 ^ 63) = isNaN binary64 x := by
  unfold isNaN; rw [classify_flip x hx]

/-- The negation of a value. -/
def Val.neg : Val → Val
  | .num n e => .num (-n) e
  | .inf s => .inf (!s)

theorem valueOf_flip (x : Nat) (hx : x < 2 ^ 64) :
    valueOf binary64 (x ^^^ 2 ^ 63) = Val.neg (valueOf binary64 x) := by
  obtain ⟨he, hf, hs⟩ := flip_fields x hx
  have hm : mantOf binary64 (x ^^^ 2 ^ 63) = mantOf binary64 x := by unfold mantOf; rw [he, hf]
  have hu : ulpExpOf binary64 (x ^^^ 2 ^ 63) = ulpExpOf binary64 x := by unfold ulpExpOf; rw [he]
  unfold valueOf; rw [classify_flip x hx, hm, hu, hs]
  cases classify binary64 x <;> simp [Val.neg] <;> cases signOf binary64 x <;> simp

theorem Val.lt_neg (u v : Val) : Val.lt (Val.neg u) (Val.neg v) = Val.lt v u := by
  cases u with
  | num n e =>
    cases v with
    | num n' e' =>
      simp only [Val.neg, Val.lt, align, Int.neg_mul, Int.min_comm e' e]
      apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
    | inf s => cases s <;> rfl
  | inf s => cases v with
    | num n' e' => cases s <;> rfl
    | inf s' => cases s <;> cases s' <;> rfl

theorem zero_flip (s : Bool) : zero binary64 (!s) = zero binary64 s ^^^ 2 ^ 63 := by
  cases s <;> decide

/-- `minimum` of the negations is the negation of `maximum`. -/
theorem minimum_flip (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    minimum binary64 (a ^^^ 2 ^ 63) (b ^^^ 2 ^ 63) = (maximum binary64 a b).map (· ^^^ 2 ^ 63) := by
  unfold minimum maximum
  rw [isNaN_flip a ha, isNaN_flip b hb, classify_flip a ha, classify_flip b hb, valueOf_flip a ha,
    valueOf_flip b hb, Val.lt_neg, (flip_fields a ha).2.2, (flip_fields b hb).2.2]
  split
  · rfl
  split
  · simp only [Option.map_some, ← zero_flip, Bool.not_and]
  split <;> rfl

/-! ## Rounding in the normal range, and Go's unsigned conversion -/

theorem roundAt_bounds (rm : RM) (neg : Bool) (m : Nat) (e q : Int) (h : e < q) :
    m / 2 ^ (q - e).toNat ≤ (roundAt rm neg m e q).1 ∧
    (roundAt rm neg m e q).1 ≤ m / 2 ^ (q - e).toNat + 1 := by
  unfold roundAt
  simp only [show ¬ q ≤ e by omega, ite_false]
  split <;> omega

/-- The bits of a binary64 rounding in the normal range, when the value has more than 53
significant bits (`log₂ m > 52`, so the rounding position is above the last bit of `m`). -/
theorem round_b64_bits (rm : RM) (neg : Bool) (m : Nat) (e : Int) (hm : 0 < m)
    (hL : 52 < Nat.log2 m) (hE1 : -1022 ≤ (Nat.log2 m : Int) + e) (hE2 : (Nat.log2 m : Int) + e ≤ 1000) :
    (round binary64 rm neg m e).bits =
      let q : Int := (Nat.log2 m : Int) + e - 52
      let k := (roundAt rm neg m e q).1
      if k = 2 ^ 53 then pack binary64 neg (q + 1 + 1075).toNat 0
      else pack binary64 neg (q + 1075).toNat (k - 2 ^ 52) := by
  have hL1 : 2 ^ Nat.log2 m ≤ m := Nat.log2_self_le (by omega)
  have hL2 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  have hmax : max ((Nat.log2 m : Int) + e) binary64.emin = (Nat.log2 m : Int) + e := by
    rw [b64_emin]; omega
  simp only [round, roundUnits, biasedExp, hmax, b64_fbits]
  simp only [show ((52 : Nat) : Int) = 52 from rfl]
  have hs : ((Nat.log2 m : Int) + e - 52 - e).toNat = Nat.log2 m - 52 := by omega
  obtain ⟨hk1, hk2⟩ := roundAt_bounds rm neg m e ((Nat.log2 m : Int) + e - 52) (by omega)
  rw [hs] at hk1 hk2
  have hlo : 2 ^ 52 ≤ m / 2 ^ (Nat.log2 m - 52) := by
    apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2
    calc 2 ^ 52 * 2 ^ (Nat.log2 m - 52) = 2 ^ Nat.log2 m := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ m := hL1
  have hhi : m / 2 ^ (Nat.log2 m - 52) < 2 ^ 53 := by
    apply Nat.div_lt_of_lt_mul
    calc m < 2 ^ (Nat.log2 m + 1) := hL2
      _ = 2 ^ (Nat.log2 m - 52) * 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
  generalize (roundAt rm neg m e ((Nat.log2 m : Int) + e - 52)).1 = k at hk1 hk2 ⊢
  simp only [b64_bias, show binary64.expMax = 2047 from rfl, show (2 : Nat) ^ (52 + 1) = 2 ^ 53 from rfl]
  by_cases hk : k = 2 ^ 53
  · subst hk
    simp only [ite_true, show ¬ (2 : Nat) ^ 53 / 2 < 2 ^ 52 by decide, ite_false]
    rw [ite_eq_right_iff.mpr (fun hc => absurd hc (by omega))]
    simp only
    congr 1
    omega
  · simp only [hk, ite_false, show ¬ k < 2 ^ 52 by omega]
    rw [ite_eq_right_iff.mpr (fun hc => absurd hc (by omega))]
    simp only
    rw [show ((Nat.log2 m : Int) + e - 52 + 52 + ((1023 : Nat) : Int)).toNat =
      ((Nat.log2 m : Int) + e - 52 + 1075).toNat by omega, show k % 2 ^ 52 = k - 2 ^ 52 by omega]

theorem log2_eq (n L : Nat) (h1 : 2 ^ L ≤ n) (h2 : n < 2 ^ (L + 1)) : Nat.log2 n = L := by
  have hn : n ≠ 0 := by have := Nat.two_pow_pos L; omega
  have a := (Nat.le_log2 hn).2 h1
  have b := (Nat.log2_lt hn).2 h2
  omega

/-- `n ||| b` for a bit `b`. -/
theorem or_bit (n b : Nat) (hb : b < 2) : n ||| b = 2 * (n / 2) + (n % 2 ||| b) := by
  have hd : (n ||| b) / 2 = n / 2 := by
    have := @Nat.or_div_two_pow n b 1
    simp only [Nat.pow_one] at this; rw [this, Nat.div_eq_of_lt hb, Nat.or_zero]
  have hm : (n ||| b) % 2 = n % 2 ||| b := by
    have := @Nat.or_mod_two_pow n b 1
    simp only [Nat.pow_one] at this; rw [this, Nat.mod_eq_of_lt hb]
  have := Nat.div_add_mod (n ||| b) 2
  omega

/-- The sticky halving of Go's `uint64 → float64` on amd64 keeps the rounding of a value in
`[2^63, 2^64)`: rounding `y = x/2 | x%2` at the unit `2^10` decides like rounding `x` at `2^11`. -/
theorem roundAt_sticky (rm : RM) (x : Nat) :
    (roundAt rm false x 0 11).1 = (roundAt rm false (x / 2 ||| x % 2) 0 10).1 := by
  have hb : x % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [or_bit _ _ hb]
  have hc : x / 2 % 2 ||| x % 2 = if x / 2 % 2 = 0 ∧ x % 2 = 0 then 0 else 1 := by
    have h1 : x / 2 % 2 = 0 ∨ x / 2 % 2 = 1 := by omega
    have h2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]
  rw [hc]
  unfold roundAt roundUp
  simp only [show ¬ (11 : Int) ≤ 0 by decide, show ¬ (10 : Int) ≤ 0 by decide, ite_false,
    show ((11 : Int) - 0).toNat = 11 from rfl, show ((10 : Int) - 0).toNat = 10 from rfl]
  generalize hy : 2 * (x / 2 / 2) + (if x / 2 % 2 = 0 ∧ x % 2 = 0 then 0 else 1) = y
  have hq : y / 2 ^ 10 = x / 2 ^ 11 := by split at hy <;> omega
  rw [hq]
  have e1 : (x % 2 ^ 11 = 0) ↔ (y % 2 ^ 10 = 0) := by split at hy <;> omega
  have e2 : (2 * (x % 2 ^ 11) > 2 ^ 11) ↔ (2 * (y % 2 ^ 10) > 2 ^ 10) := by split at hy <;> omega
  have e3 : (2 * (x % 2 ^ 11) = 2 ^ 11) ↔ (2 * (y % 2 ^ 10) = 2 ^ 10) := by split at hy <;> omega
  have e4 : (2 * (x % 2 ^ 11) ≥ 2 ^ 11) ↔ (2 * (y % 2 ^ 10) ≥ 2 ^ 10) := by split at hy <;> omega
  cases rm <;> simp only [e1] <;> split <;> simp_all

/-- `fromInt` of a positive integer in binary64's normal range with more than 53 bits. -/
theorem fromInt_b64_big (rm : RM) (n L : Nat) (hL1 : 2 ^ L ≤ n) (hL2 : n < 2 ^ (L + 1)) (h52 : 52 < L)
    (h1000 : L ≤ 1000) :
    fromInt binary64 rm (n : Int) =
      if (roundAt rm false n 0 ((L : Int) - 52)).1 = 2 ^ 53 then pack binary64 false (L + 1 + 1023) 0
      else pack binary64 false (L + 1023) ((roundAt rm false n 0 ((L : Int) - 52)).1 - 2 ^ 52) := by
  have hn : n ≠ 0 := by have := Nat.two_pow_pos L; omega
  have hlog := log2_eq n L hL1 hL2
  unfold fromInt
  rw [if_neg (by omega), show decide ((n : Int) < 0) = false by simp, Int.natAbs_natCast,
    round_b64_bits _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
  simp only [hlog, Int.add_zero]
  rw [show ((L : Int) - 52 + 1 + 1075).toNat = L + 1 + 1023 by omega,
    show ((L : Int) - 52 + 1075).toNat = L + 1023 by omega]

/-- `fromInt` is an encoding of the format. -/
theorem fromInt_lt (f : Fmt) (rm : RM) (i : Int) : fromInt f rm i < 2 ^ f.width := by
  unfold fromInt; split
  · exact zero_lt f false
  · exact round_bits_lt f rm _ _ _

/-- The integer a 64-bit register denotes as `int64`, in the form of `SCVTF`/`CVTSI2SD`. -/
theorem signed64_toInt (x : BitVec 64) :
    (if x.toNat < 2 ^ 63 then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 64) = x.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]; have := x.isLt; split <;> split <;> omega

/-- The significand and exponent of a finite non-zero binary32 encoding. -/
theorem b32_fin_fields (x : Nat)
    (h : classify binary32 x = .normal ∨ classify binary32 x = .subnormal) :
    0 < mantOf binary32 x ∧ mantOf binary32 x < 2 ^ 24 ∧ -149 ≤ ulpExpOf binary32 x ∧
    ulpExpOf binary32 x ≤ 104 := by
  have hF : fracOf binary32 x < 2 ^ 23 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hE : expOf binary32 x < 2 ^ 8 := Nat.mod_lt _ (Nat.two_pow_pos _)
  by_cases he : expOf binary32 x = 0
  · have hf0 : fracOf binary32 x ≠ 0 := by
      intro hf; revert h; unfold classify; simp [he, hf]
    have hm : mantOf binary32 x = fracOf binary32 x := by unfold mantOf; simp [he]
    have hu : ulpExpOf binary32 x = -149 := by
      unfold ulpExpOf; rw [he]; rfl
    rw [hm, hu]; omega
  · have hemax : expOf binary32 x ≠ 255 := by
      intro h1; revert h; unfold classify
      simp only [h1, show (255 : Nat) = binary32.expMax from rfl, ite_true, show binary32.expMax ≠ 0 by decide,
        ite_false]
      split <;> (try split) <;> (try split) <;> simp
    have hm : mantOf binary32 x = 2 ^ 23 + fracOf binary32 x := by
      unfold mantOf; simp only [he, ite_false]; rfl
    have hu : ulpExpOf binary32 x = (expOf binary32 x : Int) - 150 := by
      unfold ulpExpOf; simp only [he, ite_false]
      show (expOf binary32 x : Int) - (127 : Nat) - (23 : Nat) = _; omega
    refine ⟨by omega, by omega, by omega, by omega⟩

/-- Widening binary32 to binary64 is exact (no rounding error) and does not depend on the
rounding direction. -/
theorem convertFormat_32_64 (rm : RM) (x : Nat) :
    convertFormat binary32 binary64 rm x = convertFormat binary32 binary64 .rne x ∧
    ((classify binary32 x = .normal ∨ classify binary32 x = .subnormal) →
      (round binary64 rm (signOf binary32 x) (mantOf binary32 x) (ulpExpOf binary32 x)).inexact = false) := by
  have key : (classify binary32 x = .normal ∨ classify binary32 x = .subnormal) → ∀ rm',
      (round binary64 rm' (signOf binary32 x) (mantOf binary32 x) (ulpExpOf binary32 x)).bits =
        pack binary64 (signOf binary32 x)
          ((Nat.log2 (mantOf binary32 x) : Int) + ulpExpOf binary32 x + 1023).toNat
          (mantOf binary32 x * 2 ^ (52 - Nat.log2 (mantOf binary32 x)) - 2 ^ 52) ∧
      (round binary64 rm' (signOf binary32 x) (mantOf binary32 x) (ulpExpOf binary32 x)).inexact = false := by
    intro hc rm'
    obtain ⟨h0, h1, h2, h3⟩ := b32_fin_fields x hc
    have hL : Nat.log2 (mantOf binary32 x) < 24 := (Nat.log2_lt (by omega)).2 h1
    exact round_b64_normal rm' _ _ _ h0 (by omega) (by omega) (by omega)
  refine ⟨?_, fun hc => (key hc rm).2⟩
  unfold convertFormat
  cases hc : classify binary32 x <;> simp only
  · rw [(key (Or.inr hc) rm).1, (key (Or.inr hc) .rne).1]
  · rw [(key (Or.inl hc) rm).1, (key (Or.inl hc) .rne).1]

end Janus.Float
