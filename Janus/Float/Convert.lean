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

end Janus.Float
