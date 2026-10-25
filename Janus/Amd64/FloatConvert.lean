import Janus.Float.Convert
import Janus.Amd64.FloatLemmas

/-!
# SSE conversions and `MINSD` in IEEE mode (proved, not trusted)

With `MXCSR.DAZ = MXCSR.FTZ = 0` (`IEEEMode`): `CVTSI2SD`/`CVTSI2SS` compute `fromInt`,
`CVTSD2SS`/`CVTSS2SD` compute `convertFormat`, `CVTTSD2SI` gives the truncation in range and the
integer indefinite `2^63` otherwise, and `MINSD` is characterised in terms of the IEEE values
(`minmax_min_ieee`), from which the examples derive the IEEE 754-2019 `minimum`/`maximum` that
Go's compiled `min`/`max` sequences compute (`Janus.Float.Convert`).
-/

set_option linter.unusedSimpArgs false

namespace Janus.Amd64.FP

open Janus.Float

variable {c : Ctl}

/-- `CVTSI2SD`/`CVTSI2SS` of the `iw`-bit integer `x` in IEEE mode: the integer it denotes,
rounded by `MXCSR.RC`. -/
theorem ofInt_ieee (h : IEEEMode c) (f : Fmt) (iw x : Nat) :
    (ofInt f c iw x).res =
      fromInt f c.rc (if x < 2 ^ (iw - 1) then (x : Int) else (x : Int) - 2 ^ iw) := by
  unfold ofInt fromInt
  simp only
  split <;> (split <;> simp [check, roundX_ieee h])

/-- A NaN converted between the standard formats is a NaN. -/
theorem convertNaN_isNaN (f g : Fmt) (hg : g.Std) (x : Nat) :
    isNaN g (convertNaN f g x) = true ∧ convertNaN f g x < 2 ^ g.width := by
  have hq : 0 < f.quietBit := Nat.two_pow_pos _
  have h51 : (x % f.quietBit) * 2 ^ 51 / f.quietBit < 2 ^ 51 :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hq) (Nat.two_pow_pos _))
  unfold convertNaN
  generalize (x % f.quietBit) * 2 ^ 51 / f.quietBit = t at *
  rw [isNaN_iff g hg.ebits]
  rcases hg with rfl | rfl
  · have ht : t * 2 ^ 22 / 2 ^ 51 < 2 ^ 22 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by omega)
    generalize t * 2 ^ 22 / 2 ^ 51 = u at *
    simp only [pack, expOf, fracOf, Fmt.signBit, Fmt.expMax, Fmt.quietBit, Fmt.width, binary32]
    cases signOf f x <;> simp <;> omega
  · have ht : t * 2 ^ 51 / 2 ^ 51 < 2 ^ 51 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by omega)
    generalize t * 2 ^ 51 / 2 ^ 51 = u at *
    simp only [pack, expOf, fracOf, Fmt.signBit, Fmt.expMax, Fmt.quietBit, Fmt.width, binary64]
    cases signOf f x <;> simp <;> omega

theorem natAbs_signed (s : Bool) (m : Nat) : (if s = true then -(m : Int) else m).natAbs = m := by
  cases s <;> simp

/-- `CVTSD2SS`/`CVTSS2SD` in IEEE mode: an encoding of `g`, the IEEE `convertFormat` result in
direction `MXCSR.RC` when that is not a NaN, else a NaN. -/
theorem convert_ieee (h : IEEEMode c) (f g : Fmt) (hg : g.Std) (x : Nat) :
    (convert f g c x).res < 2 ^ g.width ∧
    ResultIs g (convertFormat f g c.rc x) (convert f g c x).res := by
  have hn := convertNaN_isNaN f g hg x
  have hN : isNaN f x = decide (classify f x = .qnan ∨ classify f x = .snan) := by
    unfold isNaN; cases classify f x <;> rfl
  have hV : ∀ k, classify f x = k → k = .normal ∨ k = .subnormal →
      (valueOf f x).mag = (mantOf f x, ulpExpOf f x) := by
    intro k hk hk'; unfold valueOf; rw [hk]; rcases hk' with rfl | rfl <;> simp [Val.mag, natAbs_signed]
  simp only [convert, kindOf_ieee h, valOf_ieee h, convertFormat, ResultIs, hN]
  cases hc : classify f x <;>
    simp [check, roundX_ieee h, zero_lt, inf_lt, round_bits_lt, hV _ hc]
  all_goals exact ⟨hn.2, hn.1⟩

/-- `CVTTSD2SI r64, xmm` in IEEE mode: the truncation when it is a 64-bit signed integer (two's
complement), and otherwise (out of range, an infinity or a NaN) the integer indefinite
`2^63 = 0x8000000000000000`. -/
theorem toInt_rz64 (h : IEEEMode c) (x : Nat) :
    (∀ i, truncInt binary64 x = some i → -(2 ^ 63 : Int) ≤ i → i < 2 ^ 63 →
      (toInt binary64 c .rz 64 x).res = (i % (2 ^ 64 : Int)).toNat) ∧
    (∀ i, truncInt binary64 x = some i → (i < -(2 ^ 63 : Int) ∨ 2 ^ 63 ≤ i) →
      (toInt binary64 c .rz 64 x).res = 2 ^ 63) ∧
    (truncInt binary64 x = none → (toInt binary64 c .rz 64 x).res = 2 ^ 63) := by
  unfold toInt truncInt
  simp only [valOf_ieee h]
  unfold valueOf isNaN
  cases hc : classify binary64 x <;> simp [check, natAbs_signed]
  all_goals first
    | (refine ⟨?_, ?_⟩ <;> intro i hi <;> subst hi <;> intros <;> simp_all <;> omega)
    | skip
  all_goals
    have hm := mant_pos64 x (by simp [hc])
    have hz : (if signOf binary64 x = true then -(mantOf binary64 x : Int) else mantOf binary64 x) ≠ 0 := by
      cases signOf binary64 x <;> simp <;> omega
    simp only [hz, ite_false]
    generalize roundToInt _ _ _ _ = r
    constructor <;> intros <;> split <;> simp_all <;> omega

/-- The or of a NaN encoding with any encoding is a NaN. -/
theorem isNaN_or64 (a b : Nat) (ha : isNaN binary64 a = true) :
    isNaN binary64 (a ||| b) = true := by
  rw [isNaN_iff binary64 (by decide)] at *
  obtain ⟨he, hf⟩ := ha
  have hmax : binary64.expMax = 2047 := rfl
  rw [hmax] at he ⊢
  simp only [expOf, fracOf, b64_fbits, show binary64.ebits = 11 from rfl] at *
  rw [Nat.or_div_two_pow, Nat.or_mod_two_pow, Nat.or_mod_two_pow]
  refine ⟨?_, ?_⟩
  · have h1 : 2047 ≤ a / 2 ^ 52 % 2 ^ 11 ||| b / 2 ^ 52 % 2 ^ 11 := by rw [he]; exact Nat.left_le_or
    have h2 : a / 2 ^ 52 % 2 ^ 11 ||| b / 2 ^ 52 % 2 ^ 11 < 2 ^ 11 :=
      Nat.or_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _))
    omega
  · have : a % 2 ^ 52 ≤ a % 2 ^ 52 ||| b % 2 ^ 52 := Nat.left_le_or
    omega

theorem or_lt64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a ||| b < 2 ^ 64 :=
  Nat.or_lt_two_pow ha hb

/-- `MINSD dst, src` (`minmax false binary64 c dst src`) in IEEE mode, on the IEEE values: `src`
when either operand is a NaN or both are zeros, `dst` when its value is below `src`'s, else
`src`. -/
theorem minmax_min_ieee (h : IEEEMode c) (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (minmax false binary64 c a b).res =
      if isNaN binary64 a || isNaN binary64 b then b
      else if classify binary64 a = .zero ∧ classify binary64 b = .zero then b
      else if Val.lt (valueOf binary64 a) (valueOf binary64 b) then a else b := by
  have hd : ∀ x, x < 2 ^ 64 → dazBits binary64 c x = x := by
    intro x hx; unfold dazBits; rw [kindOf_ieee h]
    split
    · rename_i hz; exact zero_self64 x hx hz
    · rfl
  unfold minmax
  simp only [hd a ha, hd b hb, kindOf_ieee h, valOf_ieee h, check, Bool.false_eq_true, ite_false]
  split <;> simp_all

/-- Go's `min(a, b float64)` on amd64 (`MOVUPS X0, X2; MINSD X1, X2; MOVUPS X2, X1; MINSD X0, X2;
POR X1, X2`): with `t = MINSD(a, b)` and `u = MINSD(t, a)`, `u | t` is IEEE `minimum(a, b)`. -/
theorem minsd_seq (h : IEEEMode c) (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((minmax false binary64 c (minmax false binary64 c a b).res a).res |||
        (minmax false binary64 c a b).res) < 2 ^ 64 ∧
    ResultIs binary64 (minimum binary64 a b)
      ((minmax false binary64 c (minmax false binary64 c a b).res a).res |||
        (minmax false binary64 c a b).res) := by
  have ht := minmax_min_ieee h a b ha hb
  have htl : (minmax false binary64 c a b).res < 2 ^ 64 := by rw [ht]; split <;> (try split) <;> (try split) <;> omega
  rw [minmax_min_ieee h _ a htl ha, ht]
  refine ⟨?_, ?_⟩
  · split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
      exact or_lt64 _ _ (by omega) (by omega)
  unfold minimum ResultIs
  by_cases hna : isNaN binary64 a = true
  · simp only [hna, Bool.true_or, Bool.or_true, ite_true]
    exact isNaN_or64 a b hna
  by_cases hnb : isNaN binary64 b = true
  · simp only [hnb, Bool.or_true, ite_true]
    rw [Nat.or_comm]; exact isNaN_or64 b a hnb
  simp only [Bool.not_eq_true] at hna hnb
  simp only [hna, hnb, Bool.or_false, Bool.false_eq_true, ite_false]
  by_cases hz : classify binary64 a = .zero ∧ classify binary64 b = .zero
  · simp only [hz.1, hz.2, and_self, ite_true, decide_true, Bool.and_self, hna, hnb, Bool.or_false,
      Bool.false_eq_true, ite_false]
    have ea := zero_self64 a ha hz.1
    have eb := zero_self64 b hb hz.2
    generalize signOf binary64 a = sa at ea ⊢
    generalize signOf binary64 b = sb at eb ⊢
    subst ea eb
    cases sa <;> cases sb <;> decide
  have hz' : (decide (classify binary64 a = .zero) && decide (classify binary64 b = .zero)) = false := by
    by_cases e1 : classify binary64 a = .zero <;> by_cases e2 : classify binary64 b = .zero <;> simp_all
  simp only [hz, hz', hna, hnb, Bool.or_false, Bool.false_eq_true, ite_false]
  by_cases hlt : Val.lt (valueOf binary64 a) (valueOf binary64 b) = true
  · simp only [hlt, ite_true, Val.lt_irrefl, Bool.false_eq_true, ite_false, Nat.or_self, hna,
      Bool.or_false]
    split <;> simp
  · simp only [Bool.not_eq_true] at hlt
    simp only [hlt, Bool.false_eq_true, ite_false]
    by_cases hlt2 : Val.lt (valueOf binary64 b) (valueOf binary64 a) = true
    · simp only [hlt2, ite_true, Nat.or_self, hna, hnb, Bool.or_false, Bool.false_eq_true, ite_false]
      split
      · rename_i hc; exact absurd ⟨hc.2, hc.1⟩ hz
      · simp
    · simp only [Bool.not_eq_true] at hlt2
      have := b64_eq_of_not_lt' a b ha hb hna hnb hz hlt hlt2
      subst this
      simp

/-- Go's `max(a, b float64)` on amd64: the `min` sequence on the negations (`PXOR` with the sign
bit), negated again: IEEE `maximum(a, b)`. -/
theorem maxsd_seq (h : IEEEMode c) (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (((minmax false binary64 c (minmax false binary64 c (a ^^^ 2 ^ 63) (b ^^^ 2 ^ 63)).res
        (a ^^^ 2 ^ 63)).res ||| (minmax false binary64 c (a ^^^ 2 ^ 63) (b ^^^ 2 ^ 63)).res) ^^^ 2 ^ 63)
        < 2 ^ 64 ∧
    ResultIs binary64 (maximum binary64 a b)
      (((minmax false binary64 c (minmax false binary64 c (a ^^^ 2 ^ 63) (b ^^^ 2 ^ 63)).res
        (a ^^^ 2 ^ 63)).res ||| (minmax false binary64 c (a ^^^ 2 ^ 63) (b ^^^ 2 ^ 63)).res) ^^^ 2 ^ 63) := by
  obtain ⟨hl, hr⟩ := minsd_seq h _ _ (flip_lt a ha) (flip_lt b hb)
  rw [minimum_flip a b ha hb] at hr
  generalize ((minmax false binary64 c (minmax false binary64 c (a ^^^ 2 ^ 63) (b ^^^ 2 ^ 63)).res
        (a ^^^ 2 ^ 63)).res ||| (minmax false binary64 c (a ^^^ 2 ^ 63) (b ^^^ 2 ^ 63)).res) = r at hl hr ⊢
  refine ⟨flip_lt r hl, ?_⟩
  unfold ResultIs at hr ⊢
  cases hm : maximum binary64 a b with
  | none => rw [hm] at hr; simp only [Option.map_none] at hr; rw [isNaN_flip r hl]; exact hr
  | some m => rw [hm] at hr; simp only [Option.map_some] at hr; rw [hr, flip64_flip]

/-- `ADDSD x, x` of a positive normal `x` in IEEE mode: `2·x` rounded. -/
theorem binop_add_self_gen (h : IEEEMode c) (f : Fmt) (a : Nat) (hcl : classify f a = .normal)
    (hs : signOf f a = false) (hm : 0 < mantOf f a) :
    (binop .add f c a a).res = (round f c.rc false (2 * mantOf f a) (ulpExpOf f a)).bits := by
  have hn : isNaN f a = false := not_isNaN_of_classify hcl (by simp)
  have hv : valueOf f a = .num (mantOf f a) (ulpExpOf f a) := by
    rw [valueOf_normal hcl, hs]; rfl
  unfold binop
  simp only [kindOf_ieee h, valOf_ieee h, hcl, hs, hn, hv, Bool.or_false, Bool.false_eq_true,
    ite_false, Val.n, Val.e, reduceCtorEq, decide_false, Bool.and_false, Bool.false_and]
  have hx : addExact (mantOf f a : Int) (ulpExpOf f a) (mantOf f a : Int) (ulpExpOf f a) =
      some (false, 2 * mantOf f a, ulpExpOf f a) := by
    simp only [addExact, align, Int.min_self, Int.sub_self, Int.toNat_zero, Int.pow_zero,
      Int.mul_one, Janus.Float.ofInt]
    rw [if_neg (by omega)]
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨by simp; omega, by omega, trivial⟩
  rw [hx]
  simp only [roundX_ieee h]

/-- `ADDSD x, x` of a positive normal binary64 `x` far from overflow: the exponent goes up by one. -/
theorem binop_add_self (h : IEEEMode c) (E F : Nat) (hE1 : 1 ≤ E) (hE2 : E ≤ 2000) (hF : F < 2 ^ 52) :
    (binop .add binary64 c (E * 2 ^ 52 + F) (E * 2 ^ 52 + F)).res = (E + 1) * 2 ^ 52 + F := by
  obtain ⟨hcl, hs, -, hm, hu⟩ := b64_normal E F hE1 (by omega) hF
  rw [binop_add_self_gen h binary64 _ hcl hs (by rw [hm]; omega), hm, hu]
  have hL : Nat.log2 (2 * (2 ^ 52 + F)) = 53 := log2_eq _ _ (by omega) (by omega)
  rw [round_b64_bits _ _ _ _ (by omega) (by omega) (by rw [hL]; omega) (by rw [hL]; omega)]
  simp only [hL]
  have hk : (roundAt c.rc false (2 * (2 ^ 52 + F)) ((E : Int) - 1075) ((53 : Nat) + ((E : Int) - 1075) - 52)).1
      = 2 ^ 52 + F := by
    unfold roundAt
    simp only [show ¬ ((53 : Nat) + ((E : Int) - 1075) - 52 ≤ (E : Int) - 1075) by omega, ite_false,
      show ((53 : Nat) + ((E : Int) - 1075) - 52 - ((E : Int) - 1075)).toNat = 1 by omega, Nat.pow_one]
    rw [show 2 * (2 ^ 52 + F) % 2 = 0 by omega, show 2 * (2 ^ 52 + F) / 2 = 2 ^ 52 + F by omega]
    simp [roundUp]
  rw [hk, if_neg (by omega)]
  simp only [pack, Bool.false_eq_true, ite_false, b64_fbits, Nat.zero_add]
  rw [show ((53 : Nat) + ((E : Int) - 1075) - 52 + 1075).toNat = E + 1 by omega]
  omega

/-- Go's `float64(x)` for `x ≥ 2^63` on amd64: `CVTSI2SDQ` of the sticky half `x/2 | x%2`, then
`ADDSD` of the result to itself, is `fromInt x` (in every rounding direction). -/
theorem u64_big (h : IEEEMode c) (x : Nat) (h1 : 2 ^ 63 ≤ x) (h2 : x < 2 ^ 64) :
    (binop .add binary64 c (fromInt binary64 c.rc ((x / 2 ||| x % 2 : Nat) : Int))
      (fromInt binary64 c.rc ((x / 2 ||| x % 2 : Nat) : Int))).res = fromInt binary64 c.rc (x : Int) := by
  have hy := or_bit (x / 2) (x % 2) (Nat.mod_lt _ (by decide))
  have hb : x / 2 % 2 ||| x % 2 < 2 := Nat.or_lt_two_pow (n := 1) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  rw [fromInt_b64_big c.rc x 63 h1 h2 (by decide) (by decide),
    fromInt_b64_big c.rc _ 62 (by omega) (by omega) (by decide) (by decide)]
  rw [show ((63 : Nat) : Int) - 52 = 11 from rfl, show ((62 : Nat) : Int) - 52 = 10 from rfl,
    roundAt_sticky]
  obtain ⟨hk1, hk2⟩ := roundAt_bounds c.rc false (x / 2 ||| x % 2) 0 10 (by decide)
  simp only [show ((10 : Int) - 0).toNat = 10 from rfl] at hk1 hk2
  generalize (roundAt c.rc false (x / 2 ||| x % 2) 0 10).1 = k at hk1 hk2 ⊢
  have hlo : 2 ^ 52 ≤ (x / 2 ||| x % 2) / 2 ^ 10 := by omega
  have hhi : (x / 2 ||| x % 2) / 2 ^ 10 < 2 ^ 53 := by omega
  simp only [pack, Bool.false_eq_true, ite_false, b64_fbits, Nat.zero_add]
  split
  · rw [binop_add_self h _ _ (by omega) (by omega) (by decide)]
  · rw [binop_add_self h _ _ (by omega) (by omega) (by omega)]

end Janus.Amd64.FP
