import Janus.Float.Convert
import Janus.Arm64.FloatLemmas

/-!
# Arm conversions and `FMIN`/`FMAX` in IEEE mode (proved, not trusted)

With `FPCR.{FIZ, AH, FZ, DN} = 0` (`IEEEMode`): `SCVTF`/`UCVTF` (`FixedToFP`) compute
`fromInt`, `FCVT` between single and double (`FPConvert`) computes `convertFormat`, `FCVTZS`
(`FPToFixed`, signed, toward zero) gives the truncation in range and saturates outside it, and
`FMIN`/`FMAX` (`FPMin`/`FPMax`) compute IEEE 754-2019 `minimum`/`maximum`
(`Janus.Float.Convert`).
-/

set_option linter.unusedSimpArgs false

namespace Janus.Arm64.FP

open Janus.Float

variable {fpcr : Nat}

/-- `SCVTF` (`unsigned = false`) / `UCVTF` of the `M`-bit register value `op` in IEEE mode: the
integer it denotes, rounded by `rm`. -/
theorem fixedToFP_ieee (h : IEEEMode fpcr) (f : Fmt) (unsigned : Bool) (rm : RM) (M op : Nat) :
    (fixedToFP f fpcr unsigned rm M op).1 =
      fromInt f rm (if unsigned || op < 2 ^ (M - 1) then (op : Int) else (op : Int) - 2 ^ M) := by
  unfold fixedToFP fromInt
  simp only
  split <;> (split <;> simp [fpRound_ieee h])

theorem satQ_signed (i : Int) (h0 : -(2 ^ 63 : Int) ≤ i) (h1 : i < 2 ^ 63) :
    (satQ 64 false i).1 = (i % (2 ^ 64 : Int)).toNat := by
  unfold satQ; simp; rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega)), ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]

/-- `FPToFixed(op, 0, FALSE, fpcr, RZ, 64)` (`FCVTZS Xd, Dn`) in IEEE mode on a value whose
truncation is a 64-bit signed integer: that integer (two's complement). -/
theorem fpToFixed_rzs_ieee (h : IEEEMode fpcr) (f : Fmt) (x : Nat) (i : Int)
    (hi : truncInt f x = some i) (h0 : -(2 ^ 63 : Int) ≤ i) (h1 : i < 2 ^ 63) :
    (fpToFixed f fpcr false .rz 64 x).1 = (i % (2 ^ 64 : Int)).toNat := by
  have hah : ah fpcr = false := h.2.1
  simp only [fpToFixed, unpack_ieee h, hah]
  unfold truncInt at hi
  unfold valueOf
  cases hc : classify f x <;> simp [hc] at hi ⊢
  · subst hi; exact satQ_signed 0 (by omega) (by omega)
  all_goals
    rw [natAbs_signed]
    by_cases hm : mantOf f x = 0
    · simp only [signed_eq_zero, hm, ite_true]
      rw [hm, roundToInt_zero] at hi; subst hi; exact satQ_signed 0 (by omega) (by omega)
    · simp only [signed_eq_zero, hm, ite_false]
      rw [hi]; exact satQ_signed i h0 h1

/-- `FCVTZS X, D` out of range, in IEEE mode: a truncation below `-2^63` gives `-2^63`
(`0x8000000000000000`), one at or above `2^63` gives `2^63 - 1`. -/
theorem fpToFixed_rzs_sat (h : IEEEMode fpcr) (f : Fmt) (x : Nat) (i : Int)
    (hi : truncInt f x = some i) :
    (i < -(2 ^ 63 : Int) → (fpToFixed f fpcr false .rz 64 x).1 = 2 ^ 63) ∧
    (2 ^ 63 ≤ i → (fpToFixed f fpcr false .rz 64 x).1 = 2 ^ 63 - 1) := by
  have hah : ah fpcr = false := h.2.1
  simp only [fpToFixed, unpack_ieee h, hah]
  unfold truncInt at hi
  unfold valueOf
  have sat : ∀ j : Int, (j < -(2 ^ 63 : Int) → (satQ 64 false j).1 = 2 ^ 63) ∧
      (2 ^ 63 ≤ j → (satQ 64 false j).1 = 2 ^ 63 - 1) := by
    intro j; constructor <;> intro hj
    · simp [satQ, show j < -9223372036854775808 by omega]
    · simp [satQ, show ¬ j < -9223372036854775808 by omega, show (9223372036854775808 : Int) ≤ j by omega]
  cases hc : classify f x <;> simp [hc] at hi ⊢
  · subst hi; constructor <;> intro hj <;> omega
  all_goals
    rw [natAbs_signed]
    by_cases hm : mantOf f x = 0
    · simp only [signed_eq_zero, hm, ite_true]
      rw [hm, roundToInt_zero] at hi; subst hi; constructor <;> intro hj <;> omega
    · simp only [signed_eq_zero, hm, ite_false]
      rw [hi]; exact sat i

/-- `FCVTZS X, D` of a NaN, in IEEE mode: `0`; of `+∞`: `2^63 - 1`; of `-∞`: `-2^63`. -/
theorem fpToFixed_rzs_special (h : IEEEMode fpcr) (f : Fmt) (x : Nat) :
    (isNaN f x = true → (fpToFixed f fpcr false .rz 64 x).1 = 0) ∧
    (classify f x = .inf → (fpToFixed f fpcr false .rz 64 x).1 =
      if signOf f x then 2 ^ 63 else 2 ^ 63 - 1) := by
  have hah : ah fpcr = false := h.2.1
  simp only [fpToFixed, unpack_ieee h, hah]
  unfold valueOf isNaN
  cases hc : classify f x <;> simp [hc, satQ]
  cases signOf f x <;> simp

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

/-- `FCVT` between single and double precision in IEEE mode: an encoding of `g`, the IEEE
`convertFormat` result when that is not a NaN, else a NaN. -/
theorem fpConvert_ieee (h : IEEEMode fpcr) (f g : Fmt) (hg : g.Std) (rm : RM)
    (x : Nat) :
    (fpConvert f g fpcr rm x).1 < 2 ^ g.width ∧
    ResultIs g (convertFormat f g rm x) (fpConvert f g fpcr rm x).1 := by
  have hdn : dn fpcr = false := h.2.2.2
  have hn := convertNaN_isNaN f g hg x
  simp only [fpConvert, unpack_ieee h, hdn, convertFormat, ResultIs]
  cases hc : classify f x <;>
    simp [hc, typeOf, FPType.isNaN, fpRound_ieee h, zero_lt, inf_lt, round_bits_lt, hn, Val.mag, valueOf,
      natAbs_signed]

/-- The finite non-zero operand that `FMIN`/`FMAX` deliver is rounded back to itself. -/
theorem fpRound_self64 (h : IEEEMode fpcr) (rm : RM) (x : Nat) (hx : x < 2 ^ 64)
    (hc : classify binary64 x = .normal ∨ classify binary64 x = .subnormal) :
    (fpRound binary64 fpcr rm (signOf binary64 x) (valueOf binary64 x).mag.1
      (valueOf binary64 x).mag.2).1 = x := by
  have hv : valueOf binary64 x = .num (if signOf binary64 x then -(mantOf binary64 x : Int)
      else mantOf binary64 x) (ulpExpOf binary64 x) := by
    unfold valueOf; rcases hc with hc | hc <;> rw [hc]
  rw [hv, fpRound_ieee h]
  simp only [Val.mag, natAbs_signed]
  exact round_self64 rm x hx hc

/-- `FMIN Dd, Dn, Dm` in IEEE mode: an encoding, IEEE `minimum(a, b)` when that is not a NaN,
else a NaN. -/
theorem fpMin_ieee (h : IEEEMode fpcr) (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (fpMaxMin false binary64 fpcr false a b).1 < 2 ^ 64 ∧
    ResultIs binary64 (minimum binary64 a b) (fpMaxMin false binary64 fpcr false a b).1 := by
  have hdn : dn fpcr = false := h.2.2.2
  have hah : ah fpcr = false := h.2.1
  simp only [ResultIs, minimum, fpMaxMin, unpack_ieee h, processNaNs, processNaN, hah, hdn]
  have hq := or_quiet_lt binary64 (Or.inr rfl)
  by_cases hlt : Val.lt (valueOf binary64 a) (valueOf binary64 b) = true <;>
  cases h1 : classify binary64 a <;> cases h2 : classify binary64 b <;>
    simp [hlt, h1, h2, typeOf, FPType.isNaN, isNaN, ha, hb, hq, zero_lt, inf_lt,
      fpRound_self64 h, zero_self64, inf_self64]
  all_goals first
    | exact zero_lt binary64 _
    | (have := isNaN_or_quiet binary64 (Or.inr rfl) a (isNaN_of_classify (Or.inr h1))
       simp only [isNaN] at this; exact ⟨hq a ha, this⟩)
    | (have := isNaN_or_quiet binary64 (Or.inr rfl) b (isNaN_of_classify (Or.inr h2))
       simp only [isNaN] at this; exact ⟨hq b hb, this⟩)
    | (refine ⟨zero_lt binary64 _, ?_⟩
       rw [valueOf_of_zero h1, (sign_vs_zero64 b (by simp [h2])).1] at hlt
       simp only [Bool.not_eq_true'] at hlt
       rw [hlt, Bool.or_false, zero_self64 a ha h1])
    | (refine ⟨zero_lt binary64 _, ?_⟩
       rw [valueOf_of_zero h2, (sign_vs_zero64 a (by simp [h1])).2] at hlt
       simp only [Bool.not_eq_true] at hlt
       rw [hlt, Bool.false_or, zero_self64 b hb h2])


/-- `FMAX Dd, Dn, Dm` in IEEE mode: an encoding, IEEE `maximum(a, b)` when that is not a NaN,
else a NaN. -/
theorem fpMax_ieee (h : IEEEMode fpcr) (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (fpMaxMin true binary64 fpcr false a b).1 < 2 ^ 64 ∧
    ResultIs binary64 (maximum binary64 a b) (fpMaxMin true binary64 fpcr false a b).1 := by
  have hdn : dn fpcr = false := h.2.2.2
  have hah : ah fpcr = false := h.2.1
  simp only [ResultIs, maximum, fpMaxMin, unpack_ieee h, processNaNs, processNaN, hah, hdn]
  have hq := or_quiet_lt binary64 (Or.inr rfl)
  by_cases hlt : Val.lt (valueOf binary64 b) (valueOf binary64 a) = true <;>
  cases h1 : classify binary64 a <;> cases h2 : classify binary64 b <;>
    simp [hlt, h1, h2, typeOf, FPType.isNaN, isNaN, ha, hb, hq, zero_lt, inf_lt,
      fpRound_self64 h, zero_self64, inf_self64]
  all_goals first
    | exact zero_lt binary64 _
    | exact absurd hlt (by rw [valueOf_of_zero h1, valueOf_of_zero h2]; decide)
    | (have := isNaN_or_quiet binary64 (Or.inr rfl) a (isNaN_of_classify (Or.inr h1))
       simp only [isNaN] at this; exact ⟨hq a ha, this⟩)
    | (have := isNaN_or_quiet binary64 (Or.inr rfl) b (isNaN_of_classify (Or.inr h2))
       simp only [isNaN] at this; exact ⟨hq b hb, this⟩)
    | (refine ⟨zero_lt binary64 _, ?_⟩
       rw [valueOf_of_zero h1, (sign_vs_zero64 b (by simp [h2])).2] at hlt
       rw [hlt, Bool.and_true, zero_self64 a ha h1])
    | (refine ⟨zero_lt binary64 _, ?_⟩
       rw [valueOf_of_zero h2, (sign_vs_zero64 a (by simp [h1])).1] at hlt
       simp only [Bool.not_eq_true', Bool.not_eq_false] at hlt
       rw [hlt, Bool.true_and, zero_self64 b hb h2])


end Janus.Arm64.FP
