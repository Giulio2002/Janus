import Janus.Float.Lemmas
import Janus.Tactic
import Janus.Contracts.Map

/-!
# Conversions between binary32 and binary64, as specifications

IEEE 754-2019 §5.4.2 `convertFormat`: the value of the source encoding, rounded to the
destination format (exact when widening); a NaN source gives a NaN (`none`, as for the
operations of `Janus.Float.Spec`: which NaN is the architecture's choice, §6.2.3); infinities
and zeros keep their sign.
-/

namespace Janus.Float

/-- `convertFormat` from `f` to `g` in rounding direction `rm`: the encoding of the result, or
`none` for a NaN. -/
def cvt (f g : Fmt) (rm : RM) (x : Nat) : Option Nat :=
  match classify f x with
  | .qnan | .snan => none
  | .inf => some (inf g (signOf f x))
  | .zero => some (zero g (signOf f x))
  | _ => some (round g rm (signOf f x) (mantOf f x) (ulpExpOf f x)).bits

/-- Rounding a value that binary64 represents exactly as a normal number: `m · 2^e` with
`L = log2 m ≤ 52` and exponent `E = L + e` in the normal range gives the encoding with biased
exponent `E + 1023` and the significand `m · 2^(52 - L)`. -/
theorem round64_exact_normal (rm : RM) (neg : Bool) (m : Nat) (e : Int) (hm : 0 < m)
    (hL : Nat.log2 m ≤ 52) (hE1 : -1022 ≤ (Nat.log2 m : Int) + e) (hE2 : (Nat.log2 m : Int) + e ≤ 1023) :
    (round binary64 rm neg m e).bits =
      pack binary64 neg ((Nat.log2 m : Int) + e + 1023).toNat (m * 2 ^ (52 - Nat.log2 m) % 2 ^ 52) := by
  have hL1 : 2 ^ Nat.log2 m ≤ m := Nat.log2_self_le (by omega)
  have hL2 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  unfold round roundUnits biasedExp roundAt
  simp only [b64_emin]
  generalize Nat.log2 m = L at *
  have hk1 : 2 ^ 52 ≤ m * 2 ^ (52 - L) := by
    calc 2 ^ 52 = 2 ^ L * 2 ^ (52 - L) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ m * 2 ^ (52 - L) := Nat.mul_le_mul_right _ hL1
  have hk2 : m * 2 ^ (52 - L) < 2 ^ 53 := by
    calc m * 2 ^ (52 - L) < 2 ^ (L + 1) * 2 ^ (52 - L) := Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
      _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
  have hq : max ((L : Int) + e) (-1022) - 52 = (L : Int) + e - 52 := by omega
  have hs : (e - ((L : Int) + e - 52)).toNat = 52 - L := by omega
  simp [binary64, Fmt.bias, Fmt.expMax, hq, hs, show ((L : Int) + e - 52 ≤ e) by omega]
  generalize m * 2 ^ (52 - L) = k at *
  have e1 : (k = 9007199254740992) = False := by simp; omega
  have e2 : (k < 4503599627370496) = False := by simp; omega
  have e3 : ((2047 : Int) ≤ (L : Int) + e - 52 + 52 + 1023) = False := by simp; omega
  simp only [e1, e2, e3, ite_false, pack]
  have e4 : ((L : Int) + e - 52 + 52 + 1023) = (L : Int) + e + 1023 := by omega
  rw [e4]

/-! ## binary32 → binary64 by class

`x` is a binary32 encoding (`x < 2^32`) with exponent field `E = x / 2^23 % 256`, fraction
`F = x % 2^23` and sign bit `x / 2^31 % 2`. -/

theorem b32_exp (x : Nat) : expOf binary32 x = x / 2 ^ 23 % 256 := rfl
theorem b32_frac (x : Nat) : fracOf binary32 x = x % 2 ^ 23 := rfl
theorem b32_sign (x : Nat) : signOf binary32 x = decide (x / 2 ^ 31 % 2 = 1) := rfl

theorem cvt32to64_normal (x : Nat) (hE1 : x / 2 ^ 23 % 256 ≠ 0) (hE2 : x / 2 ^ 23 % 256 ≠ 255) :
    cvt binary32 binary64 .rne x =
      some (pack binary64 (decide (x / 2 ^ 31 % 2 = 1)) (x / 2 ^ 23 % 256 + 896) (x % 2 ^ 23 * 2 ^ 29)) := by
  have hex : binary32.expMax = 255 := rfl
  have hcl : classify binary32 x = .normal := by
    unfold classify; simp [b32_exp, hE1, hex, hE2]
  have hF := Nat.mod_lt x (show 0 < 2 ^ 23 by decide)
  have hm : mantOf binary32 x = 2 ^ 23 + x % 2 ^ 23 := by
    unfold mantOf; simp [b32_exp, b32_frac, hE1]; rfl
  have hu : ulpExpOf binary32 x = ((x / 2 ^ 23 % 256 : Nat) : Int) - 150 := by
    unfold ulpExpOf
    rw [if_neg (show ¬ expOf binary32 x = 0 from hE1)]
    show ((x / 2 ^ 23 % 256 : Nat) : Int) - (2 ^ (8 - 1) - 1 : Nat) - (23 : Nat) = _
    omega
  have hL : Nat.log2 (2 ^ 23 + x % 2 ^ 23) = 23 :=
    (Nat.log2_eq_iff (by omega)).2 ⟨by simp, by simp only [Nat.reducePow]; omega⟩
  unfold cvt
  rw [hcl]
  simp only [hm, hu, b32_sign]
  have hE := Nat.mod_lt (x / 2 ^ 23) (show 0 < 256 by decide)
  rw [round64_exact_normal _ _ _ _ (by omega) (by omega) (by rw [hL]; omega) (by rw [hL]; omega), hL]
  congr 2
  · omega
  · rw [show (52 - 23 : Nat) = 29 by rfl, Nat.add_mul]
    rw [show (2 : Nat) ^ 23 * 2 ^ 29 = 2 ^ 52 by rfl]
    rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by
      calc x % 2 ^ 23 * 2 ^ 29 < 2 ^ 23 * 2 ^ 29 := Nat.mul_lt_mul_of_pos_right hF (by decide)
        _ = 2 ^ 52 := rfl)

theorem cvt32to64_zero (x : Nat) (hE : x / 2 ^ 23 % 256 = 0) (hF : x % 2 ^ 23 = 0) :
    cvt binary32 binary64 .rne x = some (pack binary64 (decide (x / 2 ^ 31 % 2 = 1)) 0 0) := by
  have hcl : classify binary32 x = .zero := by unfold classify; simp [b32_exp, b32_frac, hE, hF]
  unfold cvt; rw [hcl]; rfl

theorem cvt32to64_inf (x : Nat) (hE : x / 2 ^ 23 % 256 = 255) (hF : x % 2 ^ 23 = 0) :
    cvt binary32 binary64 .rne x = some (pack binary64 (decide (x / 2 ^ 31 % 2 = 1)) 2047 0) := by
  have hex : binary32.expMax = 255 := rfl
  have hcl : classify binary32 x = .inf := by unfold classify; simp [b32_exp, b32_frac, hE, hF, hex]
  unfold cvt; rw [hcl]; rfl

theorem cvt32to64_nan (x : Nat) (hE : x / 2 ^ 23 % 256 = 255) (hF : x % 2 ^ 23 ≠ 0) :
    cvt binary32 binary64 .rne x = none := by
  have hex : binary32.expMax = 255 := rfl
  have hcl : classify binary32 x = .qnan ∨ classify binary32 x = .snan := by
    unfold classify; simp only [b32_exp, b32_frac, hE, hex]; simp only [hF]
    by_cases hq : x % 8388608 / binary32.quietBit % 2 = 1 <;> simp [hq]
  unfold cvt; rcases hcl with h | h <;> rw [h]

/-- A subnormal binary32 `F · 2^-149` (`0 < F < 2^23`, `L = log2 F`) widens to the normal
binary64 with biased exponent `L + 874` and the significand `F · 2^(52 - L)`. -/
theorem cvt32to64_sub (x : Nat) (hE : x / 2 ^ 23 % 256 = 0) (hF : x % 2 ^ 23 ≠ 0) :
    cvt binary32 binary64 .rne x =
      some (pack binary64 (decide (x / 2 ^ 31 % 2 = 1)) (Nat.log2 (x % 2 ^ 23) + 874)
        (x % 2 ^ 23 * 2 ^ (52 - Nat.log2 (x % 2 ^ 23)) % 2 ^ 52)) := by
  have hcl : classify binary32 x = .subnormal := by unfold classify; simp [b32_exp, b32_frac, hE, hF]
  have hm : mantOf binary32 x = x % 2 ^ 23 := by unfold mantOf; simp [b32_exp, b32_frac, hE]
  have hu : ulpExpOf binary32 x = -149 := by
    unfold ulpExpOf; rw [if_pos (show expOf binary32 x = 0 from hE)]; decide
  have hF' := Nat.mod_lt x (show 0 < 2 ^ 23 by decide)
  have hL : Nat.log2 (x % 2 ^ 23) < 23 := (Nat.log2_lt hF).2 hF'
  unfold cvt
  rw [hcl]
  simp only [hm, hu, b32_sign]
  rw [round64_exact_normal _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
  congr 2
  omega

/-- A binary64 encoding assembled with `OR`s of disjoint fields (sign bit `sv`, biased exponent
`E`, fraction `fr`) is `pack`. -/
theorem or_pack64 (fr E sv : Nat) (hfr : fr < 2 ^ 52) (hE : E < 2 ^ 11) :
    fr ||| ((sv % 2) * 2 ^ 63 ||| E * 2 ^ 52) = pack binary64 (decide (sv % 2 = 1)) E fr := by
  have h1 : (sv % 2) * 2 ^ 63 ||| E * 2 ^ 52 = (2 ^ 11 * (sv % 2) + E) * 2 ^ 52 := by
    rw [Nat.two_pow_add_eq_or_of_lt hE]
    rw [show (2 ^ 11 * (sv % 2) ||| E) * 2 ^ 52 = (2 ^ 11 * (sv % 2) ||| E) <<< 52 from
      (Nat.shiftLeft_eq _ _).symm, Nat.shiftLeft_or_distrib, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
      Nat.mul_comm (2 ^ 11), Nat.mul_assoc, ← Nat.pow_add]
  rw [h1, Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hfr]
  unfold pack
  have : sv % 2 = 0 ∨ sv % 2 = 1 := by omega
  rcases this with h | h <;> simp [h, binary64, Fmt.signBit] <;> omega

/-- Masking one bit. -/
theorem and_two_pow_eq (n k : Nat) : n &&& 2 ^ k = (n / 2 ^ k % 2) * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.testBit_mul_two_pow]
  by_cases hi : k = i
  · subst hi
    simp only [decide_true, Bool.and_true, Nat.le_refl, Nat.sub_self, Bool.true_and,
      Nat.testBit_eq_decide_div_mod_eq (i := k), Nat.testBit_eq_decide_div_mod_eq (i := 0)]
    simp
  · simp only [hi, decide_false, Bool.and_false]
    by_cases hki : k ≤ i
    · have h2 : 2 ≤ 2 ^ (i - k) := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ i - k by omega)
        simpa using this
      have : (n / 2 ^ k % 2).testBit (i - k) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) h2)
      simp [hki, this]
    · simp [hki]

end Janus.Float

namespace Janus.Spec.SoftFloat

open Janus.Arm64 Janus.Tactic

private theorem decide_beq_decide' (A B : Prop) [Decidable A] [Decidable B] :
    (decide A == decide B) = decide (A ↔ B) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

set_option maxRecDepth 20000 in
/-- After `CMN x, y` (`adds xzr, x, y`) the signed `GE`/`LT` test `N == V` is `0 ≤ x + y` on the
signed values (arm64; the executor knows the `CMP` forms, `Tactic.sub_flags_nv`). -/
theorem add_flags_nv (x y : BitVec 64) :
    ((addWithCarry x y false).2.n == (addWithCarry x y false).2.v) = decide (0 ≤ x.toInt + y.toInt) := by
  have hx := x.isLt; have hy := y.isLt
  have key : ∀ r : Nat, r = (x.toNat + y.toNat) % 18446744073709551616 →
      (decide (9223372036854775808 ≤ r) ==
        !decide ((if r < 9223372036854775808 then (r : Int) else (r : Int) - 18446744073709551616) =
          (if x.toNat < 9223372036854775808 then (x.toNat : Int) else (x.toNat : Int) - 18446744073709551616) +
          (if y.toNat < 9223372036854775808 then (y.toNat : Int) else (y.toNat : Int) - 18446744073709551616))) =
      decide (0 ≤ (if x.toNat < 9223372036854775808 then (x.toNat : Int) else (x.toNat : Int) - 18446744073709551616) +
          (if y.toNat < 9223372036854775808 then (y.toNat : Int) else (y.toNat : Int) - 18446744073709551616)) := by
    intro r hr
    rw [← decide_not, decide_beq_decide']
    apply decide_eq_decide.mpr
    by_cases h : x.toNat + y.toNat < 18446744073709551616
    · rw [Nat.mod_eq_of_lt h] at hr
      split <;> split <;> split <;> omega
    · have e : (x.toNat + y.toNat) % 18446744073709551616 = x.toNat + y.toNat - 18446744073709551616 := by
        omega
      rw [e] at hr
      split <;> split <;> split <;> omega
  have := key _ rfl
  simp only [addWithCarry, Bool.toNat_false, Nat.add_zero, BitVec.msb_eq_decide, BitVec.toNat_ofNat,
    decide_not]
  simp only [toInt64_cond, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Int.natCast_zero,
    Int.add_zero]
  exact this

/-- `CMP Wn, …` (32-bit): the carry flag is the unsigned `≥` (as `Tactic.sub_flags_c` at 64 bits). -/
theorem sub_flags_c32 (x y : BitVec 32) : (addSub x y true).2.c = decide (y.toNat ≤ x.toNat) := by
  simp only [addSub, addWithCarry, ite_true, BitVec.toNat_ofNat, BitVec.toNat_not, Bool.toNat_true]
  have := x.isLt; have := y.isLt
  apply decide_eq_decide.mpr
  constructor
  · intro h
    apply Classical.byContradiction; intro h'; apply h
    rw [Nat.mod_eq_of_lt (by omega)]
  · intro h h'
    rw [show x.toNat + (2 ^ 32 - 1 - y.toNat) + 1 = (x.toNat - y.toNat) + 2 ^ 32 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h'
    omega

theorem toInt_ofInt64 (e : Int) (h1 : -2 ^ 63 ≤ e) (h2 : e < 2 ^ 63) : (BitVec.ofInt 64 e).toInt = e := by
  exact BitVec.toInt_ofInt_eq_self (by decide) h1 h2

/-- `UBFIZ Xd, Xn, #n, #w` (and `LSL #n` for `w = 64 - n`) as the executor leaves it: a rotation
right by `64 - n` and the mask of bits `[n, n + w)`, which is the low `w` bits shifted left. -/
theorem ubfiz_eq (x : BitVec 64) (n w : Nat) (hn : 0 < n) (h : n + w ≤ 64) :
    x.rotateRight (64 - n) &&& BitVec.ofNat 64 ((2 ^ w - 1) * 2 ^ n) =
      (x &&& BitVec.ofNat 64 (2 ^ w - 1)) <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm1 : (2 ^ w - 1) * 2 ^ n < 2 ^ 64 := by
    calc (2 ^ w - 1) * 2 ^ n < 2 ^ w * 2 ^ n :=
          Nat.mul_lt_mul_of_pos_right (by have := Nat.two_pow_pos w; omega) (Nat.two_pow_pos n)
      _ = 2 ^ (w + n) := by rw [Nat.pow_add]
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  have hm2 : 2 ^ w - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show w ≤ 64 by omega)
    have := Nat.two_pow_pos w; omega
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one, hi, decide_true,
    Bool.true_and]
  by_cases hin : i < n
  · simp [hin, show ¬ n ≤ i by omega]
  · simp only [hin, decide_false, Bool.not_false, Bool.true_and, show n ≤ i by omega, decide_true]
    rw [Nat.mod_eq_of_lt (show 64 - n < 64 by omega)]
    simp only [show ¬ i < 64 - (64 - n) by omega, ite_false, show i - (64 - (64 - n)) = i - n by omega,
      show i - n < 64 by omega, decide_true, Bool.true_and]

/-- `UBFX Xd, Xn, #r, #w` (a rotation right by `r` and a mask of the low `w` bits) is the field
`x / 2^r % 2^w`. -/
theorem ubfx_eq (x : BitVec 64) (r w : Nat) (hr : r < 64) (h : r + w ≤ 64) :
    x.rotateRight r &&& BitVec.ofNat 64 (2 ^ w - 1) = BitVec.ofNat 64 (x.toNat / 2 ^ r % 2 ^ w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm2 : 2 ^ w - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show w ≤ 64 by omega)
    have := Nat.two_pow_pos w; omega
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.mod_eq_of_lt hr]
  by_cases hiw : i < w
  · simp only [hiw, decide_true, Bool.and_true]
    rw [if_pos (show i < 64 - r by omega)]
    simp only [Bool.true_and, BitVec.testBit_toNat, Nat.add_comm]
  · simp [hiw]

/-- The return of an arm64 leaf function that obeys the Go ABI from `s` to `s'` with result `v`
in `X0`: back at `X30`, `SP`, `X18`, `X28`, `X29`, memory and the SIMD registers unchanged, every
other general register and the flags arbitrary. -/
abbrev LeafRet (s s' : State) (v : BitVec 64) : Prop :=
  ∃ (r : Nat → BitVec 64) (f : Flags),
    s' = { s with regs := Contracts.Map.keepABI s.regs r, flags := f, pc := s.regs 30 } ∧ r 0 = v

theorem leafRet_of (s s' : State) (v : BitVec 64) (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30)
    (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29)
    (hm : s'.mem = s.mem) (hv : s'.vregs = s.vregs) (hdz : s'.dczid = s.dczid)
    (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr) (hfs : s'.fpsr = s.fpsr)
    (h0 : s'.regs 0 = v) : LeafRet s s' v := by
  refine ⟨s'.regs, s'.flags, ?_, h0⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s'
  simp only at hsp hpc hdz htp hfc hfs h18 h28 h29 hm hv ⊢
  subst hsp hpc hdz htp hfc hfs hm hv
  congr
  funext i
  simp only [Contracts.Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

end Janus.Spec.SoftFloat
