import Janus.Contracts.Hash

/-!
# Laws of Go's float equality and of the seeded hash (proved, not trusted)

The contracts of `Janus.Contracts.Mem` and `Janus.Contracts.Hash` state Go's `==` on floats
(`feq`) and the float hashes (`FHashIs`) by their definitions. A map is correct only if equal keys
hash alike; this file proves the facts that rest on:

* `feq` is Go's `==`: symmetric (`feq_comm`), false on a NaN (`feq_nan_left`, `feq_nan_right`),
  reflexive on every other encoding (`feq_refl`), `+0 == -0` (`feq_zeros`), and a zero equals only
  zeros (`feq_zero_iff`);
* the key fact `feq_eq`: two encodings that are `==` are the same bit pattern unless both are zeros,
  i.e. `valueOf` is injective on infinities and on non-zero finite encodings. The proof decomposes
  an encoding into its sign, exponent and fraction fields (`eq_of_fields`) and uses that a normal
  significand lies in `[2^t, 2^(t+1))` and a subnormal one in `[1, 2^t)` with the least exponent
  (`mant_exp_eq`);
* the float hash laws: zeros hash alike (`fhashIs_zeros`, `fhashIs_zero`), `==` floats hash alike
  (`fhashIs_of_feq`), a NaN may hash to any 64-bit word (`fhashIs_nan`: `c1` is odd, so
  multiplication by it is a bijection mod `2^64`), the hash of a non-NaN is determined
  (`fhashIs_unique`), and hashes are below `2^64` (`fhashIs_lt`);
* the functional laws maps use: `==` strings have equal byte hashes (`strhash_of_strEq`), and the
  hash of a `TFlagRegularMemory` value depends only on its size and bytes (`regHash_congr`,
  `typeHash_regular_congr`, `typeHash_regular_unique`).

The float laws hold for every format; the hypotheses `x < 2 ^ f.width` (the encoding is a bit
pattern of the format) are needed only where encodings are compared as numbers.
-/

namespace Janus.Contracts.HashLaws

open Janus Janus.Arm64 Janus.Float Janus.Spec.Type Janus.Contracts.Mem Janus.Contracts.Hash

/-! ## The fields of an encoding -/

/-- The low `ebits + fbits` bits of an encoding are its exponent and fraction fields. -/
theorem mod_signBit (f : Fmt) (x : Nat) : x % f.signBit = expOf f x * 2 ^ f.fbits + fracOf f x := by
  have : f.signBit = 2 ^ f.fbits * 2 ^ f.ebits := by
    unfold Fmt.signBit; rw [Nat.pow_add, Nat.mul_comm]
  rw [this, Nat.mod_mul]; unfold expOf fracOf; rw [Nat.mul_comm]; omega

/-- An encoding is `sign · 2^(width-1) + exp · 2^t + frac`. -/
theorem decomp (f : Fmt) (x : Nat) (hx : x < 2 ^ f.width) :
    x = (if signOf f x then f.signBit else 0) + expOf f x * 2 ^ f.fbits + fracOf f x := by
  rw [two_pow_width] at hx
  have hs : 0 < f.signBit := Nat.two_pow_pos _
  have hd : x / f.signBit < 2 := (Nat.div_lt_iff_lt_mul hs).2 (by omega)
  have h := Nat.div_add_mod x f.signBit
  rw [mod_signBit] at h
  unfold signOf
  by_cases h1 : x / f.signBit = 1
  · simp [h1] at h ⊢; omega
  · have h0 : x / f.signBit = 0 := by generalize x / f.signBit = q at hd h1; omega
    simp [h0] at h ⊢; omega

/-- Two encodings with the same sign, exponent and fraction fields are equal. -/
theorem eq_of_fields (f : Fmt) {x y : Nat} (hx : x < 2 ^ f.width) (hy : y < 2 ^ f.width)
    (hs : signOf f x = signOf f y) (he : expOf f x = expOf f y) (hfr : fracOf f x = fracOf f y) :
    x = y := by
  rw [decomp f x hx, decomp f y hy, hs, he, hfr]

/-! ## Classification -/

/-- An encoding is a zero exactly when its exponent and fraction fields are 0 (either sign). -/
theorem classify_zero_iff (f : Fmt) (x : Nat) :
    classify f x = .zero ↔ expOf f x = 0 ∧ fracOf f x = 0 := by
  unfold classify
  by_cases h1 : expOf f x = 0 <;> by_cases h2 : expOf f x = f.expMax <;>
    by_cases h3 : fracOf f x = 0 <;> by_cases h4 : fracOf f x / f.quietBit % 2 = 1 <;>
    simp_all

/-- An infinity has the all-ones exponent and a zero fraction. -/
theorem classify_inf (f : Fmt) {x : Nat} (h : classify f x = .inf) :
    expOf f x = f.expMax ∧ fracOf f x = 0 := by
  unfold classify at h
  by_cases h1 : expOf f x = 0 <;> by_cases h2 : expOf f x = f.expMax <;>
    by_cases h3 : fracOf f x = 0 <;> by_cases h4 : fracOf f x / f.quietBit % 2 = 1 <;>
    simp_all

/-- A subnormal number has a zero exponent and a non-zero fraction. -/
theorem classify_subnormal (f : Fmt) {x : Nat} (h : classify f x = .subnormal) :
    expOf f x = 0 ∧ fracOf f x ≠ 0 := by
  unfold classify at h
  by_cases h1 : expOf f x = 0 <;> by_cases h2 : expOf f x = f.expMax <;>
    by_cases h3 : fracOf f x = 0 <;> by_cases h4 : fracOf f x / f.quietBit % 2 = 1 <;>
    simp_all

/-- A normal number has a non-zero exponent. -/
theorem classify_normal (f : Fmt) {x : Nat} (h : classify f x = .normal) : expOf f x ≠ 0 := by
  unfold classify at h
  by_cases h1 : expOf f x = 0 <;> by_cases h2 : expOf f x = f.expMax <;>
    by_cases h3 : fracOf f x = 0 <;> by_cases h4 : fracOf f x / f.quietBit % 2 = 1 <;>
    simp_all

/-- A quiet NaN is a NaN. -/
theorem isNaN_of_qnan {f : Fmt} {x : Nat} (h : classify f x = .qnan) : isNaN f x = true := by
  unfold isNaN; rw [h]

/-- A signalling NaN is a NaN. -/
theorem isNaN_of_snan {f : Fmt} {x : Nat} (h : classify f x = .snan) : isNaN f x = true := by
  unfold isNaN; rw [h]

/-- A zero is not a NaN. -/
theorem not_isNaN_of_zero {f : Fmt} {x : Nat} (h : classify f x = .zero) : isNaN f x = false := by
  unfold isNaN; rw [h]

/-- The value of a subnormal or normal encoding: its signed significand times `2^ulpExpOf`. -/
theorem valueOf_fin {f : Fmt} {x : Nat} (h : classify f x = .subnormal ∨ classify f x = .normal) :
    valueOf f x = .num (if signOf f x then -(mantOf f x : Int) else mantOf f x) (ulpExpOf f x) := by
  unfold valueOf; rcases h with h | h <;> rw [h]

/-- The significand and exponent of a finite non-zero encoding: a subnormal one is below `2^t`
with the least exponent `emin - t`, a normal one lies in `[2^t, 2^(t+1))` with an exponent at
least `emin - t`. -/
theorem mant_bounds {f : Fmt} {x : Nat} (h : classify f x = .subnormal ∨ classify f x = .normal) :
    0 < mantOf f x ∧
    ((mantOf f x < 2 ^ f.fbits ∧ ulpExpOf f x = f.emin - f.fbits) ∨
     (2 ^ f.fbits ≤ mantOf f x ∧ mantOf f x < 2 * 2 ^ f.fbits ∧ f.emin - f.fbits ≤ ulpExpOf f x)) := by
  have hfr : fracOf f x < 2 ^ f.fbits := Nat.mod_lt _ (Nat.two_pow_pos _)
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := classify_subnormal f h
    simp only [mantOf, ulpExpOf, h1, ite_true]
    exact ⟨Nat.pos_of_ne_zero h2, Or.inl ⟨hfr, trivial⟩⟩
  · have h1 := classify_normal f h
    simp only [mantOf, ulpExpOf, h1, ite_false, Fmt.emin]; omega

/-- The arithmetic core of `feq_eq`: if `mx · 2^ex = my · 2^ey` for two significands that are
each either subnormal (`m < B`, exponent `L`) or normal (`B ≤ m < 2B`, exponent at least `L`),
then the significands and the exponents are equal. -/
theorem mant_exp_eq_of_le (mx my B : Nat) (ex ey L : Int) (hle : ex ≤ ey)
    (hx : (mx < B ∧ ex = L) ∨ (B ≤ mx ∧ mx < 2 * B ∧ L ≤ ex))
    (hy : (my < B ∧ ey = L) ∨ (B ≤ my ∧ my < 2 * B ∧ L ≤ ey))
    (h : mx * 2 ^ (ex - min ex ey).toNat = my * 2 ^ (ey - min ex ey).toNat) :
    mx = my ∧ ex = ey := by
  have hm : min ex ey = ex := Int.min_eq_left hle
  rw [hm, Int.sub_self, Int.toNat_zero, Nat.pow_zero, Nat.mul_one] at h
  by_cases hd : (ey - ex).toNat = 0
  · rw [hd, Nat.pow_zero, Nat.mul_one] at h; omega
  · have h2 : 2 ≤ 2 ^ (ey - ex).toNat := by
      have := Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ (ey - ex).toNat by omega)
      simpa using this
    have h3 : 2 * my ≤ my * 2 ^ (ey - ex).toNat := by
      rw [Nat.mul_comm 2 my]; exact Nat.mul_le_mul_left my h2
    generalize my * 2 ^ (ey - ex).toNat = Q at h h3
    omega

/-- `mant_exp_eq_of_le` without the order of the exponents. -/
theorem mant_exp_eq (mx my B : Nat) (ex ey L : Int)
    (hx : (mx < B ∧ ex = L) ∨ (B ≤ mx ∧ mx < 2 * B ∧ L ≤ ex))
    (hy : (my < B ∧ ey = L) ∨ (B ≤ my ∧ my < 2 * B ∧ L ≤ ey))
    (h : mx * 2 ^ (ex - min ex ey).toNat = my * 2 ^ (ey - min ex ey).toNat) :
    mx = my ∧ ex = ey := by
  rcases Int.le_total ex ey with hle | hle
  · exact mant_exp_eq_of_le mx my B ex ey L hle hx hy h
  · rw [Int.min_comm] at h
    have := mant_exp_eq_of_le my mx B ey ex L hle hy hx h.symm
    exact ⟨this.1.symm, this.2.symm⟩

/-- A signed significand times a power of two, as a signed natural number. -/
theorem signed_mul (s : Bool) (m a : Nat) :
    (if s then -(m : Int) else m) * 2 ^ a = if s then -((m * 2 ^ a : Nat) : Int) else ((m * 2 ^ a : Nat) : Int) := by
  cases s <;> simp [Int.neg_mul]

/-- `Val.eq` on two finite values: equality after `align`. -/
theorem val_eq_num (n e n' e' : Int) :
    Val.eq (.num n e) (.num n' e') = true ↔
      n * 2 ^ (e - min e e').toNat = n' * 2 ^ (e' - min e e').toNat := by
  simp [Val.eq, align]

/-- Two finite non-zero encodings with equal values are equal. -/
theorem eq_of_fin (f : Fmt) {x y : Nat} (hx : x < 2 ^ f.width) (hy : y < 2 ^ f.width)
    (cx : classify f x = .subnormal ∨ classify f x = .normal)
    (cy : classify f y = .subnormal ∨ classify f y = .normal)
    (h : Val.eq (valueOf f x) (valueOf f y) = true) : x = y := by
  rw [valueOf_fin cx, valueOf_fin cy, val_eq_num, signed_mul, signed_mul] at h
  obtain ⟨px, bx⟩ := mant_bounds cx
  obtain ⟨py, b_y⟩ := mant_bounds cy
  have qx : 0 < mantOf f x * 2 ^ (ulpExpOf f x - min (ulpExpOf f x) (ulpExpOf f y)).toNat :=
    Nat.mul_pos px (Nat.two_pow_pos _)
  have qy : 0 < mantOf f y * 2 ^ (ulpExpOf f y - min (ulpExpOf f x) (ulpExpOf f y)).toNat :=
    Nat.mul_pos py (Nat.two_pow_pos _)
  have hs : signOf f x = signOf f y ∧
      mantOf f x * 2 ^ (ulpExpOf f x - min (ulpExpOf f x) (ulpExpOf f y)).toNat =
        mantOf f y * 2 ^ (ulpExpOf f y - min (ulpExpOf f x) (ulpExpOf f y)).toNat := by
    revert h qx qy
    generalize mantOf f x * 2 ^ (ulpExpOf f x - min (ulpExpOf f x) (ulpExpOf f y)).toNat = P
    generalize mantOf f y * 2 ^ (ulpExpOf f y - min (ulpExpOf f x) (ulpExpOf f y)).toNat = Q
    cases signOf f x <;> cases signOf f y <;> simp <;> omega
  obtain ⟨hm, he⟩ := mant_exp_eq _ _ _ _ _ _ bx b_y hs.2
  have hfx : fracOf f x < 2 ^ f.fbits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hfy : fracOf f y < 2 ^ f.fbits := Nat.mod_lt _ (Nat.two_pow_pos _)
  apply eq_of_fields f hx hy hs.1
  · unfold mantOf at hm; unfold ulpExpOf at he
    by_cases h1 : expOf f x = 0 <;> by_cases h2 : expOf f y = 0 <;> simp only [h1, h2, ite_true, ite_false] at hm he
    · omega
    · omega
    · omega
    · omega
  · unfold mantOf at hm
    by_cases h1 : expOf f x = 0 <;> by_cases h2 : expOf f y = 0 <;> simp only [h1, h2, ite_true, ite_false] at hm <;> omega

/-- A finite non-zero value is not equal to zero. -/
theorem fin_ne_zero (f : Fmt) {x : Nat} (cx : classify f x = .subnormal ∨ classify f x = .normal) :
    Val.eq (valueOf f x) (.num 0 0) = false ∧ Val.eq (.num 0 0) (valueOf f x) = false := by
  obtain ⟨px, -⟩ := mant_bounds cx
  rw [valueOf_fin cx]
  constructor <;> (apply Bool.eq_false_iff.2; intro h; rw [val_eq_num] at h)
  · rw [signed_mul] at h
    have := Nat.mul_pos px (Nat.two_pow_pos (ulpExpOf f x - min (ulpExpOf f x) 0).toNat)
    revert h this
    generalize mantOf f x * 2 ^ (ulpExpOf f x - min (ulpExpOf f x) 0).toNat = P
    cases signOf f x <;> simp <;> omega
  · rw [signed_mul] at h
    have := Nat.mul_pos px (Nat.two_pow_pos (ulpExpOf f x - min 0 (ulpExpOf f x)).toNat)
    revert h this
    generalize mantOf f x * 2 ^ (ulpExpOf f x - min 0 (ulpExpOf f x)).toNat = P
    cases signOf f x <;> simp <;> omega

/-! ## Go's `==` on floats -/

/-- `Val.eq` is symmetric. -/
theorem Val.eq_comm (a b : Val) : Val.eq a b = Val.eq b a := by
  cases a <;> cases b <;> simp only [Val.eq, align, Int.min_comm] <;>
    (apply Bool.eq_iff_iff.2; simp only [beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩)

/-- `Val.eq` is reflexive. -/
theorem Val.eq_refl (a : Val) : Val.eq a a = true := by
  cases a <;> simp [Val.eq, align]

/-- Go's `x == y` on floats is symmetric: `x == y` and `y == x` agree. -/
theorem feq_comm (f : Fmt) (x y : Nat) : feq f x y = feq f y x := by
  unfold feq; rw [Bool.or_comm, Val.eq_comm]

/-- A NaN on the left of Go's `==` makes it false: `NaN == y` is false for every `y`. -/
theorem feq_nan_left (f : Fmt) {x : Nat} (y : Nat) (h : isNaN f x = true) : feq f x y = false := by
  unfold feq; simp [h]

/-- A NaN on the right of Go's `==` makes it false: `x == NaN` is false for every `x`. -/
theorem feq_nan_right (f : Fmt) (x : Nat) {y : Nat} (h : isNaN f y = true) : feq f x y = false := by
  unfold feq; simp [h]

/-- Every non-NaN float equals itself under Go's `==` (`x == x` unless `x` is a NaN). -/
theorem feq_refl (f : Fmt) {x : Nat} (h : isNaN f x = false) : feq f x x = true := by
  unfold feq; simp [h, Val.eq_refl]

/-- Any two zeros are equal under Go's `==`; in particular `+0 == -0`. -/
theorem feq_zeros (f : Fmt) {x y : Nat} (hx : classify f x = .zero) (hy : classify f y = .zero) :
    feq f x y = true := by
  unfold feq
  rw [not_isNaN_of_zero hx, not_isNaN_of_zero hy, valueOf_of_zero hx, valueOf_of_zero hy]
  decide

/-- **Equal floats have equal encodings, unless both are zeros.** If Go's `x == y` holds for two
encodings of the format, they are the same bit pattern, or both are zeros (`+0` and `-0`). So the
only distinct bit patterns that `==` identifies are the two zeros, which is what a map (whose keys
are compared with `==` and hashed by their bits) must treat specially. -/
theorem feq_eq (f : Fmt) {x y : Nat} (hx : x < 2 ^ f.width) (hy : y < 2 ^ f.width)
    (h : feq f x y = true) : x = y ∨ (classify f x = .zero ∧ classify f y = .zero) := by
  unfold feq at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at h
  obtain ⟨⟨nx, ny⟩, hv⟩ := h
  cases cx : classify f x <;> cases cy : classify f y
  all_goals first
    | (exfalso; rw [isNaN_of_qnan cx] at nx; exact Bool.noConfusion nx)
    | (exfalso; rw [isNaN_of_snan cx] at nx; exact Bool.noConfusion nx)
    | (exfalso; rw [isNaN_of_qnan cy] at ny; exact Bool.noConfusion ny)
    | (exfalso; rw [isNaN_of_snan cy] at ny; exact Bool.noConfusion ny)
    | (right; exact ⟨rfl, rfl⟩)
    | skip
  -- zero against a finite non-zero value
  · rw [valueOf_of_zero cx] at hv; rw [(fin_ne_zero f (.inl cy)).2] at hv; exact absurd hv (by decide)
  · rw [valueOf_of_zero cx] at hv; rw [(fin_ne_zero f (.inr cy)).2] at hv; exact absurd hv (by decide)
  · rw [valueOf_of_zero cx] at hv; unfold valueOf at hv; rw [cy] at hv; simp [Val.eq] at hv
  · rw [valueOf_of_zero cy] at hv; rw [(fin_ne_zero f (.inl cx)).1] at hv; exact absurd hv (by decide)
  · left; exact eq_of_fin f hx hy (.inl cx) (.inl cy) hv
  · left; exact eq_of_fin f hx hy (.inl cx) (.inr cy) hv
  · rw [valueOf_fin (.inl cx)] at hv; unfold valueOf at hv; rw [cy] at hv; exact absurd hv (by simp [Val.eq])
  · rw [valueOf_of_zero cy] at hv; rw [(fin_ne_zero f (.inr cx)).1] at hv; exact absurd hv (by decide)
  · left; exact eq_of_fin f hx hy (.inr cx) (.inl cy) hv
  · left; exact eq_of_fin f hx hy (.inr cx) (.inr cy) hv
  · rw [valueOf_fin (.inr cx)] at hv; unfold valueOf at hv; rw [cy] at hv; exact absurd hv (by simp [Val.eq])
  · rw [valueOf_of_zero cy] at hv; unfold valueOf at hv; rw [cx] at hv; simp [Val.eq] at hv
  · rw [valueOf_fin (.inl cy)] at hv; unfold valueOf at hv; rw [cx] at hv; exact absurd hv (by simp [Val.eq])
  · rw [valueOf_fin (.inr cy)] at hv; unfold valueOf at hv; rw [cx] at hv; exact absurd hv (by simp [Val.eq])
  · -- two infinities: equal signs
    left
    unfold valueOf at hv; rw [cx, cy] at hv
    simp only [Val.eq, beq_iff_eq] at hv
    obtain ⟨ex, fx⟩ := classify_inf f cx
    obtain ⟨ey, fy⟩ := classify_inf f cy
    exact eq_of_fields f hx hy hv (by rw [ex, ey]) (by rw [fx, fy])

/-- A zero equals exactly the zeros under Go's `==`: `0 == y` holds iff `y` is `+0` or `-0`. -/
theorem feq_zero_iff (f : Fmt) {x y : Nat} (hx : x < 2 ^ f.width) (hy : y < 2 ^ f.width)
    (h0 : classify f x = .zero) : feq f x y = true ↔ classify f y = .zero := by
  constructor
  · intro h
    rcases feq_eq f hx hy h with rfl | ⟨-, h⟩
    · exact h0
    · exact h
  · exact feq_zeros f h0

/-- The two zeros of a format, `+0` and `-0`, are zeros. -/
theorem classify_zero (f : Fmt) (s : Bool) : classify f (zero f s) = .zero := by
  rw [classify_zero_iff]
  have hm : zero f s % f.signBit = 0 := by
    cases s <;> simp [zero, pack, Nat.mod_self, Nat.zero_mod]
  rw [mod_signBit] at hm
  constructor
  · have := Nat.two_pow_pos f.fbits
    rcases Nat.eq_zero_or_pos (expOf f (zero f s)) with h | h
    · exact h
    · exfalso; have := Nat.mul_pos h (Nat.two_pow_pos f.fbits); omega
  · omega

/-! ## The float hashes -/

/-- Two zeros (`+0` and `-0`) have the same possible hashes: Go's `f32hash`/`f64hash` hash every
zero to `c1 · (c0 ^ h)`, so a map finds the key `-0` under `+0`. -/
theorem fhashIs_zeros (H : HashModel) (f : Fmt) (k : Nat) {x y : Nat} (h r : Nat)
    (hx : classify f x = .zero) (hy : classify f y = .zero) :
    FHashIs H f k x h r ↔ FHashIs H f k y h r := by
  unfold FHashIs; rw [hx, hy, ite_eq_left rfl, ite_eq_left rfl]

/-- `+0` and `-0` have the same possible hashes. -/
theorem fhashIs_zero (H : HashModel) (f : Fmt) (k h r : Nat) :
    FHashIs H f k (zero f false) h r ↔ FHashIs H f k (zero f true) h r :=
  fhashIs_zeros H f k h r (classify_zero f false) (classify_zero f true)

/-- **Equal floats hash alike.** If Go's `x == y` holds for two encodings of the format, their
possible hashes under the same seed are the same: the law a map needs to find a float key under
any key `==` to it. -/
theorem fhashIs_of_feq (H : HashModel) (f : Fmt) (k : Nat) {x y : Nat} (h r : Nat)
    (hx : x < 2 ^ f.width) (hy : y < 2 ^ f.width) (he : feq f x y = true) :
    FHashIs H f k x h r ↔ FHashIs H f k y h r := by
  rcases feq_eq f hx hy he with rfl | ⟨h1, h2⟩
  · exact Iff.rfl
  · exact fhashIs_zeros H f k h r h1 h2

/-- The inverse of `c1` modulo `2^64` (`c1` is odd). -/
def c1inv : Nat := 7906388553261026367

/-- `c1 · c1inv = 1` modulo `2^64`. -/
theorem c1_mul_inv : c1 * c1inv % 2 ^ 64 = 1 := by decide

/-- **A NaN may hash to any 64-bit word.** For a NaN key, Go's float hash mixes in `rand()`, and
since `c1` is invertible mod `2^64` every 64-bit result is possible: nothing can be concluded about
the hash of a NaN (which is why a NaN key can be inserted many times and never found). -/
theorem fhashIs_nan (H : HashModel) (f : Fmt) (k : Nat) {x h r : Nat} (hn : isNaN f x = true)
    (hh : h < 2 ^ 64) (hr : r < 2 ^ 64) : FHashIs H f k x h r := by
  have hz : classify f x ≠ .zero := by
    intro hz; rw [not_isNaN_of_zero hz] at hn; exact Bool.noConfusion hn
  unfold FHashIs; rw [ite_eq_right hz, ite_eq_left hn]
  have hc0 : c0 < 2 ^ 64 := by decide
  have ht : r * c1inv % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos _)
  refine ⟨(c0 ^^^ h) ^^^ (r * c1inv % 2 ^ 64), Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hc0 hh) ht, ?_⟩
  rw [← Nat.xor_assoc (c0 ^^^ h), Nat.xor_self, Nat.zero_xor, Nat.mul_mod, Nat.mod_mod,
    ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_comm c1 r, Nat.mul_assoc, Nat.mul_mod, c1_mul_inv,
    Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hr]

/-- The hash of a non-NaN float is determined by the seed and the encoding. -/
theorem fhashIs_unique (H : HashModel) (f : Fmt) (k : Nat) {x h r r' : Nat} (hn : isNaN f x = false)
    (h1 : FHashIs H f k x h r) (h2 : FHashIs H f k x h r') : r = r' := by
  unfold FHashIs at h1 h2; rw [hn] at h1 h2
  by_cases hz : classify f x = .zero
  · rw [ite_eq_left hz] at h1 h2; rw [h1, h2]
  · rw [ite_eq_right hz] at h1 h2; simp only [Bool.false_eq_true, ite_false] at h1 h2; rw [h1, h2]

/-- Every possible float hash is a 64-bit word (given `H.Laws`). -/
theorem fhashIs_lt {H : HashModel} (hL : H.Laws) (f : Fmt) (k : Nat) {x h r : Nat}
    (hh : FHashIs H f k x h r) : r < 2 ^ 64 := by
  unfold FHashIs at hh
  split at hh
  · rw [hh]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · split at hh
    · obtain ⟨_, _, hh⟩ := hh; rw [hh]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · rw [hh]; exact hL.mem_lt _ _ _

/-! ## Strings and regular memory -/

/-- Go's `==` on strings is equality of the lengths and of the bytes. -/
theorem strEq_iff (m : Memory) (a b : Nat) :
    strEq m a b = true ↔ strLen m a = strLen m b ∧
      m.readLE (strPtr m a) (strLen m a) = m.readLE (strPtr m b) (strLen m b) := by
  simp [strEq]

/-- **Equal strings hash alike.** If the strings with headers at `a` and `b` are `==`
(`runtime.strequal`), `strhash` gives them the same hash under the same seed: the byte hash
`H.mem h len bytes` sees the same length and the same bytes. -/
theorem strhash_of_strEq (H : HashModel) (m : Memory) {a b : Nat} (h : Nat) (he : strEq m a b = true) :
    H.mem h (strLen m a) (m.readLE (strPtr m a) (strLen m a)) =
      H.mem h (strLen m b) (m.readLE (strPtr m b) (strLen m b)) := by
  obtain ⟨h1, h2⟩ := (strEq_iff m a b).1 he
  rw [h2, h1]

/-- The hash of a `TFlagRegularMemory` value depends only on the seed, the size and the bytes. -/
theorem regHash_congr (H : HashModel) (h : Nat) {n n' v v' : Nat} (hn : n = n') (hv : v = v') :
    H.regHash h n v = H.regHash h n' v' := by
  rw [hn, hv]

/-- The hash of a `TFlagRegularMemory` value is a 64-bit word (given `H.Laws`). -/
theorem regHash_lt {H : HashModel} (hL : H.Laws) (h n v : Nat) : H.regHash h n v < 2 ^ 64 := by
  unfold HashModel.regHash
  split
  · exact hL.mem32_lt _ _
  · split
    · exact hL.mem64_lt _ _
    · exact hL.mem_lt _ _ _

/-- **Equal bytes hash alike.** Two hashable values of a `TFlagRegularMemory` type `t` (in memories
`m`, `m'` where the runtime is usable and `t` has the same size) whose bytes are equal have the
same possible `typehash` results under the same seed: what a map with such keys (compared by
`memequal`) relies on. -/
theorem typeHash_regular_congr {H : HashModel} (hL : H.Laws) {m m' : Memory} {g g' : W64}
    {t p q : Nat} (h r : Nat) (he : H.Env m g) (he' : H.Env m' g')
    (hp : H.Hashable t m p) (hq : H.Hashable t m' q)
    (hr : isRegularMemory m t = true) (hr' : isRegularMemory m' t = true)
    (hs : tySize m t = tySize m' t)
    (hb : m.readLE p (tySize m t) = m'.readLE q (tySize m' t)) :
    H.TypeHash t m p h r ↔ H.TypeHash t m' q h r := by
  rw [hL.regular m g t p h r he hp hr, hL.regular m' g' t q h r he' hq hr', hb, hs]

/-- The `typehash` of a `TFlagRegularMemory` value is determined: it has exactly one possible
result, `H.regHash` of its size and bytes. -/
theorem typeHash_regular_unique {H : HashModel} (hL : H.Laws) {m : Memory} {g : W64} {t p h r r' : Nat}
    (he : H.Env m g) (hp : H.Hashable t m p) (hr : isRegularMemory m t = true)
    (h1 : H.TypeHash t m p h r) (h2 : H.TypeHash t m p h r') : r = r' := by
  rw [hL.regular m g t p h r he hp hr] at h1
  rw [hL.regular m g t p h r' he hp hr] at h2
  rw [h1, h2]

end Janus.Contracts.HashLaws
