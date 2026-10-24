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

theorem resultIs_bind (f : Fmt) (o : Option Nat) (x : Nat) (k : Nat → Option Nat)
    (hk : ∀ y, isNaN f y = true → k y = none) (ho : ResultIs f o x) :
    ResultIs f (o.bind k) y ↔ ResultIs f (k x) y := by
  cases o with
  | none => simp [ResultIs] at ho; simp [ResultIs, hk x ho]
  | some r => simp [ResultIs] at ho; subst ho; rfl

/-- `abs` is the encoding with the sign cleared, a value below `2^width` for every input. -/
theorem abs_lt (f : Fmt) (x : Nat) : abs f x < f.signBit := Nat.mod_lt _ (Nat.two_pow_pos _)

end Janus.Float
