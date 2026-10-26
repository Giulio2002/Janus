import JanusASL.Proofs.FP.Value
import JanusASL.Proofs.Loop

/-! # `FPRoundBase` against Janus' `fpRound`: normalization loops, floors and rounding errors -/

namespace JanusASL.Proofs

theorem iter_dbl (n : Nat) (a : Int) (y : Rat) :
    iter (fun r : Int × Rat => (r.1 - 1, r.2 * 2)) n (a, y) = (a - n, y * 2 ^ (n : Int)) := by
  induction n generalizing a y with
  | zero => simp [iter]
  | succ n ih =>
    simp only [iter]; rw [ih]
    have h2 : (2 : Rat) ≠ 0 := by decide
    congr 1
    · omega
    · rw [Rat.mul_assoc, Rat.mul_comm 2, ← Rat.zpow_add_one h2]; congr 2

theorem iter_half (n : Nat) (a : Int) (y : Rat) :
    iter (fun r : Int × Rat => (r.1 + 1, r.2 / 2)) n (a, y) = (a + n, y * 2 ^ (-(n : Int))) := by
  induction n generalizing a y with
  | zero => simp [iter]
  | succ n ih =>
    simp only [iter]; rw [ih]
    have h2 : (2 : Rat) ≠ 0 := by decide
    congr 1
    · omega
    · rw [Rat.div_def, Rat.mul_assoc, show (2 : Rat)⁻¹ = 2 ^ (-1 : Int) by rfl, ← Rat.zpow_add h2]; congr 2; omega

end JanusASL.Proofs

namespace JanusASL.Proofs
open Lean.Order

theorem mag_lower (m : Nat) (hm : m ≠ 0) (k : Int) :
    (2 : Rat) ^ ((Nat.log2 m : Int) + k) ≤ (m : Rat) * 2 ^ k := by
  have h1 : ((2 ^ Nat.log2 m : Nat) : Rat) ≤ (m : Rat) := Rat.natCast_le_natCast.mpr (Nat.log2_self_le hm)
  rw [Rat.natCast_pow, Rat.natCast_ofNat, ← Rat.zpow_natCast] at h1
  rw [Rat.zpow_add two_ne_zero_rat]
  exact Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (Rat.zpow_pos two_pos_rat))

theorem mag_upper (m : Nat) (k : Int) :
    (m : Rat) * 2 ^ k < (2 : Rat) ^ ((Nat.log2 m : Int) + 1 + k) := by
  have h1 : (m : Rat) < ((2 ^ (Nat.log2 m + 1) : Nat) : Rat) := Rat.natCast_lt_natCast.mpr Nat.lt_log2_self
  rw [Rat.natCast_pow, Rat.natCast_ofNat, ← Rat.zpow_natCast] at h1
  rw [Rat.zpow_add two_ne_zero_rat]
  have : ((Nat.log2 m + 1 : Nat) : Int) = (Nat.log2 m : Int) + 1 := by omega
  rw [this] at h1
  exact Rat.mul_lt_mul_of_pos_right h1 (Rat.zpow_pos two_pos_rat)

theorem loop_dbl {mo : Type → Type} [Monad mo] [LawfulMonad mo] [MonadTail mo]
    (f : Unit → Int × Rat → mo (ForInStep (Int × Rat)))
    (hf : ∀ r, f () r = pure (if decide (r.2 < 1) then .yield (r.1 - 1, r.2 * 2) else .done r))
    (x : Rat) (n : Nat) (hlt : ∀ i < n, x * 2 ^ (i : Int) < 1) (hge : ¬ x * 2 ^ (n : Int) < 1) :
    forIn Lean.Loop.mk ((0 : Int), x) f = pure (-(n : Int), x * 2 ^ (n : Int)) := by
  have := forIn_loop_pure (fun r : Int × Rat => decide (r.2 < 1)) (fun r => (r.1 - 1, r.2 * 2)) f hf n (0, x)
    (fun i hi => by rw [iter_dbl]; simpa using hlt i hi) (by rw [iter_dbl]; simpa using hge)
  rw [this, iter_dbl]; congr 2; omega

theorem loop_half {mo : Type → Type} [Monad mo] [LawfulMonad mo] [MonadTail mo]
    (f : Unit → Int × Rat → mo (ForInStep (Int × Rat)))
    (hf : ∀ r, f () r = pure (if decide (2 ≤ r.2) then .yield (r.1 + 1, r.2 / 2) else .done r))
    (a : Int) (x : Rat) (n : Nat) (hge : ∀ i < n, 2 ≤ x * 2 ^ (-(i : Int))) (hlt : ¬ 2 ≤ x * 2 ^ (-(n : Int))) :
    forIn Lean.Loop.mk (a, x) f = pure (a + n, x * 2 ^ (-(n : Int))) := by
  have := forIn_loop_pure (fun r : Int × Rat => decide (2 ≤ r.2)) (fun r => (r.1 + 1, r.2 / 2)) f hf n (a, x)
    (fun i hi => by rw [iter_half]; simpa using hge i hi) (by rw [iter_half]; simpa using hlt)
  rw [this, iter_half]

end JanusASL.Proofs

namespace JanusASL.Proofs
open Lean.Order

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c :=
  Rat.not_le.mp fun hca => (Rat.not_le.mpr h1) (Rat.le_trans h2 hca)

theorem rat_lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c :=
  Rat.not_le.mp fun hca => (Rat.not_le.mpr h2) (Rat.le_trans hca h1)

theorem zpow_lt_zpow {a b : Int} (h : a < b) : (2 : Rat) ^ a < (2 : Rat) ^ b := by
  have hp : (0 : Rat) < 2 ^ a := Rat.zpow_pos two_pos_rat
  have h1 : (2 : Rat) ^ a < 2 ^ (a + 1) := by
    rw [Rat.zpow_add_one two_ne_zero_rat]
    have := Rat.mul_lt_mul_of_pos_left (show (1 : Rat) < 2 by decide) hp
    rwa [Rat.mul_one] at this
  exact rat_lt_of_lt_of_le h1 (zpow_le_zpow (by omega))

/-- The normalization loops of `FPRoundBase` on `x = m * 2^e` (`m > 0`): exponent `X = log2 m + e`,
mantissa `m * 2^(-log2 m)` (in `[1, 2)`). -/
theorem norm_counts (m : Nat) (hm : m ≠ 0) (e : Int) :
    let X := (Nat.log2 m : Int) + e
    (∀ i < (-X).toNat, (m : Rat) * 2 ^ e * 2 ^ (i : Int) < 1) ∧ ¬ ((m : Rat) * 2 ^ e * 2 ^ ((-X).toNat : Int) < 1) ∧
    (∀ i < X.toNat, 2 ≤ (m : Rat) * 2 ^ e * 2 ^ ((-X).toNat : Int) * 2 ^ (-(i : Int))) ∧
    ¬ (2 ≤ (m : Rat) * 2 ^ e * 2 ^ ((-X).toNat : Int) * 2 ^ (-(X.toNat : Int))) := by
  intro X
  have rw2 : ∀ a b : Int, (m : Rat) * 2 ^ a * 2 ^ b = (m : Rat) * 2 ^ (a + b) := fun a b => by
    rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
  refine ⟨fun i hi => ?_, ?_, fun i hi => ?_, ?_⟩
  · rw [rw2]
    exact rat_lt_of_lt_of_le (mag_upper m _) (by
      rw [show (1 : Rat) = 2 ^ (0 : Int) by rfl]; exact zpow_le_zpow (by omega))
  · rw [rw2]; intro hlt
    have := rat_lt_of_le_of_lt (mag_lower m hm _) hlt
    rw [show (1 : Rat) = 2 ^ (0 : Int) by rfl] at this
    exact (Rat.not_le.mpr this) (zpow_le_zpow (by omega))
  · rw [rw2, rw2]
    exact Rat.le_trans (by rw [show (2 : Rat) = 2 ^ (1 : Int) by rfl]; exact zpow_le_zpow (by omega)) (mag_lower m hm _)
  · rw [rw2, rw2]; intro hge
    have := rat_lt_of_le_of_lt hge (mag_upper m _)
    rw [show (2 : Rat) = 2 ^ (1 : Int) by rfl] at this
    exact (Rat.not_le.mpr this) (zpow_le_zpow (by omega))

end JanusASL.Proofs

namespace JanusASL.Proofs


/-- `m * 2^(-s) = m / 2^s + (m % 2^s) * 2^(-s)`. -/
theorem split_div (m s : Nat) :
    (m : Rat) * 2 ^ (-(s : Int)) = ((m / 2 ^ s : Nat) : Rat) + ((m % 2 ^ s : Nat) : Rat) * 2 ^ (-(s : Int)) := by
  have hm : m = 2 ^ s * (m / 2 ^ s) + m % 2 ^ s := (Nat.div_add_mod m (2 ^ s)).symm
  conv => lhs; rw [hm]
  rw [Rat.natCast_add, Rat.natCast_mul, Rat.add_mul, Rat.natCast_pow, Rat.natCast_ofNat, Rat.mul_comm ((2:Rat) ^ s),
    Rat.mul_assoc, ← Rat.zpow_natCast, ← Rat.zpow_add two_ne_zero_rat, Int.add_right_neg, Rat.zpow_zero, Rat.mul_one]

theorem frac_lt_one (r s : Nat) (hr : r < 2 ^ s) : (r : Rat) * 2 ^ (-(s : Int)) < 1 := by
  have h1 : (r : Rat) < (2 : Rat) ^ (s : Int) := by
    rw [Rat.zpow_natCast]; have := Rat.natCast_lt_natCast.mpr hr; rwa [Rat.natCast_pow, Rat.natCast_ofNat] at this
  have := Rat.mul_lt_mul_of_pos_right h1 (Rat.zpow_pos (n := -(s : Int)) two_pos_rat)
  rwa [← Rat.zpow_add two_ne_zero_rat, Int.add_right_neg, Rat.zpow_zero] at this

theorem frac_nonneg (r s : Nat) : (0 : Rat) ≤ (r : Rat) * 2 ^ (-(s : Int)) :=
  Rat.mul_nonneg (Rat.natCast_nonneg) (Rat.le_of_lt (Rat.zpow_pos two_pos_rat))

theorem floor_frac (r s : Nat) (hr : r < 2 ^ s) : ((r : Rat) * 2 ^ (-(s : Int))).floor = 0 := by
  apply Int.le_antisymm
  · have := Rat.floor_lt_iff.mpr (show (r : Rat) * 2 ^ (-(s : Int)) < ((1 : Int) : Rat) from by
      rw [Rat.intCast_one]; exact frac_lt_one r s hr)
    omega
  · exact Rat.le_floor_iff.mpr (by rw [Rat.intCast_zero]; exact frac_nonneg r s)

theorem floor_div (m s : Nat) : ((m : Rat) * 2 ^ (-(s : Int))).floor = ((m / 2 ^ s : Nat) : Int) := by
  rw [split_div, Rat.add_comm, show (((m / 2 ^ s : Nat) : Rat)) = (((m / 2 ^ s : Nat) : Int) : Rat) by
    rw [Rat.intCast_natCast], Rat.floor_add_intCast, floor_frac _ _ (Nat.mod_lt _ (Nat.two_pow_pos s)), Int.zero_add]

theorem scale_back (r s : Nat) : (r : Rat) * 2 ^ (-(s : Int)) * 2 ^ (s : Int) = r := by
  rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat, Int.add_left_neg, Rat.zpow_zero, Rat.mul_one]

theorem half_scale (s : Nat) : (1 / 2 : Rat) * 2 ^ ((s : Int) + 1) = 2 ^ (s : Int) := by
  rw [Rat.zpow_add_one two_ne_zero_rat, Rat.mul_comm, Rat.mul_assoc, show (2 : Rat) * (1 / 2) = 1 by rw [Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ two_ne_zero_rat],
    Rat.mul_one]

theorem frac_scale (r s : Nat) : (r : Rat) * 2 ^ (-(s : Int)) * 2 ^ ((s : Int) + 1) = ((2 * r : Nat) : Rat) := by
  rw [Rat.zpow_add_one two_ne_zero_rat, ← Rat.mul_assoc, scale_back, Rat.natCast_mul, Rat.natCast_ofNat, Rat.mul_comm]

theorem half_lt_frac (r s : Nat) : ((1 / 2 : Rat) < (r : Rat) * 2 ^ (-(s : Int))) ↔ 2 ^ s < 2 * r := by
  rw [← Rat.mul_lt_mul_right (Rat.zpow_pos (n := (s : Int) + 1) two_pos_rat), half_scale, frac_scale,
    Rat.zpow_natCast, ← Rat.natCast_ofNat, ← Rat.natCast_pow, Rat.natCast_lt_natCast]

theorem frac_eq_half (r s : Nat) : ((r : Rat) * 2 ^ (-(s : Int)) = 1 / 2) ↔ 2 * r = 2 ^ s := by
  constructor
  · intro h
    have : (r : Rat) * 2 ^ (-(s : Int)) * 2 ^ ((s : Int) + 1) = 1 / 2 * 2 ^ ((s : Int) + 1) := by rw [h]
    rw [half_scale, frac_scale, Rat.zpow_natCast, ← Rat.natCast_ofNat, ← Rat.natCast_pow] at this
    exact Rat.natCast_inj.mp this
  · intro h
    have cancel : ∀ x : Rat, x = x * 2 ^ ((s : Int) + 1) * 2 ^ (-((s : Int) + 1)) := fun x => by
      rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat, Int.add_right_neg, Rat.zpow_zero, Rat.mul_one]
    rw [cancel ((r : Rat) * 2 ^ (-(s : Int))), cancel (1 / 2), half_scale, frac_scale, h, Rat.zpow_natCast,
      ← Rat.natCast_ofNat, ← Rat.natCast_pow]

theorem frac_ne_zero (r s : Nat) : ((r : Rat) * 2 ^ (-(s : Int)) ≠ 0) ↔ r ≠ 0 := by
  constructor
  · intro h hr; apply h; rw [hr]; simp
  · intro h e
    have := congrArg (· * (2 : Rat) ^ (s : Int)) e
    simp only [scale_back, Rat.zero_mul] at this
    exact h (Rat.natCast_eq_zero_iff.mp this)

end JanusASL.Proofs
