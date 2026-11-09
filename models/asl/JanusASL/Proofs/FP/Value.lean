import Janus.Arm64.Float

/-! # Janus' exact values as the ASL's `real` (`Rat`): comparisons and bounds -/

namespace JanusASL.Proofs

theorem two_ne_zero_rat : (2 : Rat) ≠ 0 := by decide
theorem two_pos_rat : (0 : Rat) < 2 := by decide

/-- `n * 2^e = (n * 2^(e-m)) * 2^m` for `m ≤ e`. -/
theorem num_split (n : Int) (e m : Int) (h : m ≤ e) :
    (n : Rat) * 2 ^ e = ((n * 2 ^ (e - m).toNat : Int) : Rat) * 2 ^ m := by
  rw [Rat.intCast_mul, Rat.intCast_pow, Rat.intCast_ofNat, Rat.mul_assoc, ← Rat.zpow_natCast,
    ← Rat.zpow_add two_ne_zero_rat]
  congr 2; omega

theorem align_lt (n e n' e' : Int) :
    decide ((Janus.Float.align n e n' e').1 < (Janus.Float.align n e n' e').2) =
      decide ((n : Rat) * 2 ^ e < (n' : Rat) * 2 ^ e') := by
  rw [decide_eq_decide]
  simp only [Janus.Float.align]
  rw [num_split n e (min e e') (Int.min_le_left _ _), num_split n' e' (min e e') (Int.min_le_right _ _),
    Rat.mul_lt_mul_right (Rat.zpow_pos two_pos_rat), Rat.intCast_lt_intCast]

theorem align_eq (n e n' e' : Int) :
    ((Janus.Float.align n e n' e').1 == (Janus.Float.align n e n' e').2) =
      decide ((n : Rat) * 2 ^ e = (n' : Rat) * 2 ^ e') := by
  simp only [Janus.Float.align]
  rw [num_split n e (min e e') (Int.min_le_left _ _), num_split n' e' (min e e') (Int.min_le_right _ _)]
  generalize n * 2 ^ (e - min e e').toNat = a
  generalize n' * 2 ^ (e' - min e e').toNat = b
  have hp : (0 : Rat) < 2 ^ (min e e') := Rat.zpow_pos two_pos_rat
  by_cases h : a = b
  · subst h; simp
  · have : ¬ ((a : Rat) * 2 ^ min e e' = (b : Rat) * 2 ^ min e e') := by
      intro hab
      rcases Int.lt_or_gt_of_ne h with hl | hl
      · have := (Rat.mul_lt_mul_right hp).mpr (Rat.intCast_lt_intCast.mpr hl); rw [hab] at this
        exact Rat.lt_irrefl this
      · have := (Rat.mul_lt_mul_right hp).mpr (Rat.intCast_lt_intCast.mpr hl); rw [hab] at this
        exact Rat.lt_irrefl this
    simp [h, this]

end JanusASL.Proofs

namespace JanusASL.Proofs

theorem one_le_two_pow (k : Nat) : (1 : Rat) ≤ (2 : Rat) ^ k := by
  have : ((1 : Nat) : Rat) ≤ ((2 ^ k : Nat) : Rat) := Rat.natCast_le_natCast.mpr (Nat.one_le_two_pow)
  rw [Rat.natCast_pow] at this; simpa using this

theorem zpow_le_zpow {a b : Int} (h : a ≤ b) : (2 : Rat) ^ a ≤ (2 : Rat) ^ b := by
  have e : (2 : Rat) ^ b = 2 ^ a * 2 ^ (b - a).toNat := by
    rw [← Rat.zpow_natCast, ← Rat.zpow_add two_ne_zero_rat]; congr 1; omega
  rw [e]
  have h1 := Rat.mul_le_mul_of_nonneg_left (one_le_two_pow (b - a).toNat) (Rat.le_of_lt (Rat.zpow_pos (n := a) two_pos_rat))
  rw [Rat.mul_one] at h1; exact h1

/-- A finite value bound: `|n * 2^e| < 2^1000000` when `|n| < 2^64` and `e ≤ 2^16`. -/
theorem num_lt_big (n e : Int) (hn : n.natAbs < 2 ^ 64) (he : e ≤ 65536) :
    (n : Rat) * 2 ^ e < (2 : Rat) ^ (1000000 : Int) := by
  have hn' : (n : Rat) < (2 : Rat) ^ (64 : Int) := by
    have : n < 2 ^ 64 := by omega
    have := Rat.intCast_lt_intCast.mpr this
    rw [Rat.intCast_pow, Rat.intCast_ofNat] at this
    rwa [show ((2 : Rat) ^ (64 : Int)) = 2 ^ (64 : Nat) from Rat.zpow_natCast 2 64]
  have hp : (0 : Rat) < 2 ^ e := Rat.zpow_pos two_pos_rat
  have h1 : (n : Rat) * 2 ^ e < (2 : Rat) ^ (64 + e) := by
    rw [Rat.zpow_add two_ne_zero_rat]; exact Rat.mul_lt_mul_of_pos_right hn' hp
  have h2 : (2 : Rat) ^ (64 + e) ≤ (2 : Rat) ^ (1000000 : Int) := zpow_le_zpow (by omega)
  exact Rat.not_le.mp fun hca => (Rat.not_le.mpr h1) (Rat.le_trans h2 hca)

theorem neg_big_lt_num (n e : Int) (hn : n.natAbs < 2 ^ 64) (he : e ≤ 65536) :
    -(2 : Rat) ^ (1000000 : Int) < (n : Rat) * 2 ^ e := by
  have := num_lt_big (-n) e (by omega) he
  rw [Rat.intCast_neg, Rat.neg_mul] at this
  exact Rat.neg_lt_iff.mpr this

end JanusASL.Proofs

namespace JanusASL.Proofs
open Janus.Float

/-- A Janus value as the ASL's `real` (infinities are `±2^1000000`, as in `FPUnpackBase`). -/
def valRat : Val → Rat
  | .num n e => (n : Rat) * 2 ^ e
  | .inf neg => if neg then -(2 : Rat) ^ (1000000 : Int) else (2 : Rat) ^ (1000000 : Int)

/-- Values small enough that `±2^1000000` stands for the infinities. -/
def Bnd : Val → Prop
  | .num n e => n.natAbs < 2 ^ 64 ∧ e ≤ 65536
  | .inf _ => True

theorem big_pos : (0 : Rat) < (2 : Rat) ^ (1000000 : Int) := Rat.zpow_pos two_pos_rat

theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c :=
  Rat.not_le.mp fun hca => (Rat.not_le.mpr h1) (Rat.le_trans (Rat.le_of_lt h2) hca)

theorem neg_big_lt_big : -(2 : Rat) ^ (1000000 : Int) < (2 : Rat) ^ (1000000 : Int) := by
  have h0 : -(2 : Rat) ^ (1000000 : Int) < 0 := by
    have := Rat.neg_lt_neg big_pos; rwa [Rat.neg_zero] at this
  exact rat_lt_trans h0 big_pos

theorem val_lt (v w : Val) (hv : Bnd v) (hw : Bnd w) : Val.lt v w = decide (valRat v < valRat w) := by
  have hnb := neg_big_lt_big
  have nlt : ∀ {a b : Rat}, a < b → ¬ b < a := fun h h' => Rat.lt_irrefl (rat_lt_trans h h')
  rcases v with ⟨n, e⟩ | s1 <;> rcases w with ⟨n', e'⟩ | s2
  · exact align_lt _ _ _ _
  · have h1 := num_lt_big n e hv.1 hv.2
    have h2 := neg_big_lt_num n e hv.1 hv.2
    cases s2 <;> simp [Val.lt, valRat, h1, nlt h2]
  · have h1 := num_lt_big n' e' hw.1 hw.2
    have h2 := neg_big_lt_num n' e' hw.1 hw.2
    cases s1 <;> simp [Val.lt, valRat, h2, nlt h1]
  · cases s1 <;> cases s2 <;> simp [Val.lt, valRat, hnb, nlt hnb, Rat.lt_irrefl]

theorem val_eq (v w : Val) (hv : Bnd v) (hw : Bnd w) : Val.eq v w = decide (valRat v = valRat w) := by
  have hnb := neg_big_lt_big
  have ne_of_lt' : ∀ {a b : Rat}, a < b → a ≠ b := fun h e => Rat.lt_irrefl (e ▸ h)
  rcases v with ⟨n, e⟩ | s1 <;> rcases w with ⟨n', e'⟩ | s2
  · exact align_eq _ _ _ _
  · have h1 := num_lt_big n e hv.1 hv.2
    have h2 := neg_big_lt_num n e hv.1 hv.2
    cases s2 <;> simp [Val.eq, valRat, ne_of_lt' h1, (ne_of_lt' h2).symm]
  · have h1 := num_lt_big n' e' hw.1 hw.2
    have h2 := neg_big_lt_num n' e' hw.1 hw.2
    cases s1 <;> simp [Val.eq, valRat, (ne_of_lt' h1).symm, ne_of_lt' h2]
  · cases s1 <;> cases s2 <;> simp [Val.eq, valRat, ne_of_lt' hnb, (ne_of_lt' hnb).symm]

end JanusASL.Proofs

namespace JanusASL.Proofs
open Janus.Float

theorem bnd_valueOf (f : Fmt) (hf : f = binary32 ∨ f = binary64) (x : Nat) : Bnd (valueOf f x) := by
  unfold valueOf
  split
  · trivial
  · simp [Bnd]
  · simp [Bnd]
  · simp [Bnd]
  · simp only [Bnd]
    have hm : mantOf f x < 2 ^ 53 := by
      rcases hf with rfl | rfl <;> simp only [mantOf, fracOf, expOf, binary32, binary64]
      · by_cases h : x / 2 ^ 23 % 2 ^ 8 = 0 <;> simp [h] <;> omega
      · by_cases h : x / 2 ^ 52 % 2 ^ 11 = 0 <;> simp [h] <;> omega
    have he : ulpExpOf f x ≤ 65536 := by
      rcases hf with rfl | rfl <;> simp only [ulpExpOf, expOf, binary32, binary64, Fmt.emin, Fmt.bias]
      · by_cases h : x / 2 ^ 23 % 2 ^ 8 = 0 <;> simp [h] <;> omega
      · by_cases h : x / 2 ^ 52 % 2 ^ 11 = 0 <;> simp [h] <;> omega
    constructor
    · split <;> simp <;> omega
    · omega

theorem bnd_unpack (f : Fmt) (hf : f = binary32 ∨ f = binary64) (fpcr : Nat) (e : Bool) (x : Nat) :
    Bnd (Janus.Arm64.FP.unpack f fpcr e x).1.2.2 := by
  have hb := bnd_valueOf f hf x
  unfold Janus.Arm64.FP.unpack
  split
  · simp [Bnd]
  · cases Janus.Arm64.FP.fz fpcr <;> cases Janus.Arm64.FP.ah fpcr <;> cases Janus.Arm64.FP.fiz fpcr <;>
      simp [Bnd] <;> exact hb
  · exact hb
  · trivial
  · simp [Bnd]
  · simp [Bnd]

end JanusASL.Proofs
