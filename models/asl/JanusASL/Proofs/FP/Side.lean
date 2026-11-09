import JanusASL.Proofs.FP.RoundQ
import JanusASL.Proofs.FP.RoundQ64

/-! # Rounding depends only on which side of the lattice points a value lies

`Side g a b`: `a` and `b` lie on the same side of every point `n * 2^g`, and equal one exactly when the other does.
Every observable of `FPRoundBase` (the binade, the scaled floors, whether an error is zero, above or equal to a half)
is a comparison with a lattice point, so two positive operands that are `Side`-equivalent on a lattice finer than
half a unit in the last place round identically (`rbq32_side`, `rbq64_side`). -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem mul_cancel_pos {a b c : Rat} (hp : 0 < c) (h : a * c = b * c) : a = b :=
  Rat.le_antisymm (Rat.le_of_mul_le_mul_right (h ▸ Rat.le_refl) hp) (Rat.le_of_mul_le_mul_right (h ▸ Rat.le_refl) hp)

def Side (g : Int) (a b : Rat) : Prop :=
  ∀ n : Int, (a < (n : Rat) * 2 ^ g ↔ b < (n : Rat) * 2 ^ g) ∧ (a = (n : Rat) * 2 ^ g ↔ b = (n : Rat) * 2 ^ g)

theorem Side.refl (g : Int) (a : Rat) : Side g a a := fun _ => ⟨Iff.rfl, Iff.rfl⟩

theorem Side.symm {g : Int} {a b : Rat} (h : Side g a b) : Side g b a := fun n => ⟨(h n).1.symm, (h n).2.symm⟩

theorem Side.trans {g : Int} {a b c : Rat} (h1 : Side g a b) (h2 : Side g b c) : Side g a c :=
  fun n => ⟨(h1 n).1.trans (h2 n).1, (h1 n).2.trans (h2 n).2⟩

/-- A finer lattice's points include the coarser one's: `Side g` implies `Side u` for `g ≤ u`. -/
theorem Side.mono {g u : Int} (hgu : g ≤ u) {a b : Rat} (h : Side g a b) : Side u a b := by
  intro n
  have e : (n : Rat) * 2 ^ u = ((n * 2 ^ (u - g).toNat : Int) : Rat) * 2 ^ g := num_split n u g hgu
  rw [e]; exact h _

/-- Shifting by `2^x` shifts the lattice. -/
theorem Side.scale {g : Int} {a b : Rat} (h : Side g a b) (x : Int) : Side (g + x) (a * 2 ^ x) (b * 2 ^ x) := by
  intro n
  have hp : (0 : Rat) < 2 ^ x := rat_pos_zpow x
  have e : (n : Rat) * 2 ^ (g + x) = ((n : Rat) * 2 ^ g) * 2 ^ x := by
    rw [Rat.zpow_add two_ne_zero_rat, Rat.mul_assoc]
  rw [e, Rat.mul_lt_mul_right hp, Rat.mul_lt_mul_right hp]
  refine ⟨(h n).1, ?_⟩
  constructor
  · intro h1
    have := (h n).2.mp (mul_cancel_pos hp h1)
    rw [this]
  · intro h1
    have := (h n).2.mpr (mul_cancel_pos hp h1)
    rw [this]

theorem lattice_pt (z : Int) (u g : Int) (h : g ≤ u) : (z : Rat) * 2 ^ u = ((z * 2 ^ (u - g).toNat : Int) : Rat) * 2 ^ g :=
  num_split z u g h

theorem pow_lattice (E g : Int) (h : g ≤ E) : (2 : Rat) ^ E = (((2 ^ (E - g).toNat : Nat) : Int) : Rat) * 2 ^ g := by
  have := num_split 1 E g h
  simpa using this

/-- The binade is determined by the side of the lattice points. -/
theorem Side.binade {g : Int} {a b : Rat} (h : Side g a b) {E : Int} (hg : g ≤ E)
    (h1 : (2 : Rat) ^ E ≤ a) (h2 : a < (2 : Rat) ^ (E + 1)) : (2 : Rat) ^ E ≤ b ∧ b < (2 : Rat) ^ (E + 1) := by
  constructor
  · rw [pow_lattice E g hg]
    have := (h (((2 ^ (E - g).toNat : Nat) : Int))).1
    rw [pow_lattice E g hg] at h1
    exact Rat.not_lt.mp (fun hb => (Rat.not_lt.mpr h1) (this.mpr hb))
  · rw [pow_lattice (E + 1) g (by omega)]
    rw [pow_lattice (E + 1) g (by omega)] at h2
    exact ((h _).1).mp h2

/-- `z ≤ ⌊a * 2^d⌋` iff the lattice point `z * 2^(-d)` is not above `a`. -/
theorem le_floor_scaled (a : Rat) (d z : Int) :
    z ≤ round_down (a * 2 ^ d) ↔ ¬ a < (z : Rat) * 2 ^ (-d) := by
  simp only [round_down]
  rw [Rat.le_floor_iff, Rat.not_lt]
  have hp : (0 : Rat) < 2 ^ d := rat_pos_zpow d
  have e : (z : Rat) * 2 ^ (-d) * 2 ^ d = z := by
    rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat, Int.add_left_neg, Rat.zpow_zero, Rat.mul_one]
  constructor
  · intro h
    have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_pos_zpow (-d)))
    rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat, Int.add_right_neg, Rat.zpow_zero, Rat.mul_one] at this
    exact this
  · intro h
    have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hp)
    rwa [e] at this

theorem Side.floor {g : Int} {a b : Rat} (h : Side g a b) (d : Int) (hd : g ≤ -d) :
    round_down (a * 2 ^ d) = round_down (b * 2 ^ d) := by
  have key : ∀ z : Int, z ≤ round_down (a * 2 ^ d) ↔ z ≤ round_down (b * 2 ^ d) := fun z => by
    rw [le_floor_scaled, le_floor_scaled]
    have := (Side.mono hd h) z
    exact not_congr this.1
  exact Int.le_antisymm ((key (round_down (a * 2 ^ d))).mp (Int.le_refl _))
    ((key (round_down (b * 2 ^ d))).mpr (Int.le_refl _))

theorem scaled_lt (a t : Rat) (d : Int) : a * 2 ^ d < t ↔ a < t * 2 ^ (-d) := by
  have hp : (0 : Rat) < 2 ^ (-d) := rat_pos_zpow _
  have e : a * 2 ^ d * 2 ^ (-d) = a := by
    rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat, Int.add_right_neg, Rat.zpow_zero, Rat.mul_one]
  rw [← Rat.mul_lt_mul_right hp, e]

theorem scaled_eq (a t : Rat) (d : Int) : a * 2 ^ d = t ↔ a = t * 2 ^ (-d) := by
  have hp : (0 : Rat) < 2 ^ (-d) := rat_pos_zpow _
  have e : a * 2 ^ d * 2 ^ (-d) = a := by
    rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat, Int.add_right_neg, Rat.zpow_zero, Rat.mul_one]
  constructor
  · intro h; rw [← e, h]
  · intro h; exact mul_cancel_pos hp (by rw [e, h])

theorem two_mul_inv : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 two_ne_zero_rat

theorem half_pt (z d : Int) : ((z : Rat) + (2 : Rat)⁻¹) * 2 ^ (-d) = ((2 * z + 1 : Int) : Rat) * 2 ^ (-d - 1) := by
  rw [Rat.zpow_sub_one two_ne_zero_rat]
  generalize (2 : Rat) ^ (-d) = P
  rw [Rat.intCast_add, Rat.intCast_mul, Rat.add_mul, Rat.add_mul]
  have h2 : ((2 : Int) : Rat) = 2 := rfl
  have h1 : ((1 : Int) : Rat) = 1 := rfl
  rw [h2, h1]
  have : (2 : Rat) * (z : Rat) * (P * (2 : Rat)⁻¹) = (z : Rat) * P := by
    calc (2 : Rat) * (z : Rat) * (P * (2 : Rat)⁻¹) = (z : Rat) * P * (2 * (2 : Rat)⁻¹) := by
          rw [Rat.mul_comm 2 (z : Rat), Rat.mul_assoc (z : Rat) 2, ← Rat.mul_assoc 2 P, Rat.mul_comm 2 P,
            Rat.mul_assoc P 2, ← Rat.mul_assoc (z : Rat) P]
      _ = (z : Rat) * P := by rw [two_mul_inv, Rat.mul_one]
  rw [this, Rat.one_mul, Rat.mul_comm P]

/-- The observable of an error: zero, above a half, equal to a half. -/
def ObsEq (e e' : Rat) : Prop := (e = 0 ↔ e' = 0) ∧ (1 / 2 < e ↔ 1 / 2 < e') ∧ (e = 1 / 2 ↔ e' = 1 / 2)

theorem sub_eq_zero_iff' (x z : Rat) : x - z = 0 ↔ x = z := by
  constructor
  · intro h
    have := Rat.sub_add_cancel (a := x) (b := z)
    rw [h, Rat.zero_add] at this
    exact this.symm
  · intro h; rw [h]; exact Rat.sub_self

theorem sub_eq_half_iff (x z : Rat) : x - z = (2 : Rat)⁻¹ ↔ x = (2 : Rat)⁻¹ + z := by
  constructor
  · intro h
    have := Rat.sub_add_cancel (a := x) (b := z)
    rw [h] at this
    exact this.symm
  · intro h; rw [h, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]

theorem Side.err {g : Int} {a b : Rat} (h : Side g a b) (d : Int) (hd : g + 1 ≤ -d) :
    ObsEq (sub_real (a * 2 ^ d) (to_real (round_down (a * 2 ^ d))))
      (sub_real (b * 2 ^ d) (to_real (round_down (b * 2 ^ d)))) := by
  have hf := h.floor d (by omega)
  rw [← hf]
  generalize round_down (a * 2 ^ d) = z
  simp only [sub_real, to_real]
  have hz : ((Rat.ofInt z : Rat)) = (z : Rat) := rfl
  rw [hz]
  have hh : (1 : Rat) / 2 = (2 : Rat)⁻¹ := by rw [Rat.div_def, Rat.one_mul]
  unfold ObsEq
  rw [hh]
  have p1 : Side (-d) a b := Side.mono (by omega) h
  have p2 : Side (-d - 1) a b := Side.mono (by omega) h
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_eq_zero_iff', sub_eq_zero_iff', scaled_eq, scaled_eq]
    exact (p1 z).2
  · rw [Rat.lt_sub_right_iff_add_lt, Rat.lt_sub_right_iff_add_lt, Rat.add_comm (2 : Rat)⁻¹ (z : Rat)]
    have e : ((z : Rat) + (2 : Rat)⁻¹) * 2 ^ (-d) = ((2 * z + 1 : Int) : Rat) * 2 ^ (-d - 1) := half_pt z d
    have key : ∀ y : Rat, ((z : Rat) + (2 : Rat)⁻¹ < y * 2 ^ d ↔
        ¬ y < ((2 * z + 1 : Int) : Rat) * 2 ^ (-d - 1) ∧ ¬ y = ((2 * z + 1 : Int) : Rat) * 2 ^ (-d - 1)) := fun y => by
      rw [← e, ← scaled_lt, ← scaled_eq]
      constructor
      · intro hlt
        exact ⟨fun h' => Rat.lt_irrefl (rat_lt_trans hlt h'), fun h' => Rat.lt_irrefl (h' ▸ hlt)⟩
      · rintro ⟨h1, h2⟩
        have h4 : (z : Rat) + (2 : Rat)⁻¹ ≤ y * 2 ^ d := Rat.not_lt.mp h1
        exact Rat.not_le.mp (fun h5 => h2 (Rat.le_antisymm h5 h4))
    rw [key a, key b]
    exact and_congr (not_congr (p2 (2 * z + 1)).1) (not_congr (p2 (2 * z + 1)).2)
  · rw [sub_eq_half_iff, sub_eq_half_iff, Rat.add_comm (2 : Rat)⁻¹ (z : Rat), scaled_eq, scaled_eq]
    have e : ((z : Rat) + (2 : Rat)⁻¹) * 2 ^ (-d) = ((2 * z + 1 : Int) : Rat) * 2 ^ (-d - 1) := half_pt z d
    rw [e]
    exact (p2 (2 * z + 1)).2

theorem ObsEq.bne {e e' : Rat} (h : ObsEq e e') : (e != 0) = (e' != 0) := by
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq]
  exact not_congr h.1

theorem ObsEq.gt {e e' : Rat} (h : ObsEq e e') : gt_real e (1 / 2) = gt_real e' (1 / 2) := by
  simp only [gt_real, gt_iff_lt]; exact decide_eq_decide.mpr h.2.1

theorem ObsEq.eq {e e' : Rat} (h : ObsEq e e') : eq_real e (1 / 2) = eq_real e' (1 / 2) := by
  simp only [eq_real]
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  exact h.2.2

theorem ObsEq.ru {e e' : Rat} (h : ObsEq e e') (rm : Janus.Float.RM) (neg : Bool) (A : Int) :
    rbRU rm neg e A = rbRU rm neg e' A := by
  unfold rbRU
  cases rm <;> simp [h.gt, h.eq, h.bne]

theorem ObsEq.ite_bne {e e' : Rat} (h : ObsEq e e') (c : Prop) [Decidable c] :
    ((if c then (1 : Rat) else e) != 0) = ((if c then (1 : Rat) else e') != 0) := by
  split <;> simp [h.bne]

theorem rb32_congr (ah fz ufe : Bool) (rm : Janus.Float.RM) (neg : Bool) (E A Au : Int) {Er Er' Eu Eu' : Rat}
    (h1 : ObsEq Er Er') (h2 : ObsEq Eu Eu') :
    rb32 ah fz ufe rm neg E A Au Er Eu = rb32 ah fz ufe rm neg E A Au Er' Eu' := by
  unfold rb32 rbTiny
  simp only [h1.bne, h1.ru, h2.ru, h1.ite_bne]

theorem rb64_congr (ah fz ufe : Bool) (rm : Janus.Float.RM) (neg : Bool) (E A Au : Int) {Er Er' Eu Eu' : Rat}
    (h1 : ObsEq Er Er') (h2 : ObsEq Eu Eu') :
    rb64 ah fz ufe rm neg E A Au Er Eu = rb64 ah fz ufe rm neg E A Au Er' Eu' := by
  unfold rb64 rbTiny64
  simp only [h1.bne, h1.ru, h2.ru, h1.ite_bne]

theorem rbq32_side (fpcr : Nat) (rm : Janus.Float.RM) (neg : Bool) {q d : Rat} {g E : Int} (hS : Side g q d)
    (hg : g + 24 ≤ E) : rbq32 fpcr rm neg q E = rbq32 fpcr rm neg d E := by
  unfold rbq32
  have f1 := hS.floor (23 - max E (-126)) (by omega)
  have f2 := hS.floor (23 - E) (by omega)
  have e1 := hS.err (23 - max E (-126)) (by omega)
  have e2 := hS.err (23 - E) (by omega)
  rw [f1] at e1
  rw [f2] at e2
  rw [f1, f2]
  exact rb32_congr _ _ _ _ _ _ _ _ e1 e2

theorem rbq64_side (fpcr : Nat) (rm : Janus.Float.RM) (neg : Bool) {q d : Rat} {g E : Int} (hS : Side g q d)
    (hg : g + 53 ≤ E) : rbq64 fpcr rm neg q E = rbq64 fpcr rm neg d E := by
  unfold rbq64
  have f1 := hS.floor (52 - max E (-1022)) (by omega)
  have f2 := hS.floor (52 - E) (by omega)
  have e1 := hS.err (52 - max E (-1022)) (by omega)
  have e2 := hS.err (52 - E) (by omega)
  rw [f1] at e1
  rw [f2] at e2
  rw [f1, f2]
  exact rb64_congr _ _ _ _ _ _ _ _ e1 e2

end JanusASL.Proofs
