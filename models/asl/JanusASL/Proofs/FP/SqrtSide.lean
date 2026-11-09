import JanusASL.Proofs.FP.Isqrt
import JanusASL.Proofs.FP.DivSide

/-! # The square root: Janus' round-to-odd root and the generated model's `sqrt_real` are on the same side of the lattice

`RootSide g x a`: `a > 0` is on the same side of every lattice point `t = n * 2^g > 0` as `√x`, i.e.
`a < t ↔ x < t²` and `a = t ↔ x = t²`. Two `RootSide` values are `Side`-equivalent. -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

def RootSide (g : Int) (x a : Rat) : Prop :=
  0 < a ∧ ∀ n : Int, 0 < (n : Rat) * 2 ^ g →
    (a < (n : Rat) * 2 ^ g ↔ x < ((n : Rat) * 2 ^ g) * ((n : Rat) * 2 ^ g)) ∧
    (a = (n : Rat) * 2 ^ g ↔ x = ((n : Rat) * 2 ^ g) * ((n : Rat) * 2 ^ g))

theorem RootSide.side {g : Int} {x a b : Rat} (h1 : RootSide g x a) (h2 : RootSide g x b) : Side g a b := by
  intro n
  by_cases hp : 0 < (n : Rat) * 2 ^ g
  · exact ⟨(h1.2 n hp).1.trans (h2.2 n hp).1.symm, (h1.2 n hp).2.trans (h2.2 n hp).2.symm⟩
  · have hn : (n : Rat) * 2 ^ g ≤ 0 := Rat.not_lt.mp hp
    have ha : ¬ a < (n : Rat) * 2 ^ g := Rat.not_lt.mpr (Rat.le_trans hn (Rat.le_of_lt h1.1))
    have hb : ¬ b < (n : Rat) * 2 ^ g := Rat.not_lt.mpr (Rat.le_trans hn (Rat.le_of_lt h2.1))
    have ha' : ¬ a = (n : Rat) * 2 ^ g := fun h => (Rat.not_lt.mpr hn) (h ▸ h1.1)
    have hb' : ¬ b = (n : Rat) * 2 ^ g := fun h => (Rat.not_lt.mpr hn) (h ▸ h2.1)
    exact ⟨⟨fun h => absurd h ha, fun h => absurd h hb⟩, ⟨fun h => absurd h ha', fun h => absurd h hb'⟩⟩

theorem pow_pos_rat (n : Nat) : (0 : Rat) < (2 : Rat) ^ n := by
  have := rat_pos_zpow (n : Int); rwa [Rat.zpow_natCast] at this

theorem natsq_cast (m : Nat) : (m : Rat) * (m : Rat) = ((m * m : Nat) : Rat) := (Rat.natCast_mul m m).symm

theorem natsq_succ_cast (m : Nat) : ((m : Rat) + 1) * ((m : Rat) + 1) = (((m + 1) * (m + 1) : Nat) : Rat) := by
  rw [Rat.natCast_mul, Rat.natCast_add]; rfl

theorem zcmp (m u : Nat) (z : Rat) (hlo : (m : Rat) * (m : Rat) ≤ z) (hhi : z < ((m : Rat) + 1) * ((m : Rat) + 1)) :
    (z < (u : Rat) * (u : Rat) ↔ m < u) ∧ (z = (u : Rat) * (u : Rat) ↔ (z = (m : Rat) * (m : Rat) ∧ m = u)) := by
  rw [natsq_cast] at hlo; rw [natsq_succ_cast] at hhi
  rw [natsq_cast u]
  constructor
  · constructor
    · intro h
      by_cases hmu : m < u
      · exact hmu
      · exfalso
        have h1 : u ≤ m := Nat.not_lt.mp hmu
        have h2 : u * u ≤ m * m := Nat.mul_self_le_mul_self_iff.mpr h1
        have h3 : ((u * u : Nat) : Rat) ≤ ((m * m : Nat) : Rat) := Rat.natCast_le_natCast.mpr h2
        exact (Rat.not_lt.mpr (Rat.le_trans h3 hlo)) h
    · intro h
      have h1 : (m + 1) * (m + 1) ≤ u * u := Nat.mul_self_le_mul_self_iff.mpr h
      have h3 : (((m + 1) * (m + 1) : Nat) : Rat) ≤ ((u * u : Nat) : Rat) := Rat.natCast_le_natCast.mpr h1
      exact rat_lt_of_lt_of_le hhi h3
  · constructor
    · intro h
      have hu1 : u < m + 1 := by
        by_cases hh : u < m + 1
        · exact hh
        · exfalso
          have h1 : m + 1 ≤ u := Nat.not_lt.mp hh
          have h2 : (m + 1) * (m + 1) ≤ u * u := Nat.mul_self_le_mul_self_iff.mpr h1
          have h3 : (((m + 1) * (m + 1) : Nat) : Rat) ≤ ((u * u : Nat) : Rat) := Rat.natCast_le_natCast.mpr h2
          exact (Rat.not_lt.mpr (h ▸ h3)) hhi
      have hmu : m ≤ u := by
        by_cases hh : m ≤ u
        · exact hh
        · exfalso
          have h1 : u < m := Nat.not_le.mp hh
          have h2 : u * u < m * m := Nat.mul_self_lt_mul_self_iff.mpr h1
          have h3 : ((u * u : Nat) : Rat) < ((m * m : Nat) : Rat) := Rat.natCast_lt_natCast.mpr h2
          exact (Rat.not_lt.mpr hlo) (h ▸ h3)
      have : m = u := by omega
      refine ⟨?_, this⟩
      rw [h, this]
      exact (natsq_cast u).symm
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      exact natsq_cast u

theorem four_pow (K : Nat) : (4 : Rat) ^ K = (2 : Rat) ^ K * (2 : Rat) ^ K := by
  have h : (4 : Nat) ^ K = 2 ^ K * 2 ^ K := by
    rw [← Nat.mul_pow]
  have := congrArg (fun n : Nat => (n : Rat)) h
  simpa [Rat.natCast_pow, Rat.natCast_mul] using this

theorem rootside_of_root (x : Rat) (hx : 0 < x) (K : Nat) (m : Nat) (hm : 0 < m) (g : Int) (hg : -(K : Int) ≤ g)
    (hlo : (m : Rat) * (m : Rat) ≤ x * 4 ^ K) (hhi : x * 4 ^ K < ((m : Rat) + 1) * ((m : Rat) + 1)) (a : Rat)
    (ha : (a = (m : Rat) / 2 ^ K ∧ (m : Rat) * (m : Rat) = x * 4 ^ K) ∨
      (a = ((2 * m + 1 : Nat) : Rat) / 2 ^ (K + 1) ∧ (m : Rat) * (m : Rat) < x * 4 ^ K)) :
    RootSide g x a := by
  have hK : (0 : Rat) < 2 ^ K := by
    have := rat_pos_zpow (K : Int); rwa [Rat.zpow_natCast] at this
  have hapos : 0 < a := by
    have hm' : (0 : Rat) < (m : Rat) := Rat.natCast_pos.mpr hm
    rcases ha with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h, Rat.div_def]; exact Rat.mul_pos hm' (Rat.inv_pos.mpr hK)
    · have h2 : (0 : Rat) < ((2 * m + 1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
      have hK1 : (0 : Rat) < 2 ^ (K + 1) := by
        have := rat_pos_zpow ((K + 1 : Nat) : Int); rwa [Rat.zpow_natCast] at this
      rw [h, Rat.div_def]; exact Rat.mul_pos h2 (Rat.inv_pos.mpr hK1)
  refine ⟨hapos, fun n hn => ?_⟩
  have hg2 : (0 : Rat) < 2 ^ g := rat_pos_zpow g
  have hnpos : 0 < n := by
    refine Classical.byContradiction fun hn0 => ?_
    have h0 : (n : Rat) ≤ 0 := by
      have : (n : Rat) ≤ ((0 : Int) : Rat) := Rat.intCast_le_intCast.mpr (by omega)
      simpa using this
    have := Rat.mul_le_mul_of_nonneg_right h0 (Rat.le_of_lt hg2)
    rw [Rat.zero_mul] at this
    exact (Rat.not_lt.mpr this) hn
  obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hnpos)
  have hcast : (((n' : Nat) : Int) : Rat) = (n' : Rat) := Rat.intCast_natCast n'
  rw [hcast] at hn ⊢
  generalize ht : (n' : Rat) * 2 ^ g = t at hn ⊢
  have hgK : 0 ≤ g + (K : Int) := by omega
  have hu : t * 2 ^ K = ((n' * 2 ^ (g + K).toNat : Nat) : Rat) := by
    rw [← ht, Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat, Rat.mul_assoc]
    congr 1
    rw [show ((2 : Rat) ^ K) = (2 : Rat) ^ (K : Int) from (Rat.zpow_natCast 2 K).symm, ← Rat.zpow_add two_ne_zero_rat]
    rw [show ((2 : Rat) ^ (g + K).toNat) = (2 : Rat) ^ (((g + K).toNat : Nat) : Int) from (Rat.zpow_natCast 2 _).symm]
    congr 1; omega
  generalize hU : n' * 2 ^ (g + K).toNat = u at hu
  have h4 : (0 : Rat) < 4 ^ K := by rw [four_pow]; exact Rat.mul_pos hK hK
  have hsq : t * t * 4 ^ K = (u : Rat) * (u : Rat) := by
    rw [four_pow, ← hu]
    have e1 : t * t * ((2 : Rat) ^ K * (2 : Rat) ^ K) = t * ((t * (2 : Rat) ^ K) * (2 : Rat) ^ K) := by
      rw [Rat.mul_assoc t t, ← Rat.mul_assoc t ((2 : Rat) ^ K)]
    have e2 : (t * (2 : Rat) ^ K) * (t * (2 : Rat) ^ K) = t * ((t * (2 : Rat) ^ K) * (2 : Rat) ^ K) := by
      rw [Rat.mul_assoc t ((2 : Rat) ^ K) (t * (2 : Rat) ^ K), ← Rat.mul_assoc ((2 : Rat) ^ K) t,
        Rat.mul_comm ((2 : Rat) ^ K) t]
    rw [e1, e2]
  have hxt : x < t * t ↔ x * 4 ^ K < (u : Rat) * (u : Rat) := by
    rw [← hsq, Rat.mul_lt_mul_right h4]
  have hxe : x = t * t ↔ x * 4 ^ K = (u : Rat) * (u : Rat) := by
    rw [← hsq]
    constructor
    · intro h; rw [h]
    · intro h; exact mul_cancel_pos h4 h
  obtain ⟨z1, z2⟩ := zcmp m u (x * 4 ^ K) hlo hhi
  rw [hxt, hxe, z1, z2]
  have hK1 : (0 : Rat) < 2 ^ (K + 1) := by
    have := rat_pos_zpow ((K + 1 : Nat) : Int); rwa [Rat.zpow_natCast] at this
  have hK1' : (2 : Rat) ^ (K + 1) = 2 * 2 ^ K := by
    rw [Rat.pow_succ, Rat.mul_comm]
  have ht2 : t * 2 ^ (K + 1) = ((2 * u : Nat) : Rat) := by
    rw [hK1', Rat.natCast_mul, Rat.natCast_ofNat, ← hu, ← Rat.mul_assoc, Rat.mul_comm t 2, Rat.mul_assoc]
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hax : a * 2 ^ K = (m : Rat) := by rw [h1]; exact Rat.div_mul_cancel (Rat.ne_of_gt hK)
    refine ⟨?_, ?_⟩
    · rw [← Rat.mul_lt_mul_right hK, hax, hu]; exact Rat.natCast_lt_natCast
    · constructor
      · intro h
        have : a * 2 ^ K = t * 2 ^ K := by rw [h]
        rw [hax, hu] at this
        exact ⟨h2.symm, Rat.natCast_inj.mp this⟩
      · rintro ⟨_, h⟩
        apply mul_cancel_pos hK
        rw [hax, hu, h]
  · have hax : a * 2 ^ (K + 1) = ((2 * m + 1 : Nat) : Rat) := by
      rw [h1]; exact Rat.div_mul_cancel (Rat.ne_of_gt hK1)
    refine ⟨?_, ?_⟩
    · rw [← Rat.mul_lt_mul_right hK1, hax, ht2]
      constructor
      · intro h; have := Rat.natCast_lt_natCast.mp h; omega
      · intro h; exact Rat.natCast_lt_natCast.mpr (by omega)
    · constructor
      · intro h
        have : a * 2 ^ (K + 1) = t * 2 ^ (K + 1) := by rw [h]
        rw [hax, ht2] at this
        have := Rat.natCast_inj.mp this
        omega
      · rintro ⟨h, _⟩
        exact absurd h.symm (Rat.ne_of_lt h2)

theorem rat_mul_den (x : Rat) : x * (x.den : Rat) = (x.num : Rat) := by
  have h := Rat.num_divInt_den x
  rw [Rat.divInt_eq_div] at h
  have hd : ((x.den : Int) : Rat) ≠ 0 := by
    rw [Rat.intCast_natCast]; exact Rat.ne_of_gt (Rat.natCast_pos.mpr x.den_pos)
  have h2 := Rat.div_mul_cancel (a := (x.num : Rat)) hd
  rw [h] at h2
  rw [Rat.intCast_natCast] at h2
  exact h2

theorem sqrt_real_rootside (x : Rat) (hx1 : 1 ≤ x * 4 ^ 1100) (g : Int) (hg : -1100 ≤ g) :
    RootSide g x (sqrt_real x) := by
  have h4 : (0 : Rat) < 4 ^ 1100 := by rw [four_pow]; exact Rat.mul_pos (pow_pos_rat 1100) (pow_pos_rat 1100)
  have hx : 0 < x := by
    refine Classical.byContradiction fun h => ?_
    have h0 : x ≤ 0 := Rat.not_lt.mp h
    have := Rat.mul_le_mul_of_nonneg_right h0 (Rat.le_of_lt h4)
    rw [Rat.zero_mul] at this
    have h1 : (0 : Rat) < 1 := by decide
    exact (Rat.not_lt.mpr this) (rat_lt_of_lt_of_le h1 hx1)
  have hxn : ¬ x ≤ 0 := Rat.not_le.mpr hx
  have hnum0 : 0 ≤ x.num := Rat.num_nonneg.mpr (Rat.le_of_lt hx)
  have hden : 0 < x.den := x.den_pos
  have hmd := rat_mul_den x
  -- N, D, y, m
  generalize hN : x.num.toNat = N
  have hNcast : (x.num : Rat) = (N : Rat) := by
    rw [← hN, ← Rat.intCast_natCast, Int.toNat_of_nonneg hnum0]
  rw [hNcast] at hmd
  unfold sqrt_real
  simp only [hxn, ite_false]
  rw [hN]
  generalize hD : x.den = D at hden hmd
  generalize hy : N * 4 ^ 1100 / D = y
  generalize hm : Nat.sqrt y = m
  have hDpos : (0 : Rat) < (D : Rat) := Rat.natCast_pos.mpr hden
  have hz : x * 4 ^ 1100 * (D : Rat) = ((N * 4 ^ 1100 : Nat) : Rat) := by
    rw [Rat.natCast_mul, Rat.natCast_pow, ← hmd]
    have h4' : ((4 : Nat) : Rat) = 4 := rfl
    rw [h4']
    rw [Rat.mul_assoc, Rat.mul_comm (4 ^ 1100 : Rat) (D : Rat), ← Rat.mul_assoc]
  have hdm := Nat.div_add_mod (N * 4 ^ 1100) D
  have hmod := Nat.mod_lt (N * 4 ^ 1100) hden
  rw [hy] at hdm
  have hy1 : D * y ≤ N * 4 ^ 1100 := by omega
  have hy2 : N * 4 ^ 1100 < D * (y + 1) := by rw [Nat.mul_add]; omega
  have hr1 : (y : Rat) ≤ x * 4 ^ 1100 := by
    have : ((D * y : Nat) : Rat) ≤ ((N * 4 ^ 1100 : Nat) : Rat) := Rat.natCast_le_natCast.mpr hy1
    rw [← hz, Rat.natCast_mul] at this
    rw [Rat.mul_comm (D : Rat)] at this
    exact Rat.le_of_mul_le_mul_right this hDpos
  have hr2 : x * 4 ^ 1100 < (y : Rat) + 1 := by
    have : ((N * 4 ^ 1100 : Nat) : Rat) < ((D * (y + 1) : Nat) : Rat) := Rat.natCast_lt_natCast.mpr hy2
    rw [← hz, Rat.natCast_mul, Rat.natCast_add] at this
    rw [Rat.mul_comm (D : Rat)] at this
    exact (Rat.mul_lt_mul_right hDpos).mp this
  have hm1 : m * m ≤ y := by rw [← hm]; exact Nat.sqrt_le y
  have hm2 : y < (m + 1) * (m + 1) := by rw [← hm]; exact Nat.lt_succ_sqrt y
  have hlo : (m : Rat) * (m : Rat) ≤ x * 4 ^ 1100 := by
    rw [natsq_cast]
    exact Rat.le_trans (Rat.natCast_le_natCast.mpr hm1) hr1
  have hhi : x * 4 ^ 1100 < ((m : Rat) + 1) * ((m : Rat) + 1) := by
    rw [natsq_succ_cast]
    have : ((y + 1 : Nat) : Rat) ≤ (((m + 1) * (m + 1) : Nat) : Rat) := Rat.natCast_le_natCast.mpr hm2
    rw [Rat.natCast_add] at this
    exact rat_lt_of_lt_of_le hr2 this
  have hypos : 0 < y := by
    refine Classical.byContradiction fun h0 => ?_
    have : y = 0 := by omega
    rw [this] at hr2
    have h00 : ((0 : Nat) : Rat) = 0 := rfl
    rw [h00, Rat.zero_add] at hr2
    exact (Rat.not_lt.mpr hx1) hr2
  have hmpos : 0 < m := by
    refine Classical.byContradiction fun h0 => ?_
    have : m = 0 := by omega
    subst this
    simp at hm2
    omega
  by_cases hex : m * m * D = N * 4 ^ 1100
  · simp only [hex, ite_true]
    apply rootside_of_root x hx 1100 m hmpos g hg hlo hhi
    left
    refine ⟨?_, ?_⟩
    · rw [Rat.natCast_pow, Rat.natCast_ofNat]
    · have : ((m : Rat) * (m : Rat)) * (D : Rat) = x * 4 ^ 1100 * (D : Rat) := by
        rw [hz, natsq_cast, ← Rat.natCast_mul, hex]
      exact mul_cancel_pos hDpos this
  · simp only [hex, ite_false]
    apply rootside_of_root x hx 1100 m hmpos g hg hlo hhi
    right
    refine ⟨?_, ?_⟩
    · rw [Rat.natCast_pow, Rat.natCast_ofNat]
    · refine Rat.lt_of_le_of_ne hlo ?_
      intro h
      apply hex
      have : ((m * m : Nat) : Rat) * (D : Rat) = x * 4 ^ 1100 * (D : Rat) := by rw [← natsq_cast, h]
      rw [hz, ← Rat.natCast_mul] at this
      exact Rat.natCast_inj.mp this

theorem or_one_eq' (N : Nat) : (N ||| 1) = 2 * (N / 2) + 1 := or_one_eq N

/-- Nat facts behind `janus_root_side`: the (odd-made) integer root against an even lattice point `c`. -/
theorem root_nat_cmp (M r c : Nat) (hc : c % 2 = 0) (h1 : r * r ≤ M) (h2 : M < (r + 1) * (r + 1)) :
    ((if r * r = M then r else r ||| 1) < c ↔ M < c * c) ∧
    ((if r * r = M then r else r ||| 1) = c ↔ M = c * c) := by
  by_cases hex : r * r = M
  · simp only [hex, ite_true]
    subst hex
    refine ⟨Nat.mul_self_lt_mul_self_iff.symm, ⟨fun h => by rw [h], fun h => ?_⟩⟩
    exact Nat.mul_self_inj.mp h
  · simp only [hex, ite_false, or_one_eq']
    have hlt : r * r < M := Nat.lt_of_le_of_ne h1 hex
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => by omega, fun h => ?_⟩⟩
    · have hrc : r < c := by omega
      have : r + 1 ≤ c := hrc
      have : (r + 1) * (r + 1) ≤ c * c := Nat.mul_self_le_mul_self this
      omega
    · have : r * r < c * c := Nat.lt_trans hlt h
      have := Nat.mul_self_lt_mul_self_iff.mp this
      omega
    · exfalso
      have a1 : r * r < c * c := h ▸ hlt
      have a2 : c * c < (r + 1) * (r + 1) := h ▸ h2
      have := Nat.mul_self_lt_mul_self_iff.mp a1
      have := Nat.mul_self_lt_mul_self_iff.mp a2
      omega

theorem janus_root_side (M : Nat) (hM : M ≠ 0) (e' : Int) :
    RootSide (e' + 1) ((M : Rat) * 2 ^ (2 * e'))
      (((if Janus.Float.isqrt M * Janus.Float.isqrt M = M then Janus.Float.isqrt M
        else Janus.Float.isqrt M ||| 1 : Nat) : Rat) * 2 ^ e') := by
  obtain ⟨h1, h2⟩ := isqrt_spec M
  generalize Janus.Float.isqrt M = r at h1 h2 ⊢
  have hrpos : 0 < r := by
    refine Classical.byContradiction fun h0 => ?_
    have : r = 0 := by omega
    subst this
    simp at h2
    omega
  have hMj : 0 < (if r * r = M then r else r ||| 1) := by
    by_cases hex : r * r = M
    · simp [hex, hrpos]
    · simp [hex, or_one_eq']
  generalize hMjdef : (if r * r = M then r else r ||| 1) = Mj at hMj
  have hp : (0 : Rat) < 2 ^ e' := rat_pos_zpow e'
  refine ⟨Rat.mul_pos (Rat.natCast_pos.mpr hMj) hp, fun n hn => ?_⟩
  have hg2 : (0 : Rat) < 2 ^ (e' + 1) := rat_pos_zpow _
  have hnpos : 0 < n := by
    refine Classical.byContradiction fun hn0 => ?_
    have h0 : (n : Rat) ≤ 0 := by
      have : (n : Rat) ≤ ((0 : Int) : Rat) := Rat.intCast_le_intCast.mpr (by omega)
      simpa using this
    have := Rat.mul_le_mul_of_nonneg_right h0 (Rat.le_of_lt hg2)
    rw [Rat.zero_mul] at this
    exact (Rat.not_lt.mpr this) hn
  obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hnpos)
  have hcast : (((n' : Nat) : Int) : Rat) = (n' : Rat) := Rat.intCast_natCast n'
  rw [hcast]
  have hc : (n' : Rat) * 2 ^ (e' + 1) = ((2 * n' : Nat) : Rat) * 2 ^ e' := by
    rw [Rat.zpow_add_one two_ne_zero_rat, Rat.natCast_mul, Rat.natCast_ofNat]
    rw [Rat.mul_comm (2 : Rat) (n' : Rat), Rat.mul_assoc, Rat.mul_comm (2 ^ e' : Rat) 2, ← Rat.mul_assoc]
  rw [hc]
  have hceven : (2 * n') % 2 = 0 := by omega
  generalize 2 * n' = c at hceven ⊢
  have hsq : (((c : Rat) * 2 ^ e') * ((c : Rat) * 2 ^ e')) = ((c * c : Nat) : Rat) * 2 ^ (2 * e') := by
    rw [show 2 * e' = e' + e' by omega, Rat.zpow_add two_ne_zero_rat, Rat.natCast_mul]
    generalize (2 : Rat) ^ e' = P
    generalize (c : Rat) = C
    calc C * P * (C * P) = C * (P * (C * P)) := Rat.mul_assoc _ _ _
      _ = C * ((P * C) * P) := by rw [← Rat.mul_assoc P C P]
      _ = C * ((C * P) * P) := by rw [Rat.mul_comm P C]
      _ = C * (C * (P * P)) := by rw [Rat.mul_assoc C P P]
      _ = C * C * (P * P) := (Rat.mul_assoc _ _ _).symm
  have hP : (0 : Rat) < 2 ^ (2 * e') := rat_pos_zpow _
  rw [hsq]
  obtain ⟨k1, k2⟩ := root_nat_cmp M r c hceven h1 h2
  rw [hMjdef] at k1 k2
  refine ⟨?_, ?_⟩
  · rw [Rat.mul_lt_mul_right hp, Rat.mul_lt_mul_right hP, Rat.natCast_lt_natCast, Rat.natCast_lt_natCast]
    exact k1
  · constructor
    · intro h
      have := mul_cancel_pos hp h
      have := k2.mp (Rat.natCast_inj.mp this)
      rw [this]
    · intro h
      have := mul_cancel_pos hP h
      have := k2.mpr (Rat.natCast_inj.mp this)
      rw [this]

theorem sqrt_side (fbits m : Nat) (ex : Int) (hm : m ≠ 0)
    (hbig : 1 ≤ ((m : Rat) * 2 ^ ex) * 4 ^ 1100)
    (hrange : -1100 ≤ (Janus.Float.sqrtOdd fbits m ex).2 + 1) :
    Side ((Janus.Float.sqrtOdd fbits m ex).2 + 1) (sqrt_real ((m : Rat) * 2 ^ ex))
        (((Janus.Float.sqrtOdd fbits m ex).1 : Rat) * 2 ^ (Janus.Float.sqrtOdd fbits m ex).2) ∧
      2 ^ (fbits + 4) ≤ (Janus.Float.sqrtOdd fbits m ex).1 := by
  unfold Janus.Float.sqrtOdd at hrange ⊢
  simp only [] at hrange ⊢
  have hodd0 : 0 ≤ ex % 2 := Int.emod_nonneg ex (by decide)
  have hodd1 : ex % 2 < 2 := Int.emod_lt_of_pos ex (by decide)
  have he1 : (ex - ex % 2) / 2 = ex / 2 := by omega
  generalize hk : fbits + 4 = k at hrange ⊢
  generalize hm1 : m * 2 ^ (ex % 2).toNat = m1
  generalize hMdef : m1 * 2 ^ (2 * k) = M
  have hM : M ≠ 0 := by
    rw [← hMdef]
    exact Nat.mul_ne_zero (by rw [← hm1]; exact Nat.mul_ne_zero hm (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))) (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  have hx : (m : Rat) * 2 ^ ex = (M : Rat) * 2 ^ (2 * ((ex - ex % 2) / 2 - k)) := by
    rw [he1]
    have hnum := num_scale m1 (2 * k) (2 * (ex / 2))
    rw [hMdef] at hnum
    have h1 : (m : Rat) * 2 ^ ex = (m1 : Rat) * 2 ^ (2 * (ex / 2)) := by
      rw [← hm1, Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat, Rat.mul_assoc,
        show ((2 : Rat) ^ (ex % 2).toNat) = (2 : Rat) ^ (((ex % 2).toNat : Nat) : Int) from (Rat.zpow_natCast 2 _).symm,
        ← Rat.zpow_add two_ne_zero_rat]
      congr 2; omega
    rw [h1, hnum]
    congr 2
    omega
  rw [hx] at hbig ⊢
  have hJ := janus_root_side M hM ((ex - ex % 2) / 2 - k)
  obtain ⟨h1, h2⟩ := isqrt_spec M
  generalize hr : Janus.Float.isqrt M = r at hJ h1 h2 ⊢
  refine ⟨(sqrt_real_rootside _ hbig _ hrange).side hJ, ?_⟩
  have hm1pos : 1 ≤ m1 := by
    rw [← hm1]; exact Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.two_pow_pos _)
  have hMge : 2 ^ k * 2 ^ k ≤ M := by
    rw [← hMdef, ← Nat.pow_add, show k + k = 2 * k by omega]
    calc 2 ^ (2 * k) = 1 * 2 ^ (2 * k) := (Nat.one_mul _).symm
      _ ≤ m1 * 2 ^ (2 * k) := Nat.mul_le_mul_right _ hm1pos
  have hrk : 2 ^ k ≤ r := by
    refine Classical.byContradiction fun h => ?_
    have h' : r + 1 ≤ 2 ^ k := by omega
    have := Nat.mul_self_le_mul_self h'
    omega
  by_cases hex : r * r = M
  · simp only [hex, ite_true]; exact hrk
  · simp only [hex, ite_false, or_one_eq']; omega

end JanusASL.Proofs
