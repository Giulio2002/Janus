import JanusASL.Proofs.FP.Prim

/-! # Janus' bitwise integer square root is `⌊√n⌋` -/

namespace JanusASL.Proofs

theorem isqrtGo_spec (n : Nat) : ∀ (k r : Nat), r % 2 ^ k = 0 → r * r ≤ n → n < (r + 2 ^ k) * (r + 2 ^ k) →
    Janus.Float.isqrtGo n k r * Janus.Float.isqrtGo n k r ≤ n ∧
      n < (Janus.Float.isqrtGo n k r + 1) * (Janus.Float.isqrtGo n k r + 1) := by
  intro k
  induction k with
  | zero =>
    intro r _ h1 h2
    simp only [Janus.Float.isqrtGo]
    simpa using ⟨h1, h2⟩
  | succ k ih =>
    intro r hr h1 h2
    simp only [Janus.Float.isqrtGo]
    have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    by_cases hc : (r + 2 ^ k) * (r + 2 ^ k) ≤ n
    · simp only [hc, ite_true]
      apply ih
      · -- (r + 2^k) % 2^k = 0
        have : r % 2 ^ k = 0 := by
          have : 2 ^ k ∣ 2 ^ (k + 1) := Nat.pow_dvd_pow 2 (by omega)
          exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans this (Nat.dvd_of_mod_eq_zero hr))
        rw [Nat.add_mod, this]; simp
      · exact hc
      · have : r + 2 ^ k + 2 ^ k = r + 2 ^ (k + 1) := by omega
        rw [this]; exact h2
    · simp only [hc, ite_false]
      apply ih
      · have : 2 ^ k ∣ 2 ^ (k + 1) := Nat.pow_dvd_pow 2 (by omega)
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans this (Nat.dvd_of_mod_eq_zero hr))
      · exact h1
      · exact Nat.not_le.mp hc

theorem isqrt_spec (n : Nat) : Janus.Float.isqrt n * Janus.Float.isqrt n ≤ n ∧
    n < (Janus.Float.isqrt n + 1) * (Janus.Float.isqrt n + 1) := by
  unfold Janus.Float.isqrt
  apply isqrtGo_spec
  · simp
  · simp
  · rw [Nat.zero_add]
    have h1 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
    have h2 : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ (Nat.log2 n / 2 + 1) * 2 ^ (Nat.log2 n / 2 + 1) := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    omega

end JanusASL.Proofs
