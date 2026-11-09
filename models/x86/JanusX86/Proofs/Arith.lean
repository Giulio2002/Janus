import JanusX86.Proofs.Flags

/-! # Arithmetic of the model's flag functions

The model computes flags on integers: `bits_of_int` (two's complement truncation), `logcount_int`
(population count, a well-founded recursion), `logbitp_int`. These lemmas relate them to the
natural-number formulas of Janus (`parity`, `auxCarry`, `popNat`). -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem bits_of_int_toNat_of_nonneg (v : Int) (n : Nat) (h0 : 0 ≤ v) :
    (bits_of_int v n).toNat = v.toNat % 2 ^ n := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [bits_of_int_natCast_toNat]; simp

theorem bits_of_int_eq_ofInt (v : Int) (n : Nat) : bits_of_int v n = BitVec.ofInt n v := by
  apply BitVec.eq_of_toNat_eq
  simp only [bits_of_int, Sail.get_slice_int, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.zero_add, BitVec.toNat_ofInt]
  have h5 : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  have h6 : (0 : Int) < 2 ^ (n + 1) := Int.pow_pos (by decide)
  have hd : ((2 ^ n : Nat) : Int) ∣ ((2 ^ (n + 1) : Nat) : Int) := by
    rw [Nat.pow_succ]; exact Int.natCast_dvd_natCast.mpr (Nat.dvd_mul_right _ _)
  have ha : 0 ≤ v % ((2 ^ (n + 1) : Nat) : Int) := Int.emod_nonneg _ (by omega)
  obtain ⟨a, ha'⟩ := Int.eq_ofNat_of_zero_le ha
  rw [ha', Int.toNat_natCast]
  have e : (a : Int) % ((2 ^ n : Nat) : Int) = v % ((2 ^ n : Nat) : Int) := by
    rw [← ha', Int.emod_emod_of_dvd _ hd]
  rw [← e, ← Int.natCast_emod, Int.toNat_natCast]

theorem bits_of_int_toInt (v : Int) (n : Nat) (h1 : -(2 ^ n : Int) ≤ 2 * v) (h2 : 2 * v < 2 ^ n) :
    (bits_of_int v n).toInt = v := by
  rw [bits_of_int_eq_ofInt, BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le_mul_two (by push_cast; omega) (by push_cast; omega)

theorem isEven_nat (n : Nat) : isEven (n : Int) = (n % 2 == 0) := by
  have h : (Sail.get_slice_int 1 (n : Int) 0) = BitVec.ofNat 1 (n % 2) := by
    apply BitVec.eq_of_toNat_eq
    have := bits_of_int_natCast_toNat n 1
    simp only [bits_of_int] at this
    rw [this]; simp
  simp only [isEven, h]
  rcases Nat.mod_two_eq_zero_or_one n with e | e <;> simp [e]

theorem popNat_zero : ∀ k, Janus.Amd64.popNat k 0 = 0
  | 0 => rfl
  | k + 1 => by simp [Janus.Amd64.popNat, popNat_zero k]

theorem logcount_int_nat : ∀ (k n : Nat), n < 2 ^ k → logcount_int (n : Int) = (Janus.Amd64.popNat k n : Int)
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; rw [logcount_int]; simp [Janus.Amd64.popNat]
  | k + 1, n, h => by
    rw [logcount_int]
    by_cases h0 : n = 0
    · subst h0; simp [popNat_zero]
    have hs : Sail.Int.shiftr (n : Int) 1 = ((n / 2 : Nat) : Int) := by
      simp [Sail.Int.shiftr, Sail.Nat.iterate]
    have ih := logcount_int_nat k (n / 2) (by rw [Nat.pow_succ] at h; omega)
    have hne : ((n : Int) == 0) = false := by simp; omega
    have hlt : ((n : Int) <b 0) = false := by simp
    simp only [hne, hlt, Bool.false_eq_true, ↓reduceIte, isEven_nat, hs, ih, Janus.Amd64.popNat]
    rcases Nat.mod_two_eq_zero_or_one n with e | e <;> simp [e] <;> omega

theorem logbitp_int_zero_nat (n : Nat) (s : SState) :
    (logbitp_int 0 (n : Int)).run s = .ok (n % 2 == 1) s := by
  have h : (Sail.get_slice_int 1 (n : Int) 0) = BitVec.ofNat 1 (n % 2) := by
    apply BitVec.eq_of_toNat_eq
    have := bits_of_int_natCast_toNat n 1
    simp only [bits_of_int] at this
    rw [this]; simp
  simp only [logbitp_int, run_bind, run_sail_assert_of (show (decide ((0 : Int) ≥ 0)) = true by decide),
    run_pure, bits_to_bool]
  rw [show Int.toNat 0 = 0 from rfl, h]
  rcases Nat.mod_two_eq_zero_or_one n with e | e <;> simp [e]

theorem parity_popNat : ∀ n < 256, Janus.Amd64.parity n = (Janus.Amd64.popNat 8 n % 2 == 0) := by
  decide +kernel

/-- `PF` as the model computes it (`pf_spec*`), on the low byte `n < 256` of the result. -/
theorem pf_eq (n : Nat) (hn : n < 256) (s : SState) :
    (do let b ← logbitp_int 0 (logcount_int (n : Int)); pure (bool_to_bits (!b)) : SailM (BitVec 1)).run s =
      .ok (BitVec.ofBool (Janus.Amd64.parity n)) s := by
  rw [logcount_int_nat 8 n hn]
  simp only [run_bind, logbitp_int_zero_nat, run_pure, parity_popNat n hn]
  rcases Nat.mod_two_eq_zero_or_one (Janus.Amd64.popNat 8 n) with e | e <;> simp [e, bool_to_bits]

theorem af_add_core : ∀ a < 32, ∀ b < 32, ∀ c < 2,
    ((a ^^^ b ^^^ ((a + b + c) % 32)) / 16 == 1) = decide (a % 16 + b % 16 + c > 15) := by
  decide +kernel

theorem af_sub_core : ∀ a < 32, ∀ b < 32, ∀ c < 2,
    ((a ^^^ b ^^^ ((a + 64 - b - c) % 32)) / 16 == 1) = decide (a % 16 < b % 16 + c) := by
  decide +kernel

theorem div16_mod2 (z : Nat) : z / 16 % 2 = z % 32 / 16 := by omega

theorem pow_w_32 {w : Nat} (hw : 5 ≤ w) : ∃ t, 2 ^ w = 32 * t :=
  ⟨2 ^ (w - 5), by rw [show w = 5 + (w - 5) by omega, Nat.pow_add]; simp⟩

theorem xor3_mod32 (a b c : Nat) : (a ^^^ b ^^^ c) % 32 = (a % 32) ^^^ (b % 32) ^^^ (c % 32) := by
  have h : (32 : Nat) = 2 ^ 5 := rfl
  rw [h, Nat.xor_mod_two_pow, Nat.xor_mod_two_pow]

theorem af_add_nat (a b c w : Nat) (hc : c < 2) (hw : 5 ≤ w) :
    ((a ^^^ b ^^^ ((a + b + c) % 2 ^ w)) / 16 % 2 == 1) = decide (a % 16 + b % 16 + c > 15) := by
  obtain ⟨t, ht⟩ := pow_w_32 hw
  have e : ((a + b + c) % 2 ^ w) % 32 = (a % 32 + b % 32 + c) % 32 := by
    rw [ht, Nat.mod_mul_right_mod]; omega
  rw [div16_mod2, xor3_mod32, e,
    af_add_core (a % 32) (by omega) (b % 32) (by omega) c hc]
  congr 1; apply propext; omega

theorem af_sub_nat (a b c w : Nat) (hc : c < 2) (hw : 5 ≤ w) (hb : b < 2 ^ w) :
    ((a ^^^ b ^^^ ((a + 2 ^ w - b - c) % 2 ^ w)) / 16 % 2 == 1) = decide (a % 16 < b % 16 + c) := by
  obtain ⟨t, ht⟩ := pow_w_32 hw
  have e : ((a + 2 ^ w - b - c) % 2 ^ w) % 32 = (a % 32 + 64 - b % 32 - c) % 32 := by
    rw [Nat.mod_mod_of_dvd _ (by rw [ht]; exact Nat.dvd_mul_right 32 t)]
    rw [ht] at hb ⊢; omega
  rw [div16_mod2, xor3_mod32, e,
    af_sub_core (a % 32) (by omega) (b % 32) (by omega) c hc]
  congr 1; apply propext; omega

end JanusX86.Proofs
