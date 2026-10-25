import Extracted

/-!
# `AlignUp(p, a uintptr) uintptr`: `uintptr` arithmetic, rounding up to a power of two

**Guarantee.** For all 64-bit `p`, `a` with `a = 2^k` a power of two and `p + a ≤ 2^64` (the
rounded-up value is representable), and every Go call state of `example.com/basic.AlignUp`, the
call returns (never faulting or panicking), obeys the ABI, and `r = X0` is the smallest multiple
of `a` that is at least `p`: `r mod a = 0`, `p ≤ r` and `r < p + a`.

The code is `(p + a - 1) & -a` (`add`, `sub`, `neg`, `and`); `p &^ (a - 1)` became an `and` with
`-a`, which is the same mask when `a` is a power of two.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- Masking with `2^64 - 2^k` clears the low `k` bits. -/
theorem and_high (x k : Nat) (hx : x < 2 ^ 64) (hk : k ≤ 64) :
    x &&& (2 ^ 64 - 2 ^ k) = x / 2 ^ k * 2 ^ k := by
  have e : 2 ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]
  rw [e]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases h1 : k ≤ i
  · rw [Nat.sub_add_cancel h1]
    by_cases h2 : i < 64
    · simp [h1, show i - k < 64 - k by omega]
    · have : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [h1]

/-- The value the code computes, `((p + a - 1) mod 2^64) &&& (-a mod 2^64)`, is the least
multiple of `a = 2^k` that is at least `p`. -/
theorem round_up (p a k : Nat) (ha : a = 2 ^ k) (hpa : p + a ≤ 2 ^ 64) :
    ((18446744073709551615 + (a + p)) % 18446744073709551616 &&&
        (18446744073709551616 - a) % 18446744073709551616) % a = 0 ∧
      p ≤ ((18446744073709551615 + (a + p)) % 18446744073709551616 &&&
        (18446744073709551616 - a) % 18446744073709551616) ∧
      ((18446744073709551615 + (a + p)) % 18446744073709551616 &&&
        (18446744073709551616 - a) % 18446744073709551616) < p + a := by
  have ha1 : 1 ≤ a := ha ▸ Nat.one_le_two_pow
  have hk : k ≤ 64 := by
    have : 2 ^ k ≤ 2 ^ 64 := by omega
    exact (Nat.pow_le_pow_iff_right (by decide)).1 this
  rw [show (18446744073709551615 + (a + p)) % 18446744073709551616 = a + p - 1 by omega,
    show (18446744073709551616 - a) % 18446744073709551616 = 2 ^ 64 - 2 ^ k by omega,
    and_high _ _ (by omega) hk, ← ha]
  have hd := Nat.div_add_mod (a + p - 1) a
  have hm := Nat.mod_lt (a + p - 1) (show 0 < a by omega)
  rw [Nat.mul_comm] at hd
  refine ⟨Nat.mul_mod_left _ _, ?_, ?_⟩ <;>
    generalize (a + p - 1) / a * a = r at * <;> generalize (a + p - 1) % a = m at * <;> omega

theorem correctness (p a : BitVec 64) (k : Nat) :
    Ensures Extracted.program Extracted.entry [p, a] (fun _ => a.toNat = 2 ^ k ∧ p.toNat + a.toNat ≤ 2 ^ 64)
      (fun _ s' => (s'.regs 0).toNat % a.toNat = 0 ∧ p.toNat ≤ (s'.regs 0).toNat ∧
        (s'.regs 0).toNat < p.toNat + a.toNat) := by
  intro ret hret s hs ⟨ha, hpa⟩
  janus_intro hs
  janus_run
  exact round_up p.toNat a.toNat k ha hpa

end Proof
