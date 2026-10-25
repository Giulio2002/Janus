import Janus.Spec.Basic

/-!
# Byte-buffer vocabulary

* `countOf m p c n`: the number of the `n` bytes at `p` equal to `c` (a byte count, as the C loop
  `for (i = 0; i < n; i++) k += p[i] == c;` computes it); `countOf_add16` adds sixteen bytes at
  once, in the form the 16-byte vector loops produce.
* `and_mask16`: `x &&& ~15 = 16 * (x / 16)` for a 64-bit `x` (`and x3, x1, #~15`, the block count
  of a 16-byte loop).
-/

namespace Janus.Spec

open Janus.Arm64

/-- The number of the first `n` bytes at `p` that equal `c`. -/
def countOf (m : Memory) (p c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => countOf m p c n + (if m.readLE (p + n) 1 = c then 1 else 0)

theorem countOf_le (m : Memory) (p c n : Nat) : countOf m p c n ≤ n := by
  induction n with
  | zero => simp [countOf]
  | succ n ih => simp only [countOf]; split <;> omega

/-- Sixteen more bytes. -/
theorem countOf_add16 (m : Memory) (p c n : Nat) : countOf m p c (n + 16) =
    countOf m p c n + (if m.readLE (p + n) 1 = c then 1 else 0) +
      (if m.readLE (p + n + 1) 1 = c then 1 else 0) + (if m.readLE (p + n + 2) 1 = c then 1 else 0) +
      (if m.readLE (p + n + 3) 1 = c then 1 else 0) + (if m.readLE (p + n + 4) 1 = c then 1 else 0) +
      (if m.readLE (p + n + 5) 1 = c then 1 else 0) + (if m.readLE (p + n + 6) 1 = c then 1 else 0) +
      (if m.readLE (p + n + 7) 1 = c then 1 else 0) + (if m.readLE (p + n + 8) 1 = c then 1 else 0) +
      (if m.readLE (p + n + 9) 1 = c then 1 else 0) + (if m.readLE (p + n + 10) 1 = c then 1 else 0) +
      (if m.readLE (p + n + 11) 1 = c then 1 else 0) + (if m.readLE (p + n + 12) 1 = c then 1 else 0) +
      (if m.readLE (p + n + 13) 1 = c then 1 else 0) + (if m.readLE (p + n + 14) 1 = c then 1 else 0) +
      (if m.readLE (p + n + 15) 1 = c then 1 else 0) := by
  simp only [countOf, Nat.add_assoc]

/-- The count only looks at the counted bytes. -/
theorem countOf_congr {m m' : Memory} (p c : Nat) :
    ∀ n, (∀ i, i < n → m'.readLE (p + i) 1 = m.readLE (p + i) 1) → countOf m' p c n = countOf m p c n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [countOf]; rw [countOf_congr p c n fun i hi => h i (by omega), h n (by omega)]

/-- `x &&& ~15 = 16 * (x / 16)` for a 64-bit `x`. -/
theorem and_mask16 (x : Nat) (hx : x < 2 ^ 64) : x &&& 18446744073709551600 = x / 16 * 16 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show x / 16 * 16 = x >>> 4 <<< 4 by simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow],
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hj : j < 64
  · have hm : ∀ j < 64, (18446744073709551600 : Nat).testBit j = decide (4 ≤ j) := by decide
    rw [hm j hj]
    by_cases h4 : 4 ≤ j
    · simp [h4, show 4 + (j - 4) = j by omega]
    · simp [h4]
  · have h1 : (18446744073709551600 : Nat).testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show (18446744073709551600 : Nat) < 2 ^ 64 by decide)
        (Nat.pow_le_pow_right (by decide) (show 64 ≤ j by omega)))
    have h2 : x.testBit (4 + (j - 4)) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, h2]

/-- The same for the 64-bit register value (`len &&& ~15`). -/
theorem and_mask16_toNat (len : BitVec 64) :
    (len &&& 18446744073709551600#64).toNat = len.toNat / 16 * 16 := by
  rw [BitVec.toNat_and, show (18446744073709551600#64).toNat = 18446744073709551600 from rfl,
    and_mask16 _ len.isLt]

end Janus.Spec
