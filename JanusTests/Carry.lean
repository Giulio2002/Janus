import Janus

/-!
# Tests of the multi-limb arithmetic automation

`janus_carry` (carry chains by reflection, `Janus.Tactic.Carry`), `janus_ring` (polynomial
identities, `Janus.Tactic.RingTac`), and their use in `janus_arith` / `janus64_arith`. Every
`example` must elaborate; the `fail_if_success` ones check that false statements are rejected.
-/

namespace JanusTests.Carry

open Janus Janus.Arm64

/-! ## Carry chains -/

/-- One limb: `a + b = lo + 2^64·carry`. -/
example (a b : BitVec 64) :
    (a.toNat + b.toNat) % 2 ^ 64 + 2 ^ 64 * ((a.toNat + b.toNat) / 2 ^ 64) = a.toNat + b.toNat := by
  janus_carry

/-- A 64×64-bit product as `MUL`/`UMULH`: `hi·2^64 + lo = x·y`. -/
example (x y : BitVec 64) :
    x.toNat * y.toNat / 2 ^ 64 * 2 ^ 64 + x.toNat * y.toNat % 2 ^ 64 = x.toNat * y.toNat := by
  janus_carry

/-- A multiply-add limb as Go compiles `bits.Mul64` + two `bits.Add64`: the carry
`hi + c₁ + c₂` does not wrap, because `x·y + z + c ≤ 2^128 - 1`. -/
example (x y z c : BitVec 64) :
    (z.toNat + x.toNat * y.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64 + 2 ^ 64 *
      ((x.toNat * y.toNat / 2 ^ 64 + (z.toNat + x.toNat * y.toNat % 2 ^ 64) / 2 ^ 64 % 2 ^ 64 +
        ((z.toNat + x.toNat * y.toNat) % 2 ^ 64 + c.toNat) / 2 ^ 64) % 2 ^ 64) =
      z.toNat + x.toNat * y.toNat + c.toNat := by
  janus_carry

/-- The amd64 carry flag `(decide (2^64 ≤ a + b)).toNat`. -/
example (a b : BitVec 64) :
    (decide (2 ^ 64 ≤ a.toNat + b.toNat)).toNat * 2 ^ 64 + (a.toNat + b.toNat) % 2 ^ 64 =
      a.toNat + b.toNat := by
  janus_carry

/-- A carry materialised by `SBBQ`/`SUBQ` (truncated subtraction that never truncates). -/
example (a b c : BitVec 64) :
    (2 ^ 64 - (2 ^ 64 - 1) * (decide (2 ^ 64 ≤ a.toNat + b.toNat)).toNat + c.toNat) % 2 ^ 64 =
      (c.toNat + (a.toNat + b.toNat) / 2 ^ 64) % 2 ^ 64 := by
  janus_carry

/-- A two-limb add-with-carry chain against the 128-bit sum. -/
example (a0 a1 b0 b1 : BitVec 64) :
    (a0.toNat + b0.toNat) % 2 ^ 64 + 2 ^ 64 * ((a1.toNat + b1.toNat + (a0.toNat + b0.toNat) / 2 ^ 64) % 2 ^ 64) =
      (a0.toNat + 2 ^ 64 * a1.toNat + (b0.toNat + 2 ^ 64 * b1.toNat)) % 2 ^ 128 := by
  janus_carry

/-- The low half of a 128×128-bit product (`(X·Y) mod 2^128`): the difference is a multiple
of `2^128` and both sides are below it. -/
example (x0 x1 y0 y1 : BitVec 64) :
    x0.toNat * y0.toNat % 2 ^ 64 + 2 ^ 64 * ((x0.toNat * y0.toNat / 2 ^ 64 + x1.toNat * y0.toNat +
      x0.toNat * y1.toNat) % 2 ^ 64) =
      (x0.toNat + 2 ^ 64 * x1.toNat) * (y0.toNat + 2 ^ 64 * y1.toNat) % 2 ^ 128 := by
  janus_carry

/-- Carry bounds (the side conditions of `mod64_of_lt`), which `omega` cannot prove because
it does not know the bound of a product. -/
example (x y z : BitVec 64) :
    x.toNat * y.toNat / 2 ^ 64 + (z.toNat + x.toNat * y.toNat % 2 ^ 64) / 2 ^ 64 < 2 ^ 64 := by
  janus_carry

example (x y : BitVec 64) : x.toNat * y.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
  janus_carry

/-- Bounds from hypotheses. -/
example (a b : Nat) (ha : a < 2 ^ 64) (hb : b ≤ 7) : (a + b) / 2 ^ 64 ≤ 1 := by
  janus_carry

/-- Memory reads are limbs. -/
example (m : Memory) (p : Nat) :
    (m.readLE p 8 + m.readLE (p + 8) 8) % 2 ^ 64 + 2 ^ 64 * ((m.readLE p 8 + m.readLE (p + 8) 8) / 2 ^ 64) =
      m.readLE p 8 + m.readLE (p + 8) 8 := by
  janus_carry

/-- Conjunctions are split. -/
example (a b : BitVec 64) :
    (a.toNat + b.toNat) / 2 ^ 64 ≤ 1 ∧ (a.toNat % 2 ^ 64) = a.toNat := by
  janus_carry

/-- The carry of a three-term sum is at most 2: no `% 2^64` needed. -/
example (a b c : BitVec 64) : (a.toNat + b.toNat + c.toNat) / 2 ^ 64 % 2 ^ 64 =
    (a.toNat + b.toNat + c.toNat) / 2 ^ 64 := by
  janus_carry

/-! ## Rejections -/

/-- error: janus_carry: not a carry-chain equation it can prove -/
#guard_msgs (substring := true) in
example (a b : BitVec 64) : (a.toNat + b.toNat) % 2 ^ 64 = a.toNat + b.toNat := by
  janus_carry

/-- error: janus_carry: not a carry-chain equation it can prove -/
#guard_msgs (substring := true) in
example (a : Nat) : a % 2 ^ 64 = a := by
  janus_carry

/-- error: janus_carry: not a carry-chain equation it can prove -/
#guard_msgs (substring := true) in
example (x y : BitVec 64) : x.toNat * y.toNat < 2 ^ 64 := by
  janus_carry

/-! ## `janus_ring` -/

example (a b c : Int) : (a + b) * (a - b) + c * c = a ^ 2 - b ^ 2 + c ^ 2 := by janus_ring

example (x y : Int) : (x + 2 * y) ^ 3 = x ^ 3 + 6 * x ^ 2 * y + 12 * x * y ^ 2 + 8 * y ^ 3 := by
  janus_ring

example (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by janus_ring

example (a b : Int) : a * b = b * a + 0 * a - (-1 + 1) := by janus_ring

/-- error: janus_ring: the two sides have different normal forms -/
#guard_msgs (substring := true) in
example (a b : Int) : a * b = a + b := by
  janus_ring

/-! ## `janus_arith` uses the fast path -/

example (x y z c : BitVec 64) :
    (z.toNat + x.toNat * y.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64 + 2 ^ 64 *
      ((x.toNat * y.toNat / 2 ^ 64 + (z.toNat + x.toNat * y.toNat % 2 ^ 64) / 2 ^ 64 % 2 ^ 64 +
        ((z.toNat + x.toNat * y.toNat) % 2 ^ 64 + c.toNat) / 2 ^ 64) % 2 ^ 64) =
      z.toNat + x.toNat * y.toNat + c.toNat := by
  janus_arith

-- and falls back to `omega` for what it does not decide
example (a b : Nat) (h : a < b) : a + 1 ≤ b := by janus_arith
example (a b : Nat) (h : a ≤ b) (h' : b ≤ a) : a = b := by janus_arith


/-! ## Nested carries (U12: `MulOverflow`)

The carries of a schoolbook multiplication are nested floors, `⌊(a + ⌊b/B⌋)/B⌋`. `janus_carry` flattens
them to one quotient of the product polynomial by a power of `B` (`flatQ`), so the chain of carries of
the low limbs is the same quotient atom as the carry out of the low half of the product; and it bounds a
difference of carries by `⌈…/B⌉` through the numerators (`civF`, `pairIvOf`). -/

/-- A nested floor is one quotient: `⌊(a1 + ⌊a0/B⌋)/B⌋ = ⌊(B·a1 + a0)/B²⌋`. -/
example (a0 a1 : Nat) :
    (a1 + a0 / 2 ^ 64) / 2 ^ 64 = (2 ^ 64 * a1 + a0) / 2 ^ 128 := by
  janus_carry

/-- Three columns: the carry chain of the products is the carry out of the low half of the product. -/
example (x0 x1 x2 y0 y1 y2 : BitVec 64) :
    (x2.toNat * y0.toNat + x1.toNat * y1.toNat + x0.toNat * y2.toNat +
        (x1.toNat * y0.toNat + x0.toNat * y1.toNat + x0.toNat * y0.toNat / 2 ^ 64) / 2 ^ 64) / 2 ^ 64 =
      (x2.toNat * y0.toNat * 2 ^ 128 + x1.toNat * y1.toNat * 2 ^ 128 + x0.toNat * y2.toNat * 2 ^ 128 +
        x1.toNat * y0.toNat * 2 ^ 64 + x0.toNat * y1.toNat * 2 ^ 64 + x0.toNat * y0.toNat) / 2 ^ 192 := by
  janus_carry

/-- Four columns (the carry into the fifth column of a 4×4-limb product): three nested floors. -/
example (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) :
    (x3.toNat * y0.toNat + x2.toNat * y1.toNat + x1.toNat * y2.toNat + x0.toNat * y3.toNat +
        (x2.toNat * y0.toNat + x1.toNat * y1.toNat + x0.toNat * y2.toNat +
          (x1.toNat * y0.toNat + x0.toNat * y1.toNat + x0.toNat * y0.toNat / 2 ^ 64) / 2 ^ 64) / 2 ^ 64) /
        2 ^ 64 =
      (x3.toNat * y0.toNat * 2 ^ 192 + x2.toNat * y1.toNat * 2 ^ 192 + x1.toNat * y2.toNat * 2 ^ 192 +
        x0.toNat * y3.toNat * 2 ^ 192 + x2.toNat * y0.toNat * 2 ^ 128 + x1.toNat * y1.toNat * 2 ^ 128 +
        x0.toNat * y2.toNat * 2 ^ 128 + x1.toNat * y0.toNat * 2 ^ 64 + x0.toNat * y1.toNat * 2 ^ 64 +
        x0.toNat * y0.toNat) / 2 ^ 256 := by
  janus_carry


/-- False statements about nested carries are still rejected (a wrong divisor, a wrong coefficient, a
carry that can reach `2^64`). -/
example (a0 a1 : Nat) : True := by
  fail_if_success
    have : (a1 + a0 / 2 ^ 64) / 2 ^ 64 = (2 ^ 64 * a1 + a0) / 2 ^ 127 := by janus_carry
  fail_if_success
    have : (a1 + a0 / 2 ^ 64) / 2 ^ 64 = (2 ^ 63 * a1 + a0) / 2 ^ 128 := by janus_carry
  trivial
example (a b : BitVec 64) : True := by
  fail_if_success
    have : (a.toNat * b.toNat + a.toNat * b.toNat / 2 ^ 64) / 2 ^ 64 = 0 := by janus_carry
  trivial

end JanusTests.Carry
