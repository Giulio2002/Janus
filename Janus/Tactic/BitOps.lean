import Lean

/-!
# XOR / OR of limbs: lemmas that make branch conditions readable by `omega` (both ISAs)

Go compiles an equality of `uint256` values as the XOR of the limbs (OR-ed together) and a signed comparison
through the sign bit of a XOR: a branch condition arrives as `(BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b).toNat = 0`,
`((x₀ ^^^ y₀) ||| (x₁ ^^^ y₁)).toNat = 0` or `2 ^ 63 ≤ (x ^^^ y).toNat`. `omega` does not read `^^^`/`|||`, so each
consumer proved its own lemma. These are the shared ones. They hold for every bit-vector (the sign-bit rules for 64-bit
ones), need no side condition, and are ordinary public theorems: they are NOT in the `janus_exec`/`janus_post`
(`janus64_*`) simp sets, because in the sets they turn a branch condition into a conjunction of limb equations that the
executor then uses as rewrite rules, which substitutes zero limbs in the goal and changes the shape every consumer's
closer was written for (amd64 `Slt`/`Sgt`). Pass them where you want them: `janus64_run [bv_or_toNat_eq_zero, …]` or
`simp only [bv_xor_toNat_eq_zero]`.

* `bv_xor_toNat_eq_zero`: `(x ^^^ y).toNat = 0 ↔ x.toNat = y.toNat`;
* `bv_or_toNat_eq_zero`: `(x ||| y).toNat = 0 ↔ x.toNat = 0 ∧ y.toNat = 0`;
* `bv_xor_toNat_lt_top`: `(x ^^^ y).toNat < 2 ^ 63 ↔ (x.toNat < 2 ^ 63 ↔ y.toNat < 2 ^ 63)` (64-bit);
* `bv_xor_toNat_top_le`: `2 ^ 63 ≤ (x ^^^ y).toNat ↔ ¬ (x.toNat < 2 ^ 63 ↔ y.toNat < 2 ^ 63)` (64-bit);
* the core `BitVec.xor_eq_zero_iff`, `BitVec.or_eq_zero_iff` for the bit-vector equations.

Ordering: the sign rules mention the literal `2 ^ 63`; apply them (`rw`, or a `simp only` that does not also contain
`Nat.reducePow`) BEFORE `Nat.reducePow` turns `2 ^ 63` into `9223372036854775808`, or the lemma no longer matches. The
zero rules are indifferent. They match `(x ^^^ y).toNat`, so use them before `BitVec.toNat_xor` rewrites the term.
-/

namespace Janus.Tactic

theorem bv_xor_toNat_eq_zero {w : Nat} (x y : BitVec w) : (x ^^^ y).toNat = 0 ↔ x.toNat = y.toNat := by
  rw [BitVec.toNat_xor]
  constructor
  · intro h
    exact Nat.eq_of_testBit_eq fun i => by
      have := congrArg (fun n => n.testBit i) h
      simp only [Nat.testBit_xor, Nat.zero_testBit] at this
      cases ha : x.toNat.testBit i <;> cases hb : y.toNat.testBit i <;> simp_all
  · intro h; rw [h]; simp

theorem bv_or_toNat_eq_zero {w : Nat} (x y : BitVec w) :
    (x ||| y).toNat = 0 ↔ x.toNat = 0 ∧ y.toNat = 0 := by
  rw [BitVec.toNat_or]; exact Nat.or_eq_zero_iff

theorem bv_xor_toNat_lt_top (x y : BitVec 64) :
    (x ^^^ y).toNat < 2 ^ 63 ↔ (x.toNat < 2 ^ 63 ↔ y.toNat < 2 ^ 63) := by
  have h := BitVec.msb_xor (x := x) (y := y)
  rw [BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.msb_eq_decide] at h
  simp only [Nat.reduceSub] at h
  by_cases a : 2 ^ 63 ≤ x.toNat <;> by_cases b : 2 ^ 63 ≤ y.toNat <;>
    by_cases c : 2 ^ 63 ≤ (x ^^^ y).toNat <;> simp_all <;> omega

theorem bv_xor_toNat_top_le (x y : BitVec 64) :
    2 ^ 63 ≤ (x ^^^ y).toNat ↔ ¬ (x.toNat < 2 ^ 63 ↔ y.toNat < 2 ^ 63) := by
  rw [← bv_xor_toNat_lt_top]; omega

end Janus.Tactic
