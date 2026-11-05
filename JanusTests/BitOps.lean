import Janus

/-! # XOR / OR of limbs: the shared lemmas (S8, both ISAs)

`Janus.Tactic.BitOps` provides public lemmas that make `^^^`/`|||` branch conditions readable by `omega`. They are not in
any simp set (that changed the goal shapes of existing proofs), so these tests use them explicitly, the way a consumer
passes them to `simp`/`janus_run`/`janus64_run`; the lemmas are about `BitVec`, the same for both ISAs. -/

namespace JanusTests.BitOps

open Janus Janus.Tactic

example (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b).toNat = 0 ↔ a = b := by
  rw [bv_xor_toNat_eq_zero]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega

/-- Four limbs: the OR of the XORs is zero iff every limb is equal. -/
example (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    ((a0 ^^^ b0) ||| (a1 ^^^ b1) ||| (a2 ^^^ b2) ||| (a3 ^^^ b3)).toNat = 0 ↔
      a0.toNat = b0.toNat ∧ a1.toNat = b1.toNat ∧ a2.toNat = b2.toNat ∧ a3.toNat = b3.toNat := by
  simp only [bv_or_toNat_eq_zero, bv_xor_toNat_eq_zero, and_assoc]

/-- As a `simp` argument (the way a consumer passes them). -/
example (x y z : BitVec 64) (h : ((x ^^^ y) ||| z).toNat = 0) : x.toNat = y.toNat ∧ z.toNat = 0 := by
  simp only [bv_or_toNat_eq_zero, bv_xor_toNat_eq_zero] at h
  exact h

example (x y : BitVec 64) (hx : x.toNat < 2 ^ 63) (hy : 2 ^ 63 ≤ y.toNat) : 2 ^ 63 ≤ (x ^^^ y).toNat := by
  rw [bv_xor_toNat_top_le]; omega

example (x y : BitVec 64) (hx : 2 ^ 63 ≤ x.toNat) (hy : 2 ^ 63 ≤ y.toNat) : (x ^^^ y).toNat < 2 ^ 63 := by
  rw [bv_xor_toNat_lt_top]; omega

/-- The sign test with the literals of a compiled comparison: apply the rule BEFORE `Nat.reducePow` turns `2 ^ 63`
into a literal. -/
example (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a < 2 ^ 63) (h2 : 2 ^ 63 ≤ b) :
    ¬ (BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b).toNat < 2 ^ 63 := by
  rw [bv_xor_toNat_lt_top]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega

/-- The bit-vector equation forms. -/
example (x y : BitVec 64) : x ^^^ y = 0#64 ↔ x = y := BitVec.xor_eq_zero_iff
example (x y : BitVec 64) : x ||| y = 0#64 ↔ x = 0#64 ∧ y = 0#64 := BitVec.or_eq_zero_iff

/-- NOT in the simp sets: `simp only [janus_post]` leaves a XOR alone (the executor's goals keep their shape). -/
example (x y : BitVec 64) (h : (x ^^^ y).toNat = 0) : (x ^^^ y).toNat = 0 := by
  simp only [janus_post] at h ⊢
  exact h

end JanusTests.BitOps
