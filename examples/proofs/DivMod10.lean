import Extracted

/-!
# `DivMod10(x uint64) (q, r uint64)`: named results, division by a constant

**Guarantee.** For every 64-bit `x` and every Go call state of `example.com/basic.DivMod10`, the
call returns (never faulting or panicking), obeys the ABI, and the named results are the
quotient and remainder of `x` by 10 (`QuotRem10`): `q = X0 = ⌊x / 10⌋` and `r = X1 = x mod 10`.

The compiled code has no division: it multiplies by the magic constant `⌈2^67 / 10⌉ =
0xcccccccccccccccd` (`umulh`), shifts right by 3, and computes the remainder as `x - 10·q`
(`add`, `add … lsl #2`, `sub`). The theorem shows that this is the division for all `2^64`
inputs.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- `umulh` by a literal: the compiler's constant is a `128`-bit literal after `setWidth`. -/
theorem umulh_lit (x : BitVec 64) (c : Nat) (hc : c < 2 ^ 64) :
    (BitVec.extractLsb' 64 64 (x.setWidth 128 * BitVec.ofNat 128 c)).toNat =
      x.toNat * c / 2 ^ 64 := by
  have h := Janus.Tactic.umulh_toNat x (BitVec.ofNat 64 c)
  have e : (BitVec.ofNat 64 c).setWidth 128 = BitVec.ofNat 128 c := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]; omega
  rw [e] at h; rw [h]; simp; rw [Nat.mod_eq_of_lt hc]

/-- `lsr #3` is decoded as `ubfm` (a rotation and two masks). -/
theorem lsr3 (u : BitVec 64) :
    (u.rotateRight 3 &&& 18446744073709551615#64 &&& 2305843009213693951#64) = u >>> 3 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : (2305843009213693951#64).getLsbD i = decide (i < 61) := by
    rw [show (2305843009213693951#64) = BitVec.ofNat 64 (2^61 - 1) from rfl, BitVec.getLsbD_ofNat,
      Nat.testBit_two_pow_sub_one]; simp [hi]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight, this,
    show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.getLsbD_allOnes, hi]
  by_cases h : i < 61
  · simp [h]
  · simp [h]; apply BitVec.getLsbD_of_ge; omega

theorem rem_lemma (x q : BitVec 64) (h : q.toNat = x.toNat / 10) :
    (x - (q + q + (q + q) <<< 2)).toNat = x.toNat % 10 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h]
  omega

/-- `q` and `r` are the quotient and remainder of `x` by 10. -/
def QuotRem10 (x q r : BitVec 64) : Prop := q.toNat = x.toNat / 10 ∧ r.toNat = x.toNat % 10

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x] (fun _ => True)
      (fun _ s' => QuotRem10 x (s'.regs 0) (s'.regs 1)) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  rw [lsr3]
  generalize hq : (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 x * 14757395258967641293#128)) >>> 3 = q
  have : q.toNat = x.toNat / 10 := by
    rw [← hq, BitVec.toNat_ushiftRight, umulh_lit x _ (by decide), Nat.shiftRight_eq_div_pow]
    omega
  refine ⟨this, ?_⟩
  exact rem_lemma x q this

end Proof
