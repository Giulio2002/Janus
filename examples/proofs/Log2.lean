import Extracted

/-!
# `Log2(x uint64) uint64`: a `for` loop with only a condition

**Guarantee.** For every 64-bit `x` and every Go call state of `example.com/basic.Log2`, the call
returns (never faulting or panicking; the loop terminates), obeys the ABI, and `r = X0` is the
floor of the base-2 logarithm of `x`: `2^r ≤ x < 2^(r+1)` when `x ≥ 1`, and `r = 0` when `x = 0`.

**How.** `for x > 1 { x >>= 1; n++ }` compiles to a loop with head `cmp x0, #1; b.hi` (`x` in
`X0`, the count in `X1`). `loop` is the invariant there: `count + log2(x) = log2(x₀)`, proved by
induction on a bound `k` with `x < 2^k` (each iteration halves `x`). `lsr #1` is decoded as `ubfm`
(a rotation and two masks); `lsr_ubfm` turns that back into a shift.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- The loop head `cmp x0, #1`. -/
abbrev head : Nat := Extracted.entry + 0x10

/-- `lsr #k` as decoded (`ubfm`): a rotation right by `k` and a mask of the low `64 - k` bits. -/
theorem lsr_ubfm (u : BitVec 64) (k : Nat) (hk : k < 64) :
    (u.rotateRight k &&& 18446744073709551615#64 &&& BitVec.ofNat 64 (2 ^ (64 - k) - 1)) = u >>> k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : (BitVec.ofNat 64 (2 ^ (64 - k) - 1)).getLsbD i = decide (i < 64 - k) := by
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]; simp [hi]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight, this,
    show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.getLsbD_allOnes, hi]
  by_cases h : i < 64 - k
  · simp [h, Nat.mod_eq_of_lt hk]
  · simp [h]; apply BitVec.getLsbD_of_ge; omega

theorem lsr1 (u : BitVec 64) :
    (u.rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64) = u >>> 1 :=
  lsr_ubfm u 1 (by decide)

theorem loop (x : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State) :
    ∀ k (S : State) (y c : BitVec 64), y.toNat < 2 ^ k →
      c.toNat + Nat.log2 y.toNat = Nat.log2 x.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = y → S.regs 1 = c →
      S.regs 30 = BitVec.ofNat 64 ret → S.sp = s.sp → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 18 = s.regs 18 →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = Nat.log2 x.toNat) := by
  have hlx : Nat.log2 x.toNat < 64 := by
    by_cases h : x.toNat = 0
    · rw [h]; decide
    · exact (Nat.log2_lt h).2 x.isLt
  intro k
  induction k with
  | zero =>
    intro S y c hy hc hpc h0 h1 h30 hsp h28 h29 h18
    janus_run
    rw [← hc, show y.toNat = 0 by omega]; rfl
  | succ k ih =>
    intro S y c hy hc hpc h0 h1 h30 hsp h28 h29 h18
    janus_run [lsr1] until [head]
    · have hl : Nat.log2 y.toNat = Nat.log2 (y.toNat / 2) + 1 := by
        rw [Nat.log2_def]; simp; omega
      apply ih _ (y >>> 1) (c + 1#64)
      all_goals janus_simp
      · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rw [Nat.pow_succ] at hy; omega
      · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]; omega
    · rw [← hc, Nat.log2_def]; simp; omega

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x] (fun _ => True)
      (fun _ s' => (x.toNat = 0 ∧ (s'.regs 0).toNat = 0) ∨
        (2 ^ (s'.regs 0).toNat ≤ x.toNat ∧ x.toNat < 2 ^ ((s'.regs 0).toNat + 1))) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run until [head]
  refine Reaches.mono (loop x ret hret s 64 _ x 0#64 x.isLt (by simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp)) ?_
  intro o ho
  cases o with
  | stub _ _ _ => exact ho.elim
  | returned s' =>
    simp only [isReturn_returned] at ho ⊢
    refine ⟨ho.1, ?_⟩
    rw [ho.2]
    by_cases h : x.toNat = 0
    · left; rw [h]; exact ⟨rfl, rfl⟩
    · right; exact (Nat.log2_eq_iff h).1 rfl

end Proof
