import Extracted

/-!
# `runtime.decoderune` meets its contract, from the machine code

**Guarantee.** For every list `rt` of runtime-owned ranges, every readiness predicate `H` and
every stack window of at least 24 bytes, the machine code of Go 1.26's
`runtime.decoderune(s, k)` (linux/arm64, the function `for _, r := range s` calls for a byte
`≥ 0x80`) satisfies the contract `RtContract … decoderuneSpec` (`Janus/Contracts/String.lean`):
from every call state with a readable string `s` outside the callee's stack window,
`0 ≤ k < 2^63` and a stack guard below `SP`, it returns to `X30` with `(r, pos) =
decodeRune (bytes of s) k` (`Janus/Spec/String.lean`: Go's decoder, U+FFFD for every invalid
input) in `X0` (low 32 bits) and `X1`, `SP`, `R18`, `R28`, `R29` preserved and memory changed only
in its 16-byte frame record and its argument spill slot.

So the contract that `SumRunes` and `RuneLen` assume is met by the real runtime: this theorem is
its witness (round 9's rule), and nothing about `decoderune` is trusted.

**How.** One symbolic run over the 25 paths of the code (the bounds checks, the three sequence
lengths and their continuation-byte checks, the overlong, surrogate and range checks). At each
return the machine's rune is a mask-and-shift expression over the loaded bytes (`ubfiz`/`and`/
`orr`, the field lemmas `r2`, `r3`, `r4`), `decodeRune` is restated arithmetically
(`decodeRune_eq_arith`), and `omega` matches the path's branch conditions with the spec's.
`and_sshr_sub` is Go's masked index for `s[k:]` (`AND X3, X2, (X2 - X1) ASR #63`).
-/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
namespace Proof

/-- Go's masked slice index (`AND Xd, Xk, (Xk - Xn) ASR #63`, Spectre hardening of `s[k:]`): `k`
when `k < n`. -/
theorem and_sshr_sub (a b : BitVec 64) (h : a.toNat < b.toNat) (hb : b.toNat < 2 ^ 63) :
    a.toNat &&& ((a - b).sshiftRight 63).toNat = a.toNat := by
  have hneg : (a - b).msb = true := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_sub]; simp only [decide_eq_true_eq]; omega
  have : (a - b).sshiftRight 63 = BitVec.allOnes 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_allOnes, hi, decide_true]
    split
    · rename_i h2
      obtain rfl : i = 0 := by omega
      simpa [BitVec.msb_eq_getLsbD_last] using hneg
    · simpa [hi] using hneg
  rw [this, BitVec.toNat_allOnes, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt a.isLt]

theorem bv_and63 (b : Nat) (h : b < 256) : (BitVec.ofNat 64 b &&& 63#64).toNat = b % 64 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2^64)]
  exact Nat.and_two_pow_sub_one_eq_mod b 6
theorem bv_and31 (b : Nat) (h : b < 256) : (BitVec.ofNat 64 b &&& 31#64).toNat = b % 32 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2^64)]
  exact Nat.and_two_pow_sub_one_eq_mod b 5
theorem bv_shl (x : BitVec 64) (i : Nat) (h : x.toNat * 2 ^ i < 2 ^ 64) : (x <<< i).toNat = x.toNat * 2 ^ i := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

set_option maxRecDepth 10000 in
theorem ubfiz12_4 : ∀ b, b < 256 →
    (BitVec.ofNat 64 b).rotateRight 52 &&& 61440#64 &&& 65535#64 = BitVec.ofNat 64 (b % 16 * 4096) := by
  decide +kernel
set_option maxRecDepth 10000 in
theorem ubfiz18_3 : ∀ b, b < 256 →
    (BitVec.ofNat 64 b).rotateRight 46 &&& 1835008#64 &&& 2097151#64 = BitVec.ofNat 64 (b % 8 * 262144) := by
  decide +kernel

theorem r2 (b0 b1 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) :
    (BitVec.ofNat 64 b1 &&& 63#64 ||| (BitVec.ofNat 64 b0 &&& 31#64) <<< 6).toNat = b0 % 32 * 64 + b1 % 64 := by
  rw [BitVec.toNat_or, bv_shl _ _ (by rw [bv_and31 _ h0]; omega), bv_and31 _ h0, bv_and63 _ h1]
  exact or_low' (b0 % 32) (b1 % 64) 6 (by omega)

theorem r3 (b0 b1 b2 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) :
    ((BitVec.ofNat 64 b0).rotateRight 52 &&& 61440#64 &&& 65535#64 ||| (BitVec.ofNat 64 b1 &&& 63#64) <<< 6 |||
      BitVec.ofNat 64 b2 &&& 63#64).toNat = b0 % 16 * 4096 + b1 % 64 * 64 + b2 % 64 := by
  rw [ubfiz12_4 b0 h0, BitVec.toNat_or, BitVec.toNat_or, bv_shl _ _ (by rw [bv_and63 _ h1]; omega),
    bv_and63 _ h1, bv_and63 _ h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show b0 % 16 * 4096 < 2 ^ 64 by omega)]
  rw [show b0 % 16 * 4096 = (b0 % 16 * 2 ^ 6) * 2 ^ 6 by omega, mul_or_mul, or_low _ _ 6 (by omega),
    or_low _ _ 6 (by omega)]
  omega

theorem r4 (b0 b1 b2 b3 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) :
    (BitVec.ofNat 64 b3 &&& 63#64 ||| ((BitVec.ofNat 64 b0).rotateRight 46 &&& 1835008#64 &&& 2097151#64 |||
      (BitVec.ofNat 64 b1 &&& 63#64) <<< 12 ||| (BitVec.ofNat 64 b2 &&& 63#64) <<< 6)).toNat =
      b0 % 8 * 262144 + b1 % 64 * 4096 + b2 % 64 * 64 + b3 % 64 := by
  rw [ubfiz18_3 b0 h0, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or,
    bv_shl _ _ (by rw [bv_and63 _ h1]; omega), bv_shl _ _ (by rw [bv_and63 _ h2]; omega),
    bv_and63 _ h1, bv_and63 _ h2, bv_and63 _ h3, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show b0 % 8 * 262144 < 2 ^ 64 by omega)]
  have e1 : b0 % 8 * 262144 ||| b1 % 64 * 2 ^ 12 = b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 := by
    have := or_mul_low (b0 % 8) (b1 % 64) 6 12 (by omega)
    simpa using this
  have e2 : b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 ||| b2 % 64 * 2 ^ 6 =
      b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 + b2 % 64 * 2 ^ 6 := by
    have := or_mul_low (b0 % 8 * 64 + b1 % 64) (b2 % 64) 6 6 (by omega)
    rw [show (b0 % 8 * 64 + b1 % 64) * 2 ^ (6 + 6) = b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 by omega] at this
    exact this
  have e3 : b3 % 64 ||| b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 + b2 % 64 * 2 ^ 6 =
      b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 + b2 % 64 * 2 ^ 6 + b3 % 64 := by
    have := or_low' (b0 % 8 * 4096 + b1 % 64 * 64 + b2 % 64) (b3 % 64) 6 (by omega)
    rw [show (b0 % 8 * 4096 + b1 % 64 * 64 + b2 % 64) * 2 ^ 6 = b0 % 8 * 262144 + b1 % 64 * 2 ^ 12 + b2 % 64 * 2 ^ 6 by omega] at this
    exact this
  rw [e1, e2, e3]

private theorem subRes32 (x y : BitVec 32) :
    (BitVec.ofNat 32 (x.toNat + (~~~y).toNat + true.toNat)).toNat =
      (x.toNat + 4294967296 - y.toNat) % 4294967296 := by
  simp only [BitVec.toNat_ofNat, BitVec.toNat_not, Bool.toNat_true]
  have := y.isLt; congr 1; omega

theorem toInt32_cond (x : BitVec 32) :
    x.toInt = if x.toNat < 2147483648 then (x.toNat : Int) else (x.toNat : Int) - 4294967296 := by
  rw [BitVec.toInt_eq_toNat_cond]; by_cases h : x.toNat < 2147483648
  · rw [ite_eq_left_iff.mpr (fun h' => absurd (by omega) h'), ite_eq_left_iff.mpr (fun h' => absurd h h')]
  · rw [ite_eq_right (by omega), ite_eq_right h]; rfl

private theorem decide_beq_decide (A B : Prop) [Decidable A] [Decidable B] :
    (decide A == decide B) = decide (A ↔ B) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

/-- The signed condition of a 32-bit `CMP` (`N = V`: `GE`), as a comparison of the operands. -/
theorem sub_flags_nv32 (x y : BitVec 32) :
    ((addSub x y true).2.n == (addSub x y true).2.v) = decide (y.toInt ≤ x.toInt) := by
  simp only [addSub, addWithCarry, ite_true, BitVec.msb_eq_decide]
  rw [toInt32_cond (BitVec.ofNat 32 _), subRes32, toInt32_cond (~~~y), toInt32_cond x, toInt32_cond y]
  have := x.isLt; have := y.isLt
  simp only [Bool.toNat_true, BitVec.toNat_not, Nat.reducePow, Nat.reduceSub, decide_not]
  rw [← decide_not, decide_beq_decide]
  apply decide_eq_decide.mpr
  by_cases h : y.toNat ≤ x.toNat
  · rw [show x.toNat + 4294967296 - y.toNat = (x.toNat - y.toNat) + 4294967296 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    split <;> split <;> split <;> split <;> omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    split <;> split <;> split <;> split <;> omega

theorem toInt32_of_lt (x : BitVec 32) (h : x.toNat < 2147483648) : x.toInt = (x.toNat : Int) := by
  rw [toInt32_cond, if_pos h]

set_option maxHeartbeats 20000000 in
theorem correctness (rt : List (Nat × Nat)) (stack : Nat) (H : RtReady) (hst : 24 ≤ stack) :
    RtContract Extracted.program Extracted.entry rt stack H decoderuneSpec := by
  rintro s hpc ⟨⟨hra, hrb, hal, hsb, -, hsa, hacc⟩, ⟨⟨hpb, hrd⟩, hk⟩, hout, hg, -⟩
  obtain ⟨hg1, hg2, hg3⟩ := hg 0 rfl
  simp only [decoderuneSpec, argWords, wordsFrom_succ, wordsFrom_zero, arg, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd, Nat.zero_add, List.mem_cons, List.not_mem_nil, or_false, forall_eq, calleeStack,
    outside_cons, outside_nil, and_true] at hpb hrd hk hout ⊢
  simp only [decoderuneSpec] at hacc hsa ⊢
  have h1i : (s.regs 1).toInt = ((s.regs 1).toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have h2i : (s.regs 2).toInt = ((s.regs 2).toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  by_cases hn0 : 0 < (s.regs 1).toNat
  · have hr := hrd hn0
    janus_run [h1i, h2i, and_sshr_sub]
    all_goals (apply RtPost.intro <;> (try rfl) <;> (try simp only [setReg_apply]; done))
    all_goals (try (simp only [calleeStack, List.append_nil]; janus_frame))
    all_goals (simp only [argWords, wordsFrom_succ, wordsFrom_zero, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceAdd, Nat.zero_add, setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    all_goals
      try simp only [h1i, h2i] at *
      try clear h1i h2i
      have hb0 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat) 1
      have hb1 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 1) 1
      have hb2 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 2) 1
      have hb3 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 3) 1
      simp only [Nat.pow_one] at hb0 hb1 hb2 hb3
      rw [decodeRune_eq_arith]; unfold decodeRuneA
      simp only [strBytes_length, isCont, byteAt_strBytes', ← Nat.add_assoc,
        Bool.and_eq_true, decide_eq_true_eq]
      try simp (disch := first | omega | decide |
          (simp (disch := omega) only [r2, r3, r4, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega))
        only [r2, r3, r4, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add,
        BitVec.toNat_sub, sub_flags_nv32, toInt32_of_lt, Nat.reducePow, Nat.reduceMod] at *
      try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.or_eq_true, beq_iff_eq, Bool.not_eq_false, Bool.and_eq_false_iff, Bool.not_eq_false'] at *
      try clear hacc
      try clear hg2
      try clear hr
      try clear hrd
      try clear hout
      try clear hpc
      try clear hg
      try clear hra
      try clear hrb
      try clear hsa
      try simp (disch := omega) only [if_pos, if_neg]
      first | omega | (simp only [true_and, and_true]; omega)
  · janus_run [h1i, h2i, and_sshr_sub]
    all_goals (apply RtPost.intro <;> (try rfl) <;> (try simp only [setReg_apply]; done))
    all_goals (try (simp only [calleeStack, List.append_nil]; janus_frame))
    all_goals (simp only [argWords, wordsFrom_succ, wordsFrom_zero, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceAdd, Nat.zero_add, setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    all_goals
      try simp only [h1i, h2i] at *
      try clear h1i h2i
      have hb0 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat) 1
      have hb1 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 1) 1
      have hb2 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 2) 1
      have hb3 := Memory.readLE_lt s.mem ((s.regs 0).toNat + (s.regs 2).toNat + 3) 1
      simp only [Nat.pow_one] at hb0 hb1 hb2 hb3
      rw [decodeRune_eq_arith]; unfold decodeRuneA
      simp only [strBytes_length, isCont, byteAt_strBytes', ← Nat.add_assoc,
        Bool.and_eq_true, decide_eq_true_eq]
      try simp (disch := first | omega | decide |
          (simp (disch := omega) only [r2, r3, r4, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega))
        only [r2, r3, r4, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add,
        BitVec.toNat_sub, sub_flags_nv32, toInt32_of_lt, Nat.reducePow, Nat.reduceMod] at *
      try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.or_eq_true, beq_iff_eq, Bool.not_eq_false, Bool.and_eq_false_iff, Bool.not_eq_false'] at *
      try clear hacc
      try clear hg2
      try clear hr
      try clear hrd
      try clear hout
      try clear hpc
      try clear hg
      try clear hra
      try clear hrb
      try clear hsa
      try simp (disch := omega) only [if_pos, if_neg]
      first | omega | (simp only [true_and, and_true]; omega)
end Proof
