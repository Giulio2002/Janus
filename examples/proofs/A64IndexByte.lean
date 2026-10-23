import Extracted

/-!
# `A64IndexByte(b []byte, c byte)`: `bytes.IndexByte` on 64 bytes through `internal/bytealg`'s SIMD scan

**Guarantee.** For every slice `b` (pointer `p`, length `n`, capacity `cap`), every byte `c` and
every Go call state `s` of `example.com/basic.A64IndexByte` such that
* the stack-growth prologue falls through (`GuardOK s 0`), `SP` is aligned and the bytes from
  56 below to 16 above `SP` are writable (the 48-byte frame, the saved frame pointer, and the
  spill slot of `p` in the caller's argument area),
* the slice has length 64, its data starts on a 32-byte boundary, the 64 bytes are readable,
  and they do not overlap that stack window,

the call returns (never faulting or panicking), obeys the ABI, and returns in `X0` the index of
the first of the 64 bytes that equals `c`, or `-1` if none does (`indexOf`, as a 64-bit
two's-complement value). Only the low byte of `X3` is the argument `c` (the ABI leaves the
upper bits unspecified), so the statement uses `c.toNat % 256`.

**What this covers.** `A64IndexByte` calls `internal/bytealg.IndexByte`, which jumps to
`IndexByteString`. The proof executes all of it instruction by instruction from the extracted
words: `DUP` of `c` and of the magic constant `0x40100401` into vector registers, then, per
32-byte block, `LD1 {v1.16b, v2.16b}` with post-increment, two `CMEQ .16B`, the quick
"any match?" test (`ORR`, `ADDP .2D`, `UMOV`), and on a match or at the end the syndrome
computation (`AND` with the magic constant, two `ADDP .16B`, `UMOV`), whose two bits per byte
locate the first match through `RBIT` and `CLZ`. The two semantic facts the proof needs about
this code are proved here once, for arbitrary register contents: `loopTest` (the quick test is
zero iff no byte of the block matches: two vectors of byte masks cannot add up to `0 mod 2^64`
otherwise) and `syndrome` (the syndrome is `Σ 4^i·[byte i = c]`), and `ctzN_synd`
(`Janus.Tactic.Vector`) turns its trailing zeros into the first matching index.

**Limits.** The 32-byte alignment of the data is a precondition: for an unaligned slice the
code also reads the bytes of the enclosing aligned blocks outside the slice and masks them out,
a path this theorem does not cover.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- The index of the first of the `n` bytes at `p` that equals `c`, or `-1`. -/
def indexOf (m : Memory) (p c : Nat) : Nat → Int
  | 0 => -1
  | n + 1 =>
    if m.readLE p 1 = c then 0
    else
      let r := indexOf m (p + 1) c n
      if r < 0 then -1 else r + 1

/-- The byte predicate of a 32-byte block held in two registers. -/
def blk (x1 x2 c : Nat) (i : Nat) : Bool :=
  if i < 16 then decide (elem x1 8 i = c % 256) else decide (elem x2 8 (i - 16) = c % 256)

/-- `firstTrue` only looks at the first `n` values. -/
theorem firstTrue_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = g i) :
    firstTrue f n = firstTrue g n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [firstTrue, h 0 (by omega)]
    rw [ih (fun i hi => h (i + 1) (by omega))]

/-- `synd` only looks at the first `n` values. -/
theorem synd_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = g i) :
    synd f n = synd g n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [synd, h 0 (by omega)]
    rw [ih (fun i hi => h (i + 1) (by omega))]

/-- The first match index is at most `n`. -/
theorem firstTrue_le (f : Nat → Bool) (n : Nat) : firstTrue f n ≤ n := by
  induction n generalizing f with
  | zero => simp [firstTrue]
  | succ n ih => simp only [firstTrue]; split <;> have := ih (fun i => f (i + 1)) <;> omega

/-- If something matches, the first match index is below `n`. -/
theorem firstTrue_lt (f : Nat → Bool) (n : Nat) (h : ∃ i < n, f i = true) : firstTrue f n < n := by
  induction n generalizing f with
  | zero => obtain ⟨i, hi, _⟩ := h; omega
  | succ n ih =>
    simp only [firstTrue]
    split
    · omega
    · rename_i h0
      obtain ⟨i, hi, hfi⟩ := h
      have hi0 : i ≠ 0 := by rintro rfl; exact h0 hfi
      have := ih (fun i => f (i + 1)) ⟨i - 1, by omega, by
        show f (i - 1 + 1) = true; rw [show i - 1 + 1 = i by omega]; exact hfi⟩
      omega

/-- `indexOf` is the first matching index (`firstTrue`) if a byte matches, else `-1`. -/
theorem indexOf_eq (m : Memory) (p c n : Nat) :
    indexOf m p c n = if ∃ i < n, m.readLE (p + i) 1 = c
      then (firstTrue (fun i => decide (m.readLE (p + i) 1 = c)) n : Int) else -1 := by
  induction n generalizing p with
  | zero => simp [indexOf]
  | succ n ih =>
    simp only [indexOf, firstTrue]
    by_cases h0 : m.readLE p 1 = c
    · have : ∃ i < n + 1, m.readLE (p + i) 1 = c := ⟨0, by omega, by rw [Nat.add_zero]; exact h0⟩
      simp only [h0, this, Nat.add_zero, decide_true, ite_true]; rfl
    · have e : (fun i => decide (m.readLE (p + (i + 1)) 1 = c)) =
          (fun i => decide (m.readLE (p + 1 + i) 1 = c)) := by
        funext i; rw [show p + (i + 1) = p + 1 + i by omega]
      have e2 : (∃ i < n + 1, m.readLE (p + i) 1 = c) ↔ ∃ i < n, m.readLE (p + 1 + i) 1 = c := by
        constructor
        · rintro ⟨i, hi, hfi⟩
          cases i with
          | zero => simp at hfi; exact absurd hfi h0
          | succ i => exact ⟨i, by omega, by rw [show p + 1 + i = p + (i + 1) by omega]; exact hfi⟩
        · rintro ⟨i, hi, hfi⟩
          exact ⟨i + 1, by omega, by rw [show p + (i + 1) = p + 1 + i by omega]; exact hfi⟩
      simp only [h0, ite_false, Nat.add_zero, decide_false, Bool.false_eq_true]
      rw [ih (p + 1), e]
      by_cases hx : ∃ i < n, m.readLE (p + 1 + i) 1 = c
      · have := e2.mpr hx
        simp only [hx, this, ite_true]
        have : ¬ ((firstTrue (fun i => decide (m.readLE (p + 1 + i) 1 = c)) n : Int) < 0) := by omega
        simp only [this, ite_false]; push_cast; rfl
      · have : ¬ ∃ i < n + 1, m.readLE (p + i) 1 = c := fun h => hx (e2.mp h)
        simp only [hx, this, ite_false]; decide

/-- The bytes of the magic constant `0x40100401` replicated by `DUP v5.4s`: `1, 4, 16, 64, 1, ...`. -/
theorem mask_elems : ∀ i < 16, elem (ofElems 32 4 fun _ => 1074791425) 8 i = 4 ^ (i % 4) := by
  decide

set_option maxHeartbeats 4000000 in
/-- **The syndrome.** What `AND` with the magic constant and two `ADDP .16B` compute from the
two `CMEQ` masks of a 32-byte block held in `x1:x2`, read back as `UMOV x6, v6.d[0]`: two bits
per byte, bit `2i` set iff byte `i` equals `c`. The left side is exactly the term the executor
produces. -/
theorem syndrome (x1 x2 c : Nat) :
    elem
      (threeSameOp false 0 23 128
        (threeSameOp false 0 23 128
            ((threeSameOp true 0 17 128 x1
                    ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0 %
                  340282366920938463463374607431768211456 &&&
                (ofElems 32 4 fun _ => 1074791425) % 340282366920938463463374607431768211456) %
              340282366920938463463374607431768211456)
            ((threeSameOp true 0 17 128 x2
                    ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0 %
                  340282366920938463463374607431768211456 &&&
                (ofElems 32 4 fun _ => 1074791425) % 340282366920938463463374607431768211456) %
              340282366920938463463374607431768211456)
            0 %
          340282366920938463463374607431768211456)
        (threeSameOp false 0 23 128
            ((threeSameOp true 0 17 128 x1
                    ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0 %
                  340282366920938463463374607431768211456 &&&
                (ofElems 32 4 fun _ => 1074791425) % 340282366920938463463374607431768211456) %
              340282366920938463463374607431768211456)
            ((threeSameOp true 0 17 128 x2
                    ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0 %
                  340282366920938463463374607431768211456 &&&
                (ofElems 32 4 fun _ => 1074791425) % 340282366920938463463374607431768211456) %
              340282366920938463463374607431768211456)
            0 %
          340282366920938463463374607431768211456)
        0)
      64 0 =
    synd (blk x1 x2 c) 32 := by
  rw [elem_64_bytes]
  simp (disch := decide) only [elem_mod_2_128, elem_addp, pairElem, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceSub, Nat.reducePow, Nat.reduceLT, ite_true, ite_false, elem_and, elem_cmeq,
    elem_ofElems]
  simp (disch := decide) only [mask_elems, Nat.reduceMod, Nat.reducePow, ite_land_nat, Nat.reduceAnd]
  simp (disch := decide) only [ite_add_ite_mod]
  simp (disch := decide) only [ite4_mod]
  simp only [ite_eq_mul_toNat, synd, blk, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false, Nat.reduceSub]
  omega

/-- A vector of all-zero masks is zero. -/
theorem maskSum_eq_zero (f : Nat → Bool) (n : Nat) (h : ∀ k < n, f k = false) : maskSum f n = 0 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [maskSum, h 0 (by omega), Bool.toNat_false, Nat.mul_zero, Nat.zero_add]
    rw [ih _ (fun k hk => h (k + 1) (by omega))]

/-- "No byte of the block matches", grouped the way the quick test sees the bytes. -/
theorem blk_split (x1 x2 c : Nat) :
    (∀ i < 32, blk x1 x2 c i = false) ↔
      (∀ k < 8, decide (elem x1 8 k = c % 256 ∨ elem x2 8 k = c % 256) = false ∧
        decide (elem x1 8 (8 + k) = c % 256 ∨ elem x2 8 (8 + k) = c % 256) = false) := by
  constructor
  · intro h k hk
    have h1 := h k (by omega); have h2 := h (8 + k) (by omega)
    have h3 := h (16 + k) (by omega); have h4 := h (24 + k) (by omega)
    simp only [blk, show k < 16 by omega, show 8 + k < 16 by omega, show ¬ 16 + k < 16 by omega,
      show ¬ 24 + k < 16 by omega, ite_true, ite_false, decide_eq_false_iff_not,
      show 16 + k - 16 = k by omega, show 24 + k - 16 = 8 + k by omega] at h1 h2 h3 h4
    simp only [decide_eq_false_iff_not, not_or]
    exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · intro h i hi
    simp only [decide_eq_false_iff_not, not_or] at h
    simp only [blk]
    split
    · rcases (by omega : i < 8 ∨ 8 ≤ i) with h' | h'
      · simpa using (h i h').1.1
      · have := (h (i - 8) (by omega)).2.1; rw [show 8 + (i - 8) = i by omega] at this; simpa using this
    · rcases (by omega : i < 24 ∨ 24 ≤ i) with h' | h'
      · simpa using (h (i - 16) (by omega)).1.2
      · have := (h (i - 24) (by omega)).2.2
        rw [show 8 + (i - 24) = i - 16 by omega] at this; simpa using this

set_option maxHeartbeats 4000000 in
/-- **The quick test.** `ORR` of the two `CMEQ` masks, `ADDP .2D` and `UMOV` give a value that is
zero iff no byte of the 32-byte block `x1:x2` equals `c` (adding the two 64-bit halves cannot
cancel, because both are vectors of `0x00`/`0xFF` bytes: `maskSum_add_mod`). The left side is
exactly the branch condition of the executor's `CBZ`. -/
theorem loopTest (x1 x2 c : Nat) :
    ((elem (threeSameOp true 0 17 128 x1 ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0) 64 0 |||
          elem (threeSameOp true 0 17 128 x2 ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0) 64 0) +
        (elem (threeSameOp true 0 17 128 x1 ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0) 64 1 |||
          elem (threeSameOp true 0 17 128 x2 ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0) 64 1)) %
      18446744073709551616 = 0 ↔ ∀ i < 32, blk x1 x2 c i = false := by
  rw [← elem_or, ← elem_or, elem_64_bytes, elem_64_bytes]
  simp (disch := decide) only [elem_or, elem_cmeq, elem_mod_2_128, elem_ofElems, Nat.reduceMul, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, ite_lor_ite]
  simp only [ite_eq_mul_toNat]
  rw [blk_split]
  constructor
  · intro h
    have := maskSum_add_mod (fun k => decide (elem x1 8 k = c % 256 ∨ elem x2 8 k = c % 256))
      (fun k => decide (elem x1 8 (8 + k) = c % 256 ∨ elem x2 8 (8 + k) = c % 256)) 8 (by
        simp only [maskSum, Nat.reduceAdd, Nat.reducePow]; omega)
    exact this
  · intro h
    have h1 := maskSum_eq_zero (fun k => decide (elem x1 8 k = c % 256 ∨ elem x2 8 k = c % 256)) 8
      (fun k hk => (h k hk).1)
    have h2 := maskSum_eq_zero (fun k => decide (elem x1 8 (8 + k) = c % 256 ∨ elem x2 8 (8 + k) = c % 256)) 8
      (fun k hk => (h k hk).2)
    simp only [maskSum, Nat.reduceAdd] at h1 h2
    omega


/-- The block predicate on loaded memory is the byte comparison. -/
theorem blk_readLE (m : Memory) {a b : Nat} (c : Nat) (h : b = a + 16) {i : Nat} (hi : i < 32) :
    blk (m.readLE a 16) (m.readLE b 16) c i = decide (m.readLE (a + i) 1 = c % 256) := by
  subst h
  unfold blk
  split
  · rw [elem_readLE_8 m (by omega)]
  · rw [elem_readLE_8 m (by omega), show a + 16 + (i - 16) = a + i by omega]

/-- The return value computed at `tail`: block start + `CLZ(RBIT(syndrome)) >> 1` - `p`. -/
theorem fin_arith (p : BitVec 64) (b k y : Nat) (r : Int) (hy : y = 2 * k) (hk : k < 32)
    (hb : b = 32 ∨ b = 64) (hr : r = ((b - 32 + k : Nat) : Int)) :
    p + BitVec.ofNat 64 b - 32#64 + BitVec.ofNat 64 y >>> 1 - p = BitVec.ofInt 64 r := by
  subst hy hr
  apply BitVec.eq_of_toNat_eq
  rcases hb with rfl | rfl <;>
  · simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow]
    have := p.isLt
    simp only [Nat.reducePow, Nat.reduceSub]
    omega

/-- `ANDS x9, x0, #0x1f` of an aligned pointer is 0. -/
theorem hand31 (p : BitVec 64) (hpal : p.toNat % 32 = 0) : p &&& 31#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (31#64).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simpa using hpal

/-- `AND x3, x0, #~0x1f` of an aligned pointer is the pointer. -/
theorem hand (p : BitVec 64) (hpal : p.toNat % 32 = 0) : p &&& 18446744073709551584#64 = p := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (18446744073709551584#64).toNat = (2 ^ 59 - 1) * 2 ^ 5 from rfl]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hj : 5 ≤ j
  · by_cases hj' : j < 64
    · simp [hj, show j - 5 < 59 by omega]
    · have : p.toNat.testBit j = false := Nat.testBit_lt_two_pow (by
        have := p.isLt; exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · have : p.toNat.testBit j = false := by
      rw [← Nat.mod_add_div p.toNat 32, hpal, Nat.zero_add, show (32:Nat) = 2^5 from rfl,
        Nat.testBit_two_pow_mul]; simp; omega
    simp [hj, this]

/-- A byte of the 64 is in the first or the second 32-byte block. -/
theorem exists64 (P : Nat → Prop) : (∃ i < 64, P i) ↔ (∃ i < 32, P i) ∨ (∃ i < 32, P (32 + i)) := by
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases h' : i < 32
    · exact Or.inl ⟨i, h', h⟩
    · exact Or.inr ⟨i - 32, by omega, by rw [show 32 + (i - 32) = i by omega]; exact h⟩
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨i, by omega, h⟩
    · exact ⟨32 + i, by omega, h⟩

/-- The result when neither 32-byte block holds `c`. -/
theorem final_none (m : Memory) (a c : Nat) (B0 B1 : Nat → Bool)
    (h0 : ∀ i < 32, B0 i = decide (m.readLE (a + i) 1 = c))
    (h1 : ∀ i < 32, B1 i = decide (m.readLE (a + (32 + i)) 1 = c))
    (n0 : ∀ i < 32, B0 i = false) (n1 : ∀ i < 32, B1 i = false) : indexOf m a c 64 = -1 := by
  rw [indexOf_eq]
  have : ¬∃ i < 64, m.readLE (a + i) 1 = c := by
    rw [exists64]
    rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · have := n0 i hi; rw [h0 i hi] at this; simp [h] at this
    · have := n1 i hi; rw [h1 i hi] at this; simp [h] at this
  simp only [this, ite_false]

/-- The result when the first block holds `c`. -/
theorem final_block0 (m : Memory) (a c : Nat) (B0 : Nat → Bool)
    (h0 : ∀ i < 32, B0 i = decide (m.readLE (a + i) 1 = c)) (e0 : ∃ i < 32, B0 i = true) :
    indexOf m a c 64 = ((32 - 32 + firstTrue B0 32 : Nat) : Int) := by
  rw [indexOf_eq]
  obtain ⟨i, hi, hb⟩ := e0
  have hm : ∃ i < 32, m.readLE (a + i) 1 = c := ⟨i, hi, by rw [h0 i hi] at hb; simpa using hb⟩
  have hm64 : ∃ i < 64, m.readLE (a + i) 1 = c := (exists64 _).mpr (Or.inl hm)
  have e := firstTrue_add (fun i => decide (m.readLE (a + i) 1 = c)) 32 32
  simp only [Nat.reduceAdd] at e
  have hm' : ∃ i < 32, decide (m.readLE (a + i) 1 = c) = true := by
    obtain ⟨j, hj, h⟩ := hm; exact ⟨j, hj, by simp [h]⟩
  simp only [hm64, ite_true, e, hm', Nat.sub_self, Nat.zero_add]
  rw [firstTrue_congr (fun i hi => (h0 i hi).symm)]

/-- The result when only the second block holds `c`. -/
theorem final_block1 (m : Memory) (a c : Nat) (B0 B1 : Nat → Bool)
    (h0 : ∀ i < 32, B0 i = decide (m.readLE (a + i) 1 = c))
    (h1 : ∀ i < 32, B1 i = decide (m.readLE (a + (32 + i)) 1 = c))
    (n0 : ∀ i < 32, B0 i = false) (e1 : ∃ i < 32, B1 i = true) :
    indexOf m a c 64 = ((64 - 32 + firstTrue B1 32 : Nat) : Int) := by
  rw [indexOf_eq]
  obtain ⟨i, hi, hb⟩ := e1
  have hm : ∃ i < 32, m.readLE (a + (32 + i)) 1 = c := ⟨i, hi, by rw [h1 i hi] at hb; simpa using hb⟩
  have hm64 : ∃ i < 64, m.readLE (a + i) 1 = c := (exists64 _).mpr (Or.inr hm)
  have e := firstTrue_add (fun i => decide (m.readLE (a + i) 1 = c)) 32 32
  simp only [Nat.reduceAdd] at e
  have hn : ¬∃ i < 32, decide (m.readLE (a + i) 1 = c) = true := by
    rintro ⟨j, hj, h⟩; have := n0 j hj; rw [h0 j hj] at this; rw [this] at h; exact absurd h (by decide)
  simp only [hm64, ite_true, e, hn, ite_false]
  rw [firstTrue_congr (g := B1) (fun i hi => (h1 i hi).symm)]

/-- A non-zero syndrome has a match. -/
theorem exists_of_synd {f : Nat → Bool} (h : ¬synd f 32 = 0) : ∃ i < 32, f i = true := by
  refine Classical.byContradiction fun hc => h (synd_eq_zero f 32 (fun i hi => ?_))
  cases hf : f i
  · rfl
  · exact absurd ⟨i, hi, hf⟩ hc

/-- A zero syndrome has no match. -/
theorem none_of_synd {f : Nat → Bool} (h : synd f 32 = 0) : ∀ i < 32, f i = false := by
  intro i hi
  cases hf : f i
  · rfl
  · exact absurd h (synd_ne_zero f 32 ⟨i, hi, hf⟩)

/-- `RBIT` stays within 64 bits. -/
theorem rbit_mod (x : Nat) : rbitNat 64 x % 18446744073709551616 = rbitNat 64 x :=
  Nat.mod_eq_of_lt (rbitNat_lt 64 x)

set_option maxHeartbeats 8000000 in
/-- **The theorem.** -/
theorem correctness (p n cap c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, n, cap, c]
      (fun s => GuardOK s 0 ∧ StackOK s 56 16 ∧ n.toNat = 64 ∧ p.toNat % 32 = 0 ∧
        Ptr s.mem p 64 false ∧ Disjoint p.toNat 64 (s.sp.toNat - 56) 72)
      (fun s s' => s'.regs 0 = BitVec.ofInt 64 (indexOf s.mem p.toNat (c.toNat % 256) 64)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hn, hpal, ⟨hA, hA'⟩, hd⟩
  janus_intro hs
  simp only [Disjoint] at hd
  have h1 := hand p hpal
  have h2 := hand31 p hpal
  -- Executes A64IndexByte, IndexByte and IndexByteString on the aligned path: the first block's
  -- quick test decides between `end` and a second iteration; the second ends the loop (`BLS`).
  janus_run [h1, h2]
  -- The two branch conditions and the result as statements about the bytes.
  all_goals simp only [loopTest, syndrome] at *
  all_goals
    have hF0 : ∀ i < 32, blk (s.mem.readLE p.toNat 16) (s.mem.readLE (p.toNat + 16) 16) c.toNat i =
        decide (s.mem.readLE (p.toNat + i) 1 = c.toNat % 256) := fun i hi => blk_readLE _ _ rfl hi
    have hF1 : ∀ i < 32, blk (s.mem.readLE (p.toNat + 32) 16) (s.mem.readLE (p.toNat + 48) 16) c.toNat i =
        decide (s.mem.readLE (p.toNat + (32 + i)) 1 = c.toNat % 256) := fun i hi => by
      rw [blk_readLE _ _ (by omega) hi, Nat.add_assoc]
  · -- no match in either block
    rename_i hT
    rw [final_none _ _ _ _ _ hF0 hF1 hT (none_of_synd hbr)]; decide
  · -- the first match is in the second block
    rename_i hT
    have he := exists_of_synd hbr
    rw [rbit_mod]
    rw [clzNat_rbitNat, ctzN_synd _ 32 64 (by omega) he]
    exact fin_arith p 64 _ _ _ rfl (firstTrue_lt _ _ he) (Or.inr rfl)
      (final_block1 _ _ _ _ _ hF0 hF1 hT he)
  · -- impossible: a match in the first block gives a non-zero syndrome
    rename_i hT
    exact absurd (none_of_synd hbr) hT
  · -- the first match is in the first block
    have he := exists_of_synd hbr
    rw [rbit_mod]
    rw [clzNat_rbitNat, ctzN_synd _ 32 64 (by omega) he]
    exact fin_arith p 32 _ _ _ rfl (firstTrue_lt _ _ he) (Or.inl rfl) (final_block0 _ _ _ _ hF0 he)

end Proof
