import Extracted

/-!
# `runtime.memequal` meets the `Memequal` contract (all lengths)

**Guarantee.** For every stack bound `d`, the machine code of Go 1.26's `runtime.memequal(a, b, n)`
(`internal/bytealg/equal_arm64.s`) satisfies `Janus.Contracts.Mem.Memequal … d`: from every call
state with the contract's precondition (stack guard and ABI conditions, the `n` bytes at `a` and at
`b` readable) it returns to `X30` without faulting, keeps `SP`, `X18`, `X28`, `X29` and `FPCR`,
changes **no memory at all** (stronger than the contract's window, which is what `Memequal`'s
`nargs = 0` relies on: `strequal` and `memequal_varlen` call it without spill slots), and returns
in the low byte of `X0` whether the `n` bytes at `a` equal the `n` bytes at `b`.

**What the code does, and how it is proved.** `NOFRAME` assembly, by label:
* the shortcuts: `n = 0` and `a = b` return `true`, `n = 1` compares one byte;
* `n ≥ 64`: the SIMD loop at `+0x28` (`loop64`, by induction on the 64-byte chunks left): two
  `LD1 {v0.2d-v3.2d}`, four `CMEQ .2D`, three `AND`, two `UMOV` and `CBZ` (the even and the odd
  words of the chunk, `beq64`), then `n % 64` bytes from `chunk16`;
* `chunk16` at `+0x6c`: the 16-byte `LDP` loop at `+0x78` (`loop16`, by induction) for the whole
  16-byte chunks (`n AND NOT 15`, `mask_nat`), then the tail;
* the tail at `+0xa0` (`tail`, `n < 16`, one case per length): two overlapping 8-byte words for
  `8 ≤ n < 16`, two overlapping 4-byte words for `4 ≤ n < 8` (`win`: two windows of `w` bytes at `0`
  and `n - w` cover `n ≤ 2w` bytes), a halfword and a byte, a byte.
Each label lemma ends in `Fin`: the fields a run never changes, and the comparison result.

**Assumptions.** Only the contract's precondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Mem

namespace Proof

/-- The end of a run of `memequal` from the state `S` (at some label): `SP`, memory, `X18`,
`X28`, `X29` and the system registers of `S`, and the boolean `b` in the low byte of `X0`. -/
def Fin (S S' : State) (b : Bool) : Prop :=
  S'.sp = S.sp ∧ S'.mem = S.mem ∧ S'.regs 18 = S.regs 18 ∧ S'.regs 28 = S.regs 28 ∧
    S'.regs 29 = S.regs 29 ∧ S'.dczid = S.dczid ∧ S'.tpidr = S.tpidr ∧ S'.fpcr = S.fpcr ∧
    (S'.regs 0).toNat % 256 = b.toNat

/-- Two reads are equal iff their bytes are. -/
theorem readLE_eq_iff_bytes (m : Memory) : ∀ (n a b : Nat),
    m.readLE a n = m.readLE b n ↔ ∀ i, i < n → m.bytes (a + i) = m.bytes (b + i)
  | 0, a, b => by simp
  | n + 1, a, b => by
    rw [show n + 1 = 1 + n by omega, Tactic.readLE_add_eq_iff, readLE_eq_iff_bytes m n (a + 1) (b + 1)]
    have h1 : m.readLE a 1 = m.readLE b 1 ↔ m.bytes a = m.bytes b := by
      simp only [Memory.readLE, Nat.mul_zero, Nat.add_zero]
      exact ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]⟩
    rw [h1]
    constructor
    · rintro ⟨h0, h⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · have := h i (by omega); rwa [show a + 1 + i = a + (i + 1) by omega,
          show b + 1 + i = b + (i + 1) by omega] at this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have := h (i + 1) (by omega)
      rwa [show a + (i + 1) = a + 1 + i by omega, show b + (i + 1) = b + 1 + i by omega] at this

/-- Two overlapping windows of `w` bytes (at `0` and at `k - w`) cover `k ≤ 2w` bytes. -/
theorem win (m : Memory) (a b w k : Nat) (h1 : w ≤ k) (h2 : k ≤ 2 * w) :
    m.readLE a k = m.readLE b k ↔
      m.readLE a w = m.readLE b w ∧ m.readLE (a + (k - w)) w = m.readLE (b + (k - w)) w := by
  simp only [readLE_eq_iff_bytes]
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), fun i hi => by
      have := h (k - w + i) (by omega); rwa [← Nat.add_assoc, ← Nat.add_assoc] at this⟩
  · rintro ⟨h, h'⟩ i hi
    by_cases hw : i < w
    · exact h i hw
    · have := h' (i - (k - w)) (by omega)
      rwa [Nat.add_assoc, Nat.add_assoc, show k - w + (i - (k - w)) = i by omega] at this

theorem beq_swap (a b : Nat) : (a == b) = (b == a) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩

theorem rd_mod (m : Memory) (a n : Nat) (h : n ≤ 8) : m.readLE a n % 18446744073709551616 = m.readLE a n :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (m.readLE_lt a n) (Nat.pow_le_pow_right (by decide) h))
theorem rd_mod1 (m : Memory) (a : Nat) : m.readLE a 1 % 18446744073709551616 = m.readLE a 1 := rd_mod m a 1 (by decide)
theorem rd_mod2 (m : Memory) (a : Nat) : m.readLE a 2 % 18446744073709551616 = m.readLE a 2 := rd_mod m a 2 (by decide)
theorem rd_mod4 (m : Memory) (a : Nat) : m.readLE a 4 % 18446744073709551616 = m.readLE a 4 := rd_mod m a 4 (by decide)

/-- How a comparison result ends up in `X0`. -/
theorem fin_res {r : W64} {u v : Nat} {P : Prop} (hd : u = v ↔ P) (h1 : P → r.toNat % 256 = 1)
    (h0 : ¬P → r.toNat % 256 = 0) : r.toNat % 256 = (u == v).toNat := by
  by_cases hP : P
  · rw [h1 hP, (beq_iff_eq).2 (hd.2 hP)]; rfl
  · rw [h0 hP, beq_false_of_ne (fun h => hP (hd.1 h))]; rfl

set_option maxHeartbeats 8000000 in
theorem tail (S : State) (x y k : Nat) (hk : k < 16) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0xa0))
    (h0 : S.regs 0 = BitVec.ofNat 64 x) (h1 : S.regs 1 = BitVec.ofNat 64 y)
    (h2 : S.regs 2 = BitVec.ofNat 64 k)
    (hx : x + k ≤ 2 ^ 48) (hy : y + k ≤ 2 ^ 48)
    (hax : S.mem.accessible x k false = true)
    (hay : S.mem.accessible y k false = true)
    (hl1 : (S.regs 30).toNat % 4 = 0) (hl2 : (S.regs 30).toNat < 2 ^ 48) :
    ReachesRet Extracted.program (S.regs 30) S (fun S' => Fin S S'
      (S.mem.readLE x k == S.mem.readLE y k)) := by
  have hw : ∀ w, w ≤ k → k ≤ 2 * w → (S.mem.readLE y k = S.mem.readLE x k ↔
      S.mem.readLE y w = S.mem.readLE x w ∧ S.mem.readLE (y + (k - w)) w = S.mem.readLE (x + (k - w)) w) :=
    fun w h1 h2 => win S.mem y x w k h1 h2
  have h3 := Tactic.readLE_add_eq_iff S.mem y x 2 1
  simp only [Nat.reduceAdd] at h3
  rw [beq_swap]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
    k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    janus_run [xor_eq_zero_iff, rd_mod1, rd_mod2, rd_mod4]
  all_goals
    refine ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl, ?_⟩
    first
    | (refine fin_res (hw 8 (by omega) (by omega)) ?_ ?_ <;> clear hw h3 <;> intro hP <;> simp_all [setReg])
    | (refine fin_res (hw 4 (by omega) (by omega)) ?_ ?_ <;> clear hw h3 <;> intro hP <;> simp_all [setReg])
    | (refine fin_res h3 ?_ ?_ <;> clear hw h3 <;> intro hP <;> simp_all [setReg])
    | (refine fin_res (hw 2 (by omega) (by omega)) ?_ ?_ <;> clear hw h3 <;> intro hP <;> simp_all [setReg])
    | (refine fin_res (hw 1 (by omega) (by omega)) ?_ ?_ <;> clear hw h3 <;> intro hP <;> simp_all [setReg])
    | (simp [setReg])


/-- `Fin` is about the fields a run of `memequal` never changes, so it transfers along them. -/
theorem Fin.of {S S1 S' : State} {b b' : Bool} (h : Fin S1 S' b) (hsp : S1.sp = S.sp)
    (hm : S1.mem = S.mem) (h18 : S1.regs 18 = S.regs 18) (h28 : S1.regs 28 = S.regs 28)
    (h29 : S1.regs 29 = S.regs 29) (hdz : S1.dczid = S.dczid) (htp : S1.tpidr = S.tpidr)
    (hfc : S1.fpcr = S.fpcr) (hb : b = b') : Fin S S' b' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  subst hb
  exact ⟨a1.trans hsp, a2.trans hm, a3.trans h18, a4.trans h28, a5.trans h29, a6.trans hdz,
    a7.trans htp, a8.trans hfc, a9⟩

theorem rr_mono {p : Program} {ret : W64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', h1, h2, h3⟩ := h; exact ⟨k, s', h1, h2, hQ _ h3⟩

/-- Comparing `n + k` bytes is comparing the first `n` and then the next `k`. -/
theorem beq_add (m : Memory) (a b n k : Nat) :
    (m.readLE a (n + k) == m.readLE b (n + k)) =
      ((m.readLE a n == m.readLE b n) && (m.readLE (a + n) k == m.readLE (b + n) k)) := by
  rw [Bool.eq_iff_iff]; simp [Tactic.readLE_add_eq_iff]

/-- 16 bytes compare equal iff both words do (reads in the order the loads give them). -/
theorem beq16 (m : Memory) (a b : Nat) :
    (m.readLE a 16 == m.readLE b 16) = (m.readLE b 8 == m.readLE a 8 && m.readLE (b + 8) 8 == m.readLE (a + 8) 8) := by
  rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, readLE_16_eq_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩

theorem ofNat_add16 (x : Nat) : BitVec.ofNat 64 x + 16#64 = BitVec.ofNat 64 (x + 16) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem and15 (R : Nat) (hR : R < 2 ^ 64) : BitVec.ofNat 64 R &&& 15#64 = BitVec.ofNat 64 (R % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hR, show (15 % 2 ^ 64 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

set_option maxHeartbeats 8000000 in
theorem loop16 (j : Nat) : ∀ (S : State) (x y R : Nat), 1 ≤ j → R < 2 ^ 64 →
    S.pc = BitVec.ofNat 64 (Extracted.entry + 0x78) →
    S.regs 0 = BitVec.ofNat 64 x → S.regs 1 = BitVec.ofNat 64 y →
    S.regs 2 = BitVec.ofNat 64 R → S.regs 6 = BitVec.ofNat 64 (x + 16 * j) →
    x + 16 * j + R % 16 ≤ 2 ^ 48 → y + 16 * j + R % 16 ≤ 2 ^ 48 →
    S.mem.accessible x (16 * j + R % 16) false = true →
    S.mem.accessible y (16 * j + R % 16) false = true →
    (S.regs 30).toNat % 4 = 0 → (S.regs 30).toNat < 2 ^ 48 →
    ReachesRet Extracted.program (S.regs 30) S (fun S' => Fin S S'
      (S.mem.readLE x (16 * j + R % 16) == S.mem.readLE y (16 * j + R % 16))) := by
  induction j with
  | zero => intro _ _ _ _ h; omega
  | succ j ih =>
  intro S x y R hj hR hpc h0 h1 h2 h6 hx hy hax hay hl1 hl2
  rw [show 16 * (j + 1) + R % 16 = 16 + (16 * j + R % 16) by omega, beq_add, beq16]
  rw [show 16 * (j + 1) + R % 16 = 16 + (16 * j + R % 16) by omega] at hax hay
  janus_run [xor_eq_zero_iff] until [Extracted.entry + 0x78, Extracted.entry + 0xa0]
  all_goals
    first
    | -- the last chunk, no tail: equal
      (have hj0 : j = 0 := by omega
       subst hj0
       refine ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl, ?_⟩
       simp [setReg])
    | -- a word differs: not equal
      (refine ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl, ?_⟩
       rw [beq_false_of_ne ‹¬ (_ : Nat) = _›]
       simp [setReg])
    | -- the last chunk, then the tail
      (have hj0 : j = 0 := by omega
       subst hj0
       refine rr_mono (tail _ (x + 16) (y + 16) (R % 16) (Nat.mod_lt _ (by decide)) rfl
         (by simp [setReg, ofNat_add16]) (by simp [setReg, ofNat_add16]) (by simp [setReg, and15 R hR])
         (by omega) (by omega)
         (Memory.accessible_mono _ hax (by omega) (by omega))
         (Memory.accessible_mono _ hay (by omega) (by omega))
         (by simpa [setReg] using hl1) (by simpa [setReg] using hl2)) ?_
       intro S' hF
       exact Fin.of hF rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
         (by clear ih hF; simp_all))
    | -- the next chunk
      (refine rr_mono (ih _ (x + 16) (y + 16) R (by omega) hR rfl
         (by simp [setReg, ofNat_add16]) (by simp [setReg, ofNat_add16]) (by simp [setReg, h2])
         (by simp [setReg, h6]; congr 1; omega) (by omega) (by omega)
         (Memory.accessible_mono _ hax (by omega) (by omega))
         (Memory.accessible_mono _ hay (by omega) (by omega))
         (by simpa [setReg] using hl1) (by simpa [setReg] using hl2)) ?_
       intro S' hF
       exact Fin.of hF rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
         (by clear ih hF; simp_all))

theorem and_mask (R k : Nat) (hk : k ≤ 64) (hR : R < 2 ^ 64) :
    R &&& (2 ^ 64 - 2 ^ k) = R >>> k <<< k := by
  have hm : 2 ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases h1 : k ≤ i
  · by_cases h2 : i < 64
    · simp [h1, show i - k < 64 - k by omega]
    · have : R.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hR (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h1, this, show ¬ i - k < 64 - k by omega]
  · simp [h1]

theorem mask_nat (R k : Nat) (hk : k ≤ 64) (hR : R < 2 ^ 64) :
    R &&& (2 ^ 64 - 2 ^ k) = 2 ^ k * (R / 2 ^ k) := by
  rw [and_mask R k hk hR, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm]

theorem mask_bv (R k : Nat) (hk : k ≤ 64) (hR : R < 2 ^ 64) :
    BitVec.ofNat 64 R &&& BitVec.ofNat 64 (2 ^ 64 - 2 ^ k) = BitVec.ofNat 64 (2 ^ k * (R / 2 ^ k)) := by
  have h2k := Nat.two_pow_pos k
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR,
    Nat.mod_eq_of_lt (by omega), mask_nat R k hk hR, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := Nat.mul_div_le R (2 ^ k); omega

theorem ofNat_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp

set_option maxHeartbeats 8000000 in
theorem chunk16 (S : State) (x y R : Nat) (hR : R < 2 ^ 64)
    (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x6c))
    (h0 : S.regs 0 = BitVec.ofNat 64 x) (h1 : S.regs 1 = BitVec.ofNat 64 y)
    (h2 : S.regs 2 = BitVec.ofNat 64 R)
    (hx : x + R ≤ 2 ^ 48) (hy : y + R ≤ 2 ^ 48)
    (hax : S.mem.accessible x R false = true) (hay : S.mem.accessible y R false = true)
    (hl1 : (S.regs 30).toNat % 4 = 0) (hl2 : (S.regs 30).toNat < 2 ^ 48) :
    ReachesRet Extracted.program (S.regs 30) S (fun S' => Fin S S'
      (S.mem.readLE x R == S.mem.readLE y R)) := by
  have hm := mask_nat R 4 (by decide) hR
  have hb := mask_bv R 4 (by decide) hR
  simp only [show 2 ^ 64 - 2 ^ 4 = 18446744073709551600 from rfl, show (2 : Nat) ^ 4 = 16 from rfl] at hm hb
  janus_run [hm] until [Extracted.entry + 0x78, Extracted.entry + 0xa0]
  · -- fewer than 16 bytes: the tail
    have hR16 : R < 16 := by omega
    refine rr_mono (tail _ x y R hR16 rfl (by simp [setReg, h0]) (by simp [setReg, h1])
      (by simp [setReg, h2]) hx hy hax hay (by simpa [setReg] using hl1) (by simpa [setReg] using hl2)) ?_
    intro S' hF
    exact Fin.of hF rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl rfl
  · -- the 16-byte loop, then the tail
    have hj : 1 ≤ R / 16 := by omega
    have hRe : 16 * (R / 16) + R % 16 = R := by omega
    refine rr_mono (loop16 (R / 16) _ x y R hj hR rfl (by simp [setReg, h0]) (by simp [setReg, h1])
      (by simp [setReg, h2]) (by simp [setReg, h0, hb, ofNat_add]) (by omega) (by omega)
      (by rw [hRe]; exact hax) (by rw [hRe]; exact hay)
      (by simpa [setReg] using hl1) (by simpa [setReg] using hl2)) ?_
    intro S' hF
    exact Fin.of hF rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
      (by rw [hRe])

/-- 64 bytes compare equal iff their eight words do, in the form the SIMD loop's two lane
tests give them (the even words, then the odd words). -/
theorem beq64 (m : Memory) (a b : Nat) :
    (m.readLE a 64 == m.readLE b 64) = decide (
      (m.readLE (b + 48) 8 = m.readLE (a + 48) 8 ∧ m.readLE (b + 32) 8 = m.readLE (a + 32) 8 ∧
        m.readLE (b + 16) 8 = m.readLE (a + 16) 8 ∧ m.readLE b 8 = m.readLE a 8) ∧
      (m.readLE (b + 48 + 8) 8 = m.readLE (a + 48 + 8) 8 ∧ m.readLE (b + 32 + 8) 8 = m.readLE (a + 32 + 8) 8 ∧
        m.readLE (b + 16 + 8) 8 = m.readLE (a + 16 + 8) 8 ∧ m.readLE (b + 8) 8 = m.readLE (a + 8) 8)) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, Tactic.readLE_64_eq_iff]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  omega

theorem ofNat_add64 (x : Nat) : BitVec.ofNat 64 x + 64#64 = BitVec.ofNat 64 (x + 64) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem and63 (R : Nat) (hR : R < 2 ^ 64) : BitVec.ofNat 64 R &&& 63#64 = BitVec.ofNat 64 (R % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hR, show (63 % 2 ^ 64 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

set_option maxHeartbeats 8000000 in
theorem loop64 (j : Nat) : ∀ (S : State) (x y R : Nat), 1 ≤ j → R < 2 ^ 64 →
    S.pc = BitVec.ofNat 64 (Extracted.entry + 0x28) →
    S.regs 0 = BitVec.ofNat 64 x → S.regs 1 = BitVec.ofNat 64 y →
    S.regs 2 = BitVec.ofNat 64 R → S.regs 6 = BitVec.ofNat 64 (x + 64 * j) →
    x + 64 * j + R % 64 ≤ 2 ^ 48 → y + 64 * j + R % 64 ≤ 2 ^ 48 →
    S.mem.accessible x (64 * j + R % 64) false = true →
    S.mem.accessible y (64 * j + R % 64) false = true →
    (S.regs 30).toNat % 4 = 0 → (S.regs 30).toNat < 2 ^ 48 →
    ReachesRet Extracted.program (S.regs 30) S (fun S' => Fin S S'
      (S.mem.readLE x (64 * j + R % 64) == S.mem.readLE y (64 * j + R % 64))) := by
  induction j with
  | zero => intro _ _ _ _ h; omega
  | succ j ih =>
  intro S x y R hj hR hpc h0 h1 h2 h6 hx hy hax hay hl1 hl2
  rw [show 64 * (j + 1) + R % 64 = 64 + (64 * j + R % 64) by omega, beq_add, beq64]
  rw [show 64 * (j + 1) + R % 64 = 64 + (64 * j + R % 64) by omega] at hax hay
  janus_run until [Extracted.entry + 0x28, Extracted.entry + 0x6c]
  all_goals
    first
    | -- the last chunk, nothing left: equal
      (have hj0 : j = 0 := by omega
       subst hj0
       refine ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl, ?_⟩
       try rw [decide_eq_true ⟨‹_›, ‹_›⟩]
       simp [setReg, ‹R % 64 = 0›])
    | -- a word differs: not equal
      (refine ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl, ?_⟩
       clear ih
       simp_all [setReg])
    | -- the last chunk, then the rest (`chunk16`)
      (have hj0 : j = 0 := by omega
       subst hj0
       refine rr_mono (chunk16 _ (x + 64) (y + 64) (R % 64) (by omega) rfl
         (by simp [setReg, ofNat_add64]) (by simp [setReg, ofNat_add64]) (by simp [setReg, and63 R hR])
         (by omega) (by omega)
         (Memory.accessible_mono _ hax (by omega) (by omega))
         (Memory.accessible_mono _ hay (by omega) (by omega))
         (by simpa [setReg] using hl1) (by simpa [setReg] using hl2)) ?_
       intro S' hF
       exact Fin.of hF rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
         (by (try rw [decide_eq_true ⟨‹_›, ‹_›⟩]); simp))
    | -- the next chunk
      (refine rr_mono (ih _ (x + 64) (y + 64) R (by omega) hR rfl
         (by simp [setReg, ofNat_add64]) (by simp [setReg, ofNat_add64]) (by simp [setReg, h2])
         (by simp [setReg, h6]; congr 1; omega) (by omega) (by omega)
         (Memory.accessible_mono _ hax (by omega) (by omega))
         (Memory.accessible_mono _ hay (by omega) (by omega))
         (by simpa [setReg] using hl1) (by simpa [setReg] using hl2)) ?_
       intro S' hF
       exact Fin.of hF rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
         (by (try rw [decide_eq_true ⟨‹_›, ‹_›⟩]); simp))

theorem rr_mono' {p : Program} {ret : W64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', s'.pc = ret → Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', h1, h2, h3⟩ := h; exact ⟨k, s', h1, h2, hQ _ h2 h3⟩

theorem eqRet_of_fin {d : Nat} {s s' : State} {b : Bool} (h : Fin s s' b) (hpc : s'.pc = s.regs 30) :
    EqRet d 0 s s' fun r => BoolRes r b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  exact EqRet.intro a1 hpc a3 a4 a5 a6 a7 a8 (by rw [a2]; exact MemFrame.refl _ _) a9

theorem regs_ofNat (s : State) (i : Nat) : s.regs i = BitVec.ofNat 64 (s.regs i).toNat := by simp

set_option maxHeartbeats 8000000 in
theorem correctness (d : Nat) : Memequal Extracted.program Extracted.entry d := by
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, hgo⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  have hn64 := (s.regs 2).isLt
  have hm4 := mask_nat (s.regs 2).toNat 4 (by decide) hn64
  have hm6 := mask_nat (s.regs 2).toNat 6 (by decide) hn64
  simp only [show 2 ^ 64 - 2 ^ 4 = 18446744073709551600 from rfl, show (2 : Nat) ^ 4 = 16 from rfl,
    show 2 ^ 64 - 2 ^ 6 = 18446744073709551552 from rfl, show (2 : Nat) ^ 6 = 64 from rfl] at hm4 hm6
  janus_run [hm6] until [Extracted.entry + 0x28, Extracted.entry + 0x6c, Extracted.entry + 0xa0]
  all_goals
    have h0 := regs_ofNat s 0
    have h1 := regs_ofNat s 1
    have h2 := regs_ofNat s 2
    first
    | -- `n = 0`, `a = b`, and `n = 1` with equal bytes: `true`
      (refine EqRet.intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
        (MemFrame.refl _ _) ?_
       simp only [BoolRes, setReg_apply, Nat.reduceEqDiff, reduceIte, rd_mod1] at *
       clear h0 h1 h2
       simp_all
       done)
    | -- `n = 1`, the bytes differ: `false`
      (refine EqRet.intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
        (MemFrame.refl _ _) ?_
       simp only [BoolRes, setReg_apply, Nat.reduceEqDiff, reduceIte]
       rw [beq_false_of_ne (fun h => (by assumption : ¬ s.mem.readLE _ 1 % 18446744073709551616 =
         s.mem.readLE _ 1 % 18446744073709551616) (by rw [h]))]
       simp)
    | -- fewer than 16 bytes: the tail
      (refine rr_mono' (tail _ (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat ‹_› rfl h0 h1 h2
         ha1 hb1 ha2 hb2 hl1 hl2) ?_
       intro S' hpc' hF
       exact eqRet_of_fin (Fin.of hF rfl rfl rfl rfl rfl rfl rfl rfl rfl) hpc')
    | -- 16 to 63 bytes: `chunk16`
      (refine rr_mono' (chunk16 _ (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat hn64 rfl
         (by simpa [setReg] using h0) (by simpa [setReg] using h1) (by simpa [setReg] using h2)
         ha1 hb1 ha2 hb2 (by simpa [setReg] using hl1) (by simpa [setReg] using hl2)) ?_
       intro S' hpc' hF
       exact eqRet_of_fin (Fin.of hF rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
         rfl rfl rfl rfl) (by simpa [setReg] using hpc'))
    | -- 64 bytes or more: the SIMD loop
      (have hj : 1 ≤ (s.regs 2).toNat / 64 := by omega
       have hRe : 64 * ((s.regs 2).toNat / 64) + (s.regs 2).toNat % 64 = (s.regs 2).toNat := by omega
       refine rr_mono' (loop64 ((s.regs 2).toNat / 64) _ (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat
         hj hn64 rfl (by simpa [setReg] using h0) (by simpa [setReg] using h1) (by simpa [setReg] using h2)
         ?_ (by omega) (by omega) (by rw [hRe]; exact ha2) (by rw [hRe]; exact hb2)
         (by simpa [setReg] using hl1) (by simpa [setReg] using hl2)) ?_
       · simp only [setReg_apply, Nat.reduceEqDiff, reduceIte]
         apply BitVec.eq_of_toNat_eq
         simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, hm6]
         try omega
       intro S' hpc' hF
       exact eqRet_of_fin (Fin.of hF rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
         rfl rfl rfl (by rw [hRe])) (by simpa [setReg] using hpc'))

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness call state: `memequal(VAL, DST, 8)` on `EqHashModel.wmem` (`VAL` holds 42, `DST`
zeros), goroutine `wg`, stack pointer `wsp`, return address `wret`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 VAL else if i = 1 then BitVec.ofNat 64 DST
      else if i = 2 then 8 else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 wret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := EqHashModel.wmem }

/-- The precondition holds at `s0` (stack bound 64). -/
theorem pre : EqPre 64 0 s0 ∧ Input s0 64 0 (s0.regs 0).toNat (s0.regs 2).toNat ∧
    Input s0 64 0 (s0.regs 1).toNat (s0.regs 2).toNat := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [CallOK, Input, calleeStack, outside_cons, outside_nil] <;> decide

theorem nonvacuous : ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧
    (EqPre 64 0 s ∧ Input s 64 0 (s.regs 0).toNat (s.regs 2).toNat ∧
      Input s 64 0 (s.regs 1).toNat (s.regs 2).toNat) :=
  ⟨s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns whether the 8 bytes at `VAL` and `DST` agree. -/
theorem returns : ReachesRet Extracted.program (s0.regs 30) s0
    (fun s' => EqRet 64 0 s0 s' fun r => BoolRes r
      (s0.mem.readLE (s0.regs 0).toNat 8 == s0.mem.readLE (s0.regs 1).toNat 8)) :=
  correctness 64 s0 rfl pre

end Witness

end Proof
