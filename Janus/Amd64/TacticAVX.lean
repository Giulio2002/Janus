import Janus.Amd64.TacticExt

/-!
# Proof support for the vector instructions (SSE packed integers, AVX/AVX2)

Extends the `janus64_exec` / `janus64_post` simp sets of `Janus.Amd64.Tactic` so that the
executor can step the VEX moves and compares of `runtime.memmove` and `internal/bytealg`, and
adds the lemmas the proofs about them need. Everything is proved from the model.

* Vector operands (`readV`, `writeV`, `State.getV`, `State.setV`) are unfolded; the upper YMM
  lanes get the same `setXmmF` normal form as the lower ones (`State.setYmmHi_eq`).
* A 256-bit value written by `setV` and read back by `getV` is re-assembled by `ymmJoin_ofNat`
  (`ymmJoin (v / 2^128) v = v mod 2^256`); the `_mod` lemmas then drop the `mod` for the
  values the code produces (32-byte reads, `PCMPEQB` masks).
* `msbBytes_cmpeq_land`: the `PMOVMSKB` of the `PAND` of two `PCMPEQB` masks is all ones iff
  both pairs of operands are equal. This is the step from `memeqbody`'s mask test to byte
  equality, at 16 lanes (SSE) and 32 lanes (AVX2).
* `copied_writes`: like `zeroed_writes` for copies. A chain of chunk stores, each storing the
  bytes of a fixed source memory `M` at the matching offset (`writeLE (d + o) k (M.readLE
  (s + o) k)`), in any order and overlapping, leaves `d + i` holding `M`'s byte `s + i` for every
  `i` the chunks cover. It proves that byte by byte, with `omega`.
-/

namespace Janus.Amd64.Tactic

open Janus.Amd64

/-! ## Simp set: vector operands and the upper YMM lanes -/

attribute [janus64_exec] readV writeV State.getV State.setV State.ymm

@[janus64_exec] theorem State.setYmmHi_eq (s : State) (r : Nat) (v : W128) :
    s.setYmmHi r v = { s with ymmHi := setXmmF s.ymmHi r v } := rfl

/-- `2^128` and `2^256` as the literals `simp` produces. -/
private theorem p128 : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by decide
private theorem p256 :
    (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by decide

/-- Re-assembling a 256-bit value that `State.setV` split into two lanes. -/
@[janus64_exec, janus64_post] theorem ymmJoin_ofNat (v : Nat) :
    ymmJoin (BitVec.ofNat 128 (v / 340282366920938463463374607431768211456)) (BitVec.ofNat 128 v) =
      v % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  unfold ymmJoin
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, p128,
    show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) =
      340282366920938463463374607431768211456 * 340282366920938463463374607431768211456 by decide,
    Nat.mod_mul]
  omega

@[janus64_exec, janus64_post] theorem readLE_mod_32 (m : Memory) (a : Nat) :
    m.readLE a 32 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      m.readLE a 32 :=
  Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt m a 32; rw [← p256]; simpa using this)

/-! ## Byte lanes -/

theorem cmpeqBytes_lt (k a b : Nat) : cmpeqBytes k a b < 256 ^ k := by
  induction k generalizing a b with
  | zero => simp [cmpeqBytes]
  | succ k ih =>
    have := ih (a / 256) (b / 256)
    simp only [cmpeqBytes, Nat.pow_succ]
    split <;> omega

theorem msbBytes_lt (k a : Nat) : msbBytes k a < 2 ^ k := by
  induction k generalizing a with
  | zero => simp [msbBytes]
  | succ k ih =>
    have := ih (a / 256)
    have : a % 256 / 128 < 2 := by omega
    simp only [msbBytes, Nat.pow_succ]
    omega

/-- `msbBytes k` only looks at the low `k` bytes. -/
theorem msbBytes_mod (k a : Nat) : msbBytes k (a % 256 ^ k) = msbBytes k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [msbBytes]
    rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul]
    have h1 : (a % 256 + 256 * (a / 256 % 256 ^ k)) % 256 = a % 256 := by omega
    have h2 : (a % 256 + 256 * (a / 256 % 256 ^ k)) / 256 = a / 256 % 256 ^ k := by omega
    rw [h1, h2, ih]

@[janus64_exec, janus64_post] theorem cmpeqBytes_mod_32 (a b : Nat) :
    cmpeqBytes 32 a b %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      cmpeqBytes 32 a b :=
  Nat.mod_eq_of_lt (by have := cmpeqBytes_lt 32 a b; rw [← p256]; simpa using this)

@[janus64_exec, janus64_post] theorem cmpeqBytes_mod_16 (a b : Nat) :
    cmpeqBytes 16 a b % 340282366920938463463374607431768211456 = cmpeqBytes 16 a b :=
  Nat.mod_eq_of_lt (by have := cmpeqBytes_lt 16 a b; rw [← p128]; simpa using this)

@[janus64_exec, janus64_post] theorem msbBytes_mod_32 (a : Nat) :
    msbBytes 32
        (a % 115792089237316195423570985008687907853269984665640564039457584007913129639936) =
      msbBytes 32 a := by
  have := msbBytes_mod 32 a; rw [show (256 : Nat) ^ 32 = 2 ^ 256 by decide, p256] at this
  exact this

@[janus64_exec, janus64_post] theorem msbBytes_mod_16 (a : Nat) :
    msbBytes 16 (a % 340282366920938463463374607431768211456) = msbBytes 16 a := by
  have := msbBytes_mod 16 a; rw [show (256 : Nat) ^ 16 = 2 ^ 128 by decide, p128] at this
  exact this

/-- `AND` of two values given byte by byte (`x, u < 256`). -/
theorem land_byte_split (x y u v : Nat) (hx : x < 256) (hu : u < 256) :
    (x + 256 * y) &&& (u + 256 * v) = (x &&& u) + 256 * (y &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hxu : x &&& u < 2 ^ 8 := Nat.and_lt_two_pow x (by simpa using hu)
  rw [show (256 : Nat) = 2 ^ 8 by rfl, Nat.add_comm x, Nat.add_comm u, Nat.add_comm (x &&& u),
    Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (by simpa using hx),
    Nat.testBit_two_pow_mul_add _ (by simpa using hu), Nat.testBit_two_pow_mul_add _ hxu]
  split <;> simp [Nat.testBit_and]

/-- Both pairs equal, byte by byte. -/
def cmpeq2Bytes : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | k + 1, a, b, c, d =>
    (if a % 256 = b % 256 ∧ c % 256 = d % 256 then 255 else 0) +
      256 * cmpeq2Bytes k (a / 256) (b / 256) (c / 256) (d / 256)

theorem cmpeqBytes_land (k a b c d : Nat) :
    cmpeqBytes k a b &&& cmpeqBytes k c d = cmpeq2Bytes k a b c d := by
  induction k generalizing a b c d with
  | zero => simp [cmpeqBytes, cmpeq2Bytes]
  | succ k ih =>
    simp only [cmpeqBytes, cmpeq2Bytes]
    rw [land_byte_split _ _ _ _ (by split <;> omega) (by split <;> omega), ih]
    congr 1
    by_cases h1 : a % 256 = b % 256 <;> by_cases h2 : c % 256 = d % 256 <;> simp [h1, h2]

private theorem mod_succ_iff (a b k : Nat) :
    a % 256 ^ (k + 1) = b % 256 ^ (k + 1) ↔
      a % 256 = b % 256 ∧ a / 256 % 256 ^ k = b / 256 % 256 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul, Nat.mod_mul]
  omega

/-- The `PMOVMSKB` of the `PAND` of two `PCMPEQB` masks over `k` bytes is all ones iff the
low `k` bytes of `a` and `b` agree and those of `c` and `d` agree. -/
theorem msbBytes_cmpeq_land (k a b c d : Nat) :
    msbBytes k (cmpeqBytes k a b &&& cmpeqBytes k c d) = 2 ^ k - 1 ↔
      a % 256 ^ k = b % 256 ^ k ∧ c % 256 ^ k = d % 256 ^ k := by
  rw [cmpeqBytes_land]
  induction k generalizing a b c d with
  | zero => simp [msbBytes, Nat.mod_one]
  | succ k ih =>
    rw [mod_succ_iff, mod_succ_iff]
    have hlt := msbBytes_lt k (cmpeq2Bytes k (a / 256) (b / 256) (c / 256) (d / 256))
    have ihk := ih (a / 256) (b / 256) (c / 256) (d / 256)
    simp only [msbBytes, cmpeq2Bytes]
    by_cases h : a % 256 = b % 256 ∧ c % 256 = d % 256
    · rw [if_pos h]
      have e1 : (255 + 256 * cmpeq2Bytes k (a / 256) (b / 256) (c / 256) (d / 256)) % 256 = 255 := by
        omega
      have e2 : (255 + 256 * cmpeq2Bytes k (a / 256) (b / 256) (c / 256) (d / 256)) / 256 =
          cmpeq2Bytes k (a / 256) (b / 256) (c / 256) (d / 256) := by omega
      rw [e1, e2, Nat.pow_succ]
      constructor
      · intro hm; have := ihk.1 (by omega); exact ⟨⟨h.1, this.1⟩, h.2, this.2⟩
      · intro hm; have := ihk.2 ⟨hm.1.2, hm.2.2⟩; omega
    · rw [if_neg h]
      have e1 : (0 + 256 * cmpeq2Bytes k (a / 256) (b / 256) (c / 256) (d / 256)) % 256 = 0 := by
        omega
      rw [e1, Nat.pow_succ]
      constructor
      · intro hm; have := Nat.two_pow_pos k; omega
      · intro hm; exact absurd ⟨hm.1.1, hm.2.1⟩ h

/-- `PMOVMSKB` of an `AND` is all ones iff it is for both operands. -/
theorem msbBytes_land (k x y : Nat) :
    msbBytes k (x &&& y) = 2 ^ k - 1 ↔ msbBytes k x = 2 ^ k - 1 ∧ msbBytes k y = 2 ^ k - 1 := by
  induction k generalizing x y with
  | zero => simp [msbBytes]
  | succ k ih =>
    simp only [msbBytes]
    have m1 : (x &&& y) % 256 = x % 256 &&& y % 256 := Nat.and_mod_two_pow (n := 8)
    have d1 : (x &&& y) / 256 = x / 256 &&& y / 256 := Nat.and_div_two_pow (n := 8)
    have d2 : (x % 256 &&& y % 256) / 128 = x % 256 / 128 &&& y % 256 / 128 :=
      Nat.and_div_two_pow (n := 7)
    rw [m1, d1, d2]
    have hx := msbBytes_lt k (x / 256)
    have hy := msbBytes_lt k (y / 256)
    have hxy := msbBytes_lt k (x / 256 &&& y / 256)
    have ihk := ih (x / 256) (y / 256)
    have hp : x % 256 / 128 = 0 ∨ x % 256 / 128 = 1 := by omega
    have hq : y % 256 / 128 = 0 ∨ y % 256 / 128 = 1 := by omega
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have := Nat.two_pow_pos k
    rw [hpow]
    rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq] <;>
      simp only [show (0 : Nat) &&& 0 = 0 by decide, show (0 : Nat) &&& 1 = 0 by decide,
        show (1 : Nat) &&& 0 = 0 by decide, show (1 : Nat) &&& 1 = 1 by decide] <;>
      omega

/-- `PMOVMSKB` of a `PCMPEQB` mask is all ones iff the low `k` bytes are equal. -/
theorem msbBytes_cmpeq (k a b : Nat) :
    msbBytes k (cmpeqBytes k a b) = 2 ^ k - 1 ↔ a % 256 ^ k = b % 256 ^ k := by
  induction k generalizing a b with
  | zero => simp [msbBytes, Nat.mod_one]
  | succ k ih =>
    rw [mod_succ_iff]
    simp only [msbBytes, cmpeqBytes]
    have hr := cmpeqBytes_lt k (a / 256) (b / 256)
    have hlt := msbBytes_lt k (cmpeqBytes k (a / 256) (b / 256))
    have ihk := ih (a / 256) (b / 256)
    rw [Nat.pow_succ]
    by_cases h : a % 256 = b % 256
    · rw [if_pos h]
      have e1 : (255 + 256 * cmpeqBytes k (a / 256) (b / 256)) % 256 / 128 = 1 := by omega
      have e2 : (255 + 256 * cmpeqBytes k (a / 256) (b / 256)) / 256 = cmpeqBytes k (a / 256) (b / 256) := by
        omega
      rw [e1, e2]
      have := Nat.two_pow_pos k
      constructor
      · intro hm; exact ⟨h, ihk.1 (by omega)⟩
      · intro hm; have := ihk.2 hm.2; omega
    · rw [if_neg h]
      have e1 : (0 + 256 * cmpeqBytes k (a / 256) (b / 256)) % 256 / 128 = 0 := by omega
      rw [e1]
      have := Nat.two_pow_pos k
      constructor
      · intro hm; omega
      · intro hm; exact absurd hm.1 h

/-- The 32-bit mask test `CMPL DX, $0xffff; JEQ` on a 16-lane `PMOVMSKB` result. -/
theorem mask16_test (m : Nat) :
    BitVec.setWidth 32 (BitVec.ofNat 64 (msbBytes 16 m)) - 65535#32 = 0#32 ↔
      msbBytes 16 m = 2 ^ 16 - 1 := by
  have := msbBytes_lt 16 m
  rw [show (2 : Nat) ^ 16 = 65536 by decide] at this ⊢
  rw [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `memeqbody`'s AVX2 test `VPAND (VPCMPEQB a b) (VPCMPEQB c d); VPMOVMSKB; CMPL $-1; JEQ` as
the executor leaves it: the mask is all ones iff both 32-byte pairs are equal. -/
theorem avx2_mask_eq (a b c d : Nat) :
    BitVec.setWidth 32 (BitVec.ofNat 64 (msbBytes 32 (cmpeqBytes 32 c d &&& cmpeqBytes 32 a b))) -
        4294967295#32 = 0#32 ↔ a % 256 ^ 32 = b % 256 ^ 32 ∧ c % 256 ^ 32 = d % 256 ^ 32 := by
  have hlt := msbBytes_lt 32 (cmpeqBytes 32 c d &&& cmpeqBytes 32 a b)
  have key := msbBytes_cmpeq_land 32 c d a b
  rw [show (2 : Nat) ^ 32 = 4294967296 by decide] at hlt key
  rw [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  constructor
  · intro h; have := key.1 (by omega); exact ⟨this.2, this.1⟩
  · intro h; have := key.2 ⟨h.2, h.1⟩; omega

/-- `memeqbody`'s SSE test (`PCMPEQB`, `PAND` of the four 16-byte results, `PMOVMSKB`,
`CMPL $0xffff`) in the same form, 16 lanes. -/
theorem sse_mask_eq (a b c d : Nat) :
    BitVec.setWidth 32 (BitVec.ofNat 64 (msbBytes 16 (cmpeqBytes 16 c d &&& cmpeqBytes 16 a b))) -
        65535#32 = 0#32 ↔ a % 256 ^ 16 = b % 256 ^ 16 ∧ c % 256 ^ 16 = d % 256 ^ 16 := by
  have hlt := msbBytes_lt 16 (cmpeqBytes 16 c d &&& cmpeqBytes 16 a b)
  have key := msbBytes_cmpeq_land 16 c d a b
  rw [show (2 : Nat) ^ 16 = 65536 by decide] at hlt key
  rw [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  constructor
  · intro h; have := key.1 (by omega); exact ⟨this.2, this.1⟩
  · intro h; have := key.2 ⟨h.2, h.1⟩; omega

/-- Two `2n`-byte reads are equal iff both halves are. -/
theorem readLE_eq_halves (m : Memory) (a b n : Nat) :
    m.readLE a (n + n) = m.readLE b (n + n) ↔
      m.readLE a n = m.readLE b n ∧ m.readLE (a + n) n = m.readLE (b + n) n := by
  have la := Janus.Arm64.Memory.readLE_lt m a n
  have lb := Janus.Arm64.Memory.readLE_lt m b n
  rw [Janus.Arm64.Memory.readLE_add, Janus.Arm64.Memory.readLE_add]
  constructor
  · intro h
    have h1 := congrArg (· % 256 ^ n) h
    have h2 := congrArg (· / 256 ^ n) h
    have hp : 0 < 256 ^ n := Nat.pow_pos (by decide)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt la, Nat.mod_eq_of_lt lb,
      Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt la, Nat.div_eq_of_lt lb, Nat.zero_add] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]

/-- A `SETcc` byte written into `AL` (`putReg 8`), read back at 8 bits. -/
@[janus64_post] theorem setWidth8_merge_ite (x : BitVec 64) (p : Prop) [Decidable p] :
    BitVec.setWidth 8 (x &&& 18446744073709551360#64 ||| BitVec.setWidth 64 (if p then 1#8 else 0#8)) =
      if p then 1#8 else 0#8 := by
  split
  · exact setWidth8_merge x 1 (by decide)
  · exact setWidth8_merge x 0 (by decide)

/-- `ANDQ $-32, r` on an address (`memmove`'s 32-byte destination alignment) as `Nat`
arithmetic for `omega`. -/
@[janus64_exec, janus64_post] theorem land_align32 (x : Nat) (h : x < 18446744073709551616) :
    x &&& 18446744073709551584 = x - x % 32 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e1 : (18446744073709551584 : Nat) = 2 ^ 64 - (31 + 1) := by decide
  have e2 : x - x % 32 = 2 ^ 5 * (x / 2 ^ 5) := by omega
  rw [Nat.testBit_and, e1, Nat.testBit_two_pow_sub_succ (by decide), e2, Nat.testBit_two_pow_mul,
    show (31 : Nat) = 2 ^ 5 - 1 by decide, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases hi : i < 64
  · by_cases h5 : i < 5
    · simp [hi, h5]; intro; omega
    · simp [hi, h5, show i - 5 + 5 = i by omega]; omega
  · have hx : x.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (show 18446744073709551616 ≤ 2 ^ i from
        (show (18446744073709551616 : Nat) = 2 ^ 64 by decide) ▸
          Nat.pow_le_pow_right (show 2 > 0 by decide) (by omega)))
    simp [hi, show i - 5 + 5 = i by omega, hx]

/-- A byte loaded into `AL` (`MOVB m8, AL`: `putReg 8`) read back at 8 bits. -/
@[janus64_exec, janus64_post] theorem setWidth8_merge_bv (x : BitVec 64) (y : BitVec 8) :
    BitVec.setWidth 8 (x &&& 18446744073709551360#64 ||| BitVec.setWidth 64 y) = y := by
  have := setWidth8_merge x y.toNat y.isLt
  rw [BitVec.ofNat_toNat] at this
  simpa using this

/-- `TESTB $1, AL; JNE` on a feature byte (`memmove`'s `TESTB $avxSupported, AX`) as a `Nat`
equation. -/
@[janus64_exec, janus64_post] theorem bv8_and_one_eq_zero (v : Nat) :
    (BitVec.ofNat 8 v &&& 1#8 = 0#8) = (v % 2 = 0) := by
  apply propext
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have := Nat.and_two_pow_sub_one_eq_mod (v % 2 ^ 8) 1
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.zero_mod] at this ⊢
  rw [this]
  omega

/-- The 32-byte alignment of `(x & -32) + c`. -/
@[janus64_exec, janus64_post] theorem align32_add_mod (x c : Nat) :
    (x - x % 32 + c) % 32 = c % 32 := by omega

@[janus64_exec, janus64_post] theorem align32_add_add_mod (x c e : Nat) :
    (x - x % 32 + c + e) % 32 = (c + e) % 32 := by omega

@[janus64_exec, janus64_post] theorem align32_add_add_add_mod (x c e f : Nat) :
    (x - x % 32 + c + e + f) % 32 = (c + e + f) % 32 := by omega

/-! ## Block copies from overlapping chunk stores -/

theorem byte_of_readLE (M : Memory) (c k i : Nat) (h : i < k) :
    BitVec.ofNat 8 (M.readLE c k / 256 ^ i) = M.bytes (c + i) := by
  rw [Janus.Arm64.Memory.readLE_div _ _ _ _ (by omega)]
  obtain ⟨j, hj⟩ : ∃ j, k - i = j + 1 := ⟨k - i - 1, by omega⟩
  rw [hj, Janus.Arm64.Memory.readLE_succ]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have := (M.bytes (c + i)).isLt
  omega

/-- One store of a chunk of `M` (`k` bytes from `c`) at `a`, seen from byte `x`. -/
theorem cb_step {W M : Memory} {a k c x : Nat} {r : Byte}
    (h1 : a ≤ x ∧ x < a + k → M.bytes (c + (x - a)) = r)
    (h2 : ¬(a ≤ x ∧ x < a + k) → W.bytes x = r) : (W.writeLE a k (M.readLE c k)).bytes x = r := by
  rw [Janus.Arm64.Memory.bytes_writeLE]
  by_cases h : a ≤ x ∧ x < a + k
  · rw [if_pos h, byte_of_readLE _ _ _ _ (by omega)]; exact h1 h
  · rw [if_neg h]; exact h2 h

/-- A store that does not touch byte `x`. -/
theorem cb_skip {W : Memory} {a k v x : Nat} {r : Byte} (h1 : x < a ∨ a + k ≤ x)
    (h2 : W.bytes x = r) : (W.writeLE a k v).bytes x = r := by
  rw [Janus.Arm64.Memory.bytes_writeLE, if_neg (by omega)]; exact h2

/-- A read of `n` bytes at `d` equals `M`'s `n` bytes at `s` when every byte does. -/
theorem readLE_of_bytes {M' M : Memory} {d s n : Nat}
    (h : ∀ i, i < n → M'.bytes (d + i) = M.bytes (s + i)) : M'.readLE d n = M.readLE s n := by
  induction n generalizing d s with
  | zero => rfl
  | succ n ih =>
    rw [Janus.Arm64.Memory.readLE_succ, Janus.Arm64.Memory.readLE_succ,
      ih (d := d + 1) (s := s + 1) (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show d + (i + 1) = d + 1 + i by omega, show s + (i + 1) = s + 1 + i by omega] at this)]
    have := h 0 (by omega); simp at this; rw [this]

/-- Prove `W.bytes x = M.bytes y` when `W` is a chain of stores ending in memory where `x` is
not covered: chunk stores of `M` (`cb_step`, with the offset arithmetic by `omega`) and other
stores that miss `x` (`cb_skip`); a byte no chunk covers is a contradiction (`omega`). -/
macro "copied_writes" : tactic => `(tactic| (
  repeat (first
    | refine cb_step (fun h => congrArg _ (by omega)) (fun h => ?_)
    | refine cb_skip (by omega) ?_)
  exfalso; omega))

end Janus.Amd64.Tactic
