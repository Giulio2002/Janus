import Janus.Amd64.ExecCrypto
import Janus.Tactic.Vector

/-!
# AES (FIPS-197): a reference specification

The Advanced Encryption Standard as FIPS-197 (2001, updated 2023) defines it, written from the
standard and not from either ISA model:

* **GF(2^8)** (§4): `xtime` (multiplication by `x`, §4.2.1), `gmul` the product of two bytes by
  shift-and-add over the bits of the second (§4.2), `ginv` the multiplicative inverse as `b^254`
  (`0 ↦ 0`);
* **`SubBytes`** (§5.1.1): the S-box `sbox b = affine(ginv b)` with the affine map
  `b'_i = b_i ⊕ b_{i+4} ⊕ b_{i+5} ⊕ b_{i+6} ⊕ b_{i+7} ⊕ c_i`, `c = 63H`, and its inverse
  (§5.3.2) `invSbox b = ginv(invAffine b)`;
* **the state** (§3.4) is 16 bytes `s[r,c] = in[r + 4c]`, held as a 128-bit natural whose byte
  `i` is `in[i]` (`elem x 8 i`), which is how both architectures' 128-bit loads see the bytes in
  memory; **`ShiftRows`** `s'[r,c] = s[r, (c + r) mod 4]` (§5.1.2), **`MixColumns`**
  `s'[r,c] = 02•s[r,c] ⊕ 03•s[r+1,c] ⊕ s[r+2,c] ⊕ s[r+3,c]` (§5.1.3) and their inverses (§5.3);
* **`KeyExpansion`** (§5.2) with `RotWord`, `SubWord` and `Rcon[i] = x^(i-1)`, a word being 4
  bytes held little-endian (`w[i]` byte `k` is `elem w 8 k`), round key `r` the words
  `w[4r .. 4r+3]` (`roundKey`);
* **`Cipher`** (§5.1): `AddRoundKey` with round key 0, `nr - 1` full rounds, a final round
  without `MixColumns`. `aes128 key block` is AES-128.

`fips197_C1`, `fips197_C3` check the appendix C.1/C.3 vectors (and `fips197_A1` the expanded key
of appendix A.1) in the kernel; `sbox_table` / `invSbox_table` check the S-boxes against the
tables of FIPS-197 figures 7 and 14 as transcribed in `Janus.Arm64.aesSbox` / `aesInvSbox`.

**The instructions.** `aesenc_eq`, `aesenclast_eq`, `aesdec_eq`, `aesdeclast_eq`, `aesimc_eq`
prove that the x86 instructions of `Janus.Amd64.ExecCrypto` are the FIPS-197 round (and inverse
round) transformations on every state and round key: `AESENC` is one `Cipher` round,
`AESENCLAST` the last round, `AESDEC`/`AESDECLAST` the rounds of the Equivalent Inverse Cipher
(§5.3.5) and `AESIMC` is `InvMixColumns`. `keygenAssist_eq` relates `AESKEYGENASSIST` to
`SubWord`/`RotWord`.
-/

namespace Janus.Spec.AES

-- the byte-wise proofs below use one simp set for all sixteen bytes; some lemmas are needed
-- for some bytes only
set_option linter.unusedSimpArgs false

open Janus.Arm64 (elem ofElems)
open Janus.Tactic (elem_lt ofElems_lt elem_ofElems)

/-! ## GF(2^8) -/

/-- Multiplication by `x` (`{02}`) modulo `m(x) = x^8 + x^4 + x^3 + x + 1` (§4.2.1). -/
def xtime (b : Nat) : Nat := if b < 128 then 2 * b else 2 * b - 256 ^^^ 0x1B

/-- `a • b` for bytes: `Σ b_i · (x^i • a)` over the bits of `b` (§4.2), `n` bits. -/
def gmulN : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, a, b => (if b % 2 = 1 then a else 0) ^^^ gmulN n (xtime a) (b / 2)

/-- The product of two bytes in GF(2^8). -/
def gmul (a b : Nat) : Nat := gmulN 8 a b

/-- `b^e` by square-and-multiply over the `n` low bits of `e`. -/
def gpowN : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | n + 1, b, e => gmul (if e % 2 = 1 then b else 1) (gpowN n (gmul b b) (e / 2))

/-- `b^e` for `e < 256`. -/
def gpow (b e : Nat) : Nat := gpowN 8 b e

/-- The multiplicative inverse (`b^254`; `0` for `0`, §5.1.1). -/
def ginv (b : Nat) : Nat := gpow b 254

/-- Bit `i` of a byte, indices mod 8. -/
@[reducible] def bit (b i : Nat) : Nat := b / 2 ^ (i % 8) % 2

/-- The affine map of the S-box: `b'_i = b_i ⊕ b_{i+4} ⊕ b_{i+5} ⊕ b_{i+6} ⊕ b_{i+7} ⊕ c_i`. -/
def affine (b : Nat) : Nat :=
  ofElems 1 8 fun i => bit b i ^^^ bit b (i + 4) ^^^ bit b (i + 5) ^^^ bit b (i + 6) ^^^
    bit b (i + 7) ^^^ bit 0x63 i

/-- The inverse affine map: `b'_i = b_{i+2} ⊕ b_{i+5} ⊕ b_{i+7} ⊕ d_i`, `d = 05H` (§5.3.2). -/
def invAffine (b : Nat) : Nat :=
  ofElems 1 8 fun i => bit b (i + 2) ^^^ bit b (i + 5) ^^^ bit b (i + 7) ^^^ bit 0x05 i

/-- The S-box (§5.1.1). -/
def sbox (b : Nat) : Nat := affine (ginv b)

/-- The inverse S-box (§5.3.2). -/
def invSbox (b : Nat) : Nat := ginv (invAffine b)

/-! ## The state transformations -/

/-- `s[r, c]`: byte `r + 4c` of the state. -/
@[reducible] def s (x r c : Nat) : Nat := elem x 8 (r + 4 * c)

/-- The state whose `s[r, c]` is `f r c`. -/
@[reducible] def state (f : Nat → Nat → Nat) : Nat := ofElems 8 16 fun i => f (i % 4) (i / 4)

def subBytes (x : Nat) : Nat := state fun r c => sbox (s x r c)
def invSubBytes (x : Nat) : Nat := state fun r c => invSbox (s x r c)

/-- `s'[r, c] = s[r, (c + r) mod 4]`. -/
def shiftRows (x : Nat) : Nat := state fun r c => s x r ((c + r) % 4)

/-- `s'[r, (c + r) mod 4] = s[r, c]`, i.e. `s'[r, c] = s[r, (c + 4 - r) mod 4]`. -/
def invShiftRows (x : Nat) : Nat := state fun r c => s x r ((c + 4 - r) % 4)

/-- (5.6): `s'[r,c] = 02•s[r,c] ⊕ 03•s[r+1,c] ⊕ s[r+2,c] ⊕ s[r+3,c]` (rows mod 4). -/
def mixColumns (x : Nat) : Nat :=
  state fun r c => gmul 2 (s x r c) ^^^ gmul 3 (s x ((r + 1) % 4) c) ^^^ s x ((r + 2) % 4) c ^^^
    s x ((r + 3) % 4) c

/-- (5.10): `s'[r,c] = 0e•s[r,c] ⊕ 0b•s[r+1,c] ⊕ 0d•s[r+2,c] ⊕ 09•s[r+3,c]`. -/
def invMixColumns (x : Nat) : Nat :=
  state fun r c => gmul 0x0e (s x r c) ^^^ gmul 0x0b (s x ((r + 1) % 4) c) ^^^
    gmul 0x0d (s x ((r + 2) % 4) c) ^^^ gmul 0x09 (s x ((r + 3) % 4) c)

/-- `AddRoundKey`: the bitwise XOR of the state and the round key (§5.1.4). -/
def addRoundKey (x k : Nat) : Nat := x ^^^ k

/-! ## Key expansion and the cipher -/

/-- `SubWord`. -/
def subWord (w : Nat) : Nat := ofElems 8 4 fun k => sbox (elem w 8 k)

/-- `RotWord([a0, a1, a2, a3]) = [a1, a2, a3, a0]`. -/
def rotWord (w : Nat) : Nat := ofElems 8 4 fun k => elem w 8 ((k + 1) % 4)

/-- `Rcon[i] = [x^(i-1), 00, 00, 00]` (`i ≥ 1`). -/
def rcon (i : Nat) : Nat := gpow 2 (i - 1)

/-- `KeyExpansion` (§5.2) of an `nk`-word key `key` (a natural whose byte `4i + k` is byte `k`
of word `i`), `k` more words: the list `w[0 .. nk + k - 1]`. -/
def expandN (nk key : Nat) : Nat → List Nat
  | 0 => (List.range nk).map fun i => elem key 32 i
  | k + 1 =>
    let ws := expandN nk key k
    let i := nk + k
    let temp := ws.getD (i - 1) 0
    let temp := if i % nk = 0 then subWord (rotWord temp) ^^^ rcon (i / nk)
      else if nk > 6 ∧ i % nk = 4 then subWord temp else temp
    ws ++ [ws.getD (i - nk) 0 ^^^ temp]

/-- The `4 (nr + 1)` words of the key schedule. -/
def keyExpansion (nk nr key : Nat) : List Nat := expandN nk key (4 * (nr + 1) - nk)

/-- Round key `r`: the words `w[4r .. 4r+3]`, word `4r + c` in column `c`. -/
def roundKey (w : List Nat) (r : Nat) : Nat := ofElems 32 4 fun c => w.getD (4 * r + c) 0

/-- One full round `r`: `SubBytes`, `ShiftRows`, `MixColumns`, `AddRoundKey`. -/
def round (w : List Nat) (r x : Nat) : Nat :=
  addRoundKey (mixColumns (shiftRows (subBytes x))) (roundKey w r)

/-- Rounds `1 .. k`. -/
def rounds (w : List Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => round w (k + 1) (rounds w k x)

/-- `Cipher(in, Nr, w)` (§5.1). -/
def cipher (nr : Nat) (w : List Nat) (input : Nat) : Nat :=
  let st := addRoundKey input (roundKey w 0)
  let st := rounds w (nr - 1) st
  addRoundKey (shiftRows (subBytes st)) (roundKey w nr)

/-- AES-128, AES-192, AES-256 encryption of a block under a key (both as naturals whose byte `i`
is byte `i` of the string). -/
def aes128 (key input : Nat) : Nat := cipher 10 (keyExpansion 4 10 key) input
def aes192 (key input : Nat) : Nat := cipher 12 (keyExpansion 6 12 key) input
def aes256 (key input : Nat) : Nat := cipher 14 (keyExpansion 8 14 key) input

/-! ## Known answers (FIPS-197 appendices A.1, C.1, C.2, C.3) -/

/-- The bytes `b0 b1 ...` of a string, as a natural (`b0` lowest). -/
def ofBytes : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * ofBytes bs

/-- `00112233445566778899aabbccddeeff`. -/
def plainC : Nat := ofBytes [0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa,
  0xbb, 0xcc, 0xdd, 0xee, 0xff]

/-- The key `00 01 02 ...` of `n` bytes. -/
def countKey (n : Nat) : Nat := ofBytes (List.range n)

theorem fips197_A1 :
    roundKey (keyExpansion 4 10 (ofBytes [0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab,
      0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c])) 10 =
    ofBytes [0xd0, 0x14, 0xf9, 0xa8, 0xc9, 0xee, 0x25, 0x89, 0xe1, 0x3f, 0x0c, 0xc8, 0xb6, 0x63,
      0x0c, 0xa6] := by decide +kernel

theorem fips197_C1 : aes128 (countKey 16) plainC =
    ofBytes [0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4,
      0xc5, 0x5a] := by decide +kernel

theorem fips197_C2 : aes192 (countKey 24) plainC =
    ofBytes [0xdd, 0xa9, 0x7c, 0xa4, 0x86, 0x4c, 0xdf, 0xe0, 0x6e, 0xaf, 0x70, 0xa0, 0xec, 0x0d,
      0x71, 0x91] := by decide +kernel

theorem fips197_C3 : aes256 (countKey 32) plainC =
    ofBytes [0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49,
      0x60, 0x89] := by decide +kernel

/-! ## The S-boxes and the multiplications against the tables of the ISA models -/

theorem sbox_table : ∀ b, b < 256 → sbox b = Janus.Arm64.aesSbox.getD b 0 := by decide +kernel
theorem invSbox_table : ∀ b, b < 256 → invSbox b = Janus.Arm64.aesInvSbox.getD b 0 := by
  decide +kernel

theorem gmul_2 : ∀ b, b < 256 → gmul 2 b = Janus.Arm64.gfMul 2 b := by decide +kernel
theorem gmul_3 : ∀ b, b < 256 → gmul 3 b = Janus.Arm64.gfMul 3 b := by decide +kernel
theorem gmul_9 : ∀ b, b < 256 → gmul 9 b = Janus.Arm64.gfMul 9 b := by decide +kernel
theorem gmul_11 : ∀ b, b < 256 → gmul 11 b = Janus.Arm64.gfMul 11 b := by decide +kernel
theorem gmul_13 : ∀ b, b < 256 → gmul 13 b = Janus.Arm64.gfMul 13 b := by decide +kernel
theorem gmul_14 : ∀ b, b < 256 → gmul 14 b = Janus.Arm64.gfMul 14 b := by decide +kernel

set_option maxRecDepth 8000 in
theorem aesSbox_lt : ∀ b, Janus.Arm64.aesSbox.getD b 0 < 256 := by
  intro b
  by_cases h : b < 256
  · revert b; decide +kernel
  · have hl : Janus.Arm64.aesSbox.length = 256 := rfl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    decide

set_option maxRecDepth 8000 in
theorem aesInvSbox_lt : ∀ b, Janus.Arm64.aesInvSbox.getD b 0 < 256 := by
  intro b
  by_cases h : b < 256
  · revert b; decide +kernel
  · have hl : Janus.Arm64.aesInvSbox.length = 256 := rfl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    decide

theorem gfMul_lt (k : Nat) {b : Nat} (hb : b < 256) : Janus.Arm64.gfMul k b < 256 := by
  have hx : ∀ y, y < 256 → Janus.Arm64.xtime y < 256 := by decide +kernel
  have h2 := hx _ hb
  have h4 := hx _ h2
  have h8 := hx _ h4
  simp only [Janus.Arm64.gfMul]
  generalize Janus.Arm64.xtime b = b2 at h2 h4 h8 ⊢
  generalize Janus.Arm64.xtime b2 = b4 at h4 h8 ⊢
  generalize Janus.Arm64.xtime b4 = b8 at h8 ⊢
  have hx8 : ∀ x y : Nat, x < 256 → y < 256 → x ^^^ y < 256 := fun x y hx hy =>
    Nat.xor_lt_two_pow (n := 8) hx hy
  apply hx8 _ _ _ (by split <;> omega)
  apply hx8 _ _ _ (by split <;> omega)
  apply hx8 _ _ (by split <;> omega) (by split <;> omega)

/-! ## Element lemmas -/

theorem elem_xor (x y e i : Nat) : elem (x ^^^ y) e i = elem x e i ^^^ elem y e i := by
  unfold elem; apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  cases decide (j < e) <;> simp

theorem elem_8_lt (x i : Nat) : elem x 8 i < 256 := elem_lt x 8 i

/-- Two vectors of `n` elements are equal if their elements are. -/
theorem ofElems_congr (e : Nat) {f g : Nat → Nat} : ∀ n, (∀ i, i < n → f i % 2 ^ e = g i % 2 ^ e) →
    ofElems e n f = ofElems e n g
  | 0, _ => rfl
  | n + 1, h => by
    simp only [ofElems]
    rw [ofElems_congr e n (fun i hi => h i (by omega)), h n (by omega)]

/-- A value below `2^(e·n)` is the vector of its `n` elements of `e` bits. -/
theorem ofElems_elem_gen (e n x : Nat) (hx : x < 2 ^ (e * n)) : ofElems e n (fun i => elem x e i) = x := by
  have key : ∀ k, ofElems e k (fun i => elem x e i) = x % 2 ^ (e * k) := by
    intro k
    induction k with
    | zero => simp [ofElems, Nat.mod_one]
    | succ k ih =>
      rw [ofElems, ih, Nat.mul_succ, Nat.pow_add, Nat.mod_mul, elem,
        Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos e)), Nat.add_comm]
  rw [key n, Nat.mod_eq_of_lt hx]

/-- A 128-bit value is the vector of its bytes. -/
theorem ofElems_elem (x : Nat) (hx : x < 2 ^ 128) : ofElems 8 16 (fun i => elem x 8 i) = x :=
  ofElems_elem_gen 8 16 x hx

/-- Equality of 128-bit values byte by byte. -/
theorem eq_of_bytes {x y : Nat} (hx : x < 2 ^ 128) (hy : y < 2 ^ 128)
    (h : ∀ i, i < 16 → elem x 8 i = elem y 8 i) : x = y := by
  rw [← ofElems_elem x hx, ← ofElems_elem y hy]
  exact ofElems_congr 8 16 fun i hi => by rw [h i hi]

/-- A property of the sixteen byte indices. -/
theorem forall_lt_16 {P : Nat → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12)
    (h13 : P 13) (h14 : P 14) (h15 : P 15) : ∀ i, i < 16 → P i := by
  intro i hi
  match i, hi with
  | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2 | 3, _ => exact h3
  | 4, _ => exact h4 | 5, _ => exact h5 | 6, _ => exact h6 | 7, _ => exact h7
  | 8, _ => exact h8 | 9, _ => exact h9 | 10, _ => exact h10 | 11, _ => exact h11
  | 12, _ => exact h12 | 13, _ => exact h13 | 14, _ => exact h14 | 15, _ => exact h15
  | _ + 16, h => exact absurd h (by omega)

theorem gfMul_1 (b : Nat) : Janus.Arm64.gfMul 1 b = b := by simp [Janus.Arm64.gfMul]

theorem lt_128_of_ofElems (f : Nat → Nat) : ofElems 8 16 f < 2 ^ 128 := ofElems_lt 8 16 f

/-! ## The x86 instructions are the FIPS-197 transformations -/

open Janus.Arm64 (aesShiftRows aesSubBytes aesMixColumns aesSbox aesInvSbox gfMul)

attribute [local simp] elem_ofElems elem_8_lt aesSbox_lt aesInvSbox_lt Nat.mod_eq_of_lt gfMul_1

theorem shiftRows_eq (x : Nat) : aesShiftRows false x = shiftRows x := by
  apply eq_of_bytes (ofElems_lt 8 16 _) (ofElems_lt 8 16 _)
  refine forall_lt_16 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [aesShiftRows, shiftRows, Janus.Arm64.aesShiftRowsPerm]

theorem invShiftRows_eq (x : Nat) : aesShiftRows true x = invShiftRows x := by
  apply eq_of_bytes (ofElems_lt 8 16 _) (ofElems_lt 8 16 _)
  refine forall_lt_16 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [aesShiftRows, invShiftRows, Janus.Arm64.aesInvShiftRowsPerm]

theorem subBytes_eq (x : Nat) : aesSubBytes false x = subBytes x := by
  apply eq_of_bytes (ofElems_lt 8 16 _) (ofElems_lt 8 16 _)
  refine forall_lt_16 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [aesSubBytes, subBytes, sbox_table _ (elem_8_lt _ _)]

theorem invSubBytes_eq (x : Nat) : aesSubBytes true x = invSubBytes x := by
  apply eq_of_bytes (ofElems_lt 8 16 _) (ofElems_lt 8 16 _)
  refine forall_lt_16 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [aesSubBytes, invSubBytes, invSbox_table _ (elem_8_lt _ _)]

theorem mixColumns_eq (x : Nat) : aesMixColumns false x = mixColumns x := by
  apply eq_of_bytes (ofElems_lt 8 16 _) (ofElems_lt 8 16 _)
  have hl : ∀ a b c d : Nat, a < 256 → b < 256 → c < 256 → d < 256 → a ^^^ b ^^^ c ^^^ d < 256 :=
    fun a b c d ha hb hc hd => Nat.xor_lt_two_pow (n := 8) (Nat.xor_lt_two_pow (n := 8)
      (Nat.xor_lt_two_pow (n := 8) ha hb) hc) hd
  refine forall_lt_16 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [aesMixColumns, mixColumns, gmul_2 _ (elem_8_lt _ _), gmul_3 _ (elem_8_lt _ _),
      hl _ _ _ _ (gfMul_lt 2 (elem_8_lt _ _)) (gfMul_lt 3 (elem_8_lt _ _)) (elem_8_lt _ _) (elem_8_lt _ _)]

theorem invMixColumns_eq (x : Nat) : aesMixColumns true x = invMixColumns x := by
  apply eq_of_bytes (ofElems_lt 8 16 _) (ofElems_lt 8 16 _)
  have hl : ∀ a b c d : Nat, a < 256 → b < 256 → c < 256 → d < 256 → a ^^^ b ^^^ c ^^^ d < 256 :=
    fun a b c d ha hb hc hd => Nat.xor_lt_two_pow (n := 8) (Nat.xor_lt_two_pow (n := 8)
      (Nat.xor_lt_two_pow (n := 8) ha hb) hc) hd
  refine forall_lt_16 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [aesMixColumns, invMixColumns, gmul_9 _ (elem_8_lt _ _), gmul_11 _ (elem_8_lt _ _),
      gmul_13 _ (elem_8_lt _ _), gmul_14 _ (elem_8_lt _ _),
      hl _ _ _ _ (gfMul_lt 14 (elem_8_lt _ _)) (gfMul_lt 11 (elem_8_lt _ _))
        (gfMul_lt 13 (elem_8_lt _ _)) (gfMul_lt 9 (elem_8_lt _ _))]

/-- `SubBytes` and `ShiftRows` commute (the S-box acts on each byte, `ShiftRows` permutes them). -/
theorem shiftRows_subBytes (x : Nat) : shiftRows (subBytes x) = subBytes (shiftRows x) := by
  apply eq_of_bytes (ofElems_lt 8 16 _) (ofElems_lt 8 16 _)
  refine forall_lt_16 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [shiftRows, subBytes]

theorem invShiftRows_invSubBytes (x : Nat) :
    invShiftRows (invSubBytes x) = invSubBytes (invShiftRows x) := by
  apply eq_of_bytes (ofElems_lt 8 16 _) (ofElems_lt 8 16 _)
  refine forall_lt_16 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [invShiftRows, invSubBytes]

open Janus.Amd64 Janus.Amd64.ExecCrypto in
/-- **`AESENC` is a `Cipher` round**: `MixColumns(ShiftRows(SubBytes(state)))` XOR the key. -/
theorem aesenc_eq (x k : Nat) :
    aesRound .enc x k = addRoundKey (mixColumns (shiftRows (subBytes x))) k := by
  simp only [aesRound, addRoundKey, shiftRows_eq, subBytes_eq, mixColumns_eq, shiftRows_subBytes]

open Janus.Amd64 Janus.Amd64.ExecCrypto in
/-- **`AESENCLAST` is the last `Cipher` round** (no `MixColumns`). -/
theorem aesenclast_eq (x k : Nat) :
    aesRound .encLast x k = addRoundKey (shiftRows (subBytes x)) k := by
  simp only [aesRound, addRoundKey, shiftRows_eq, subBytes_eq, shiftRows_subBytes]

open Janus.Amd64 Janus.Amd64.ExecCrypto in
/-- **`AESDEC` is an Equivalent Inverse Cipher round** (§5.3.5: `InvSubBytes`,
`InvShiftRows`, `InvMixColumns`, `AddRoundKey` with the transformed key). -/
theorem aesdec_eq (x k : Nat) :
    aesRound .dec x k = addRoundKey (invMixColumns (invShiftRows (invSubBytes x))) k := by
  simp only [aesRound, addRoundKey, invShiftRows_eq, invSubBytes_eq, invMixColumns_eq,
    invShiftRows_invSubBytes]

open Janus.Amd64 Janus.Amd64.ExecCrypto in
/-- **`AESDECLAST`** is the last Inverse Cipher round. -/
theorem aesdeclast_eq (x k : Nat) :
    aesRound .decLast x k = addRoundKey (invShiftRows (invSubBytes x)) k := by
  simp only [aesRound, addRoundKey, invShiftRows_eq, invSubBytes_eq, invShiftRows_invSubBytes]

/-- **`AESIMC` is `InvMixColumns`.** -/
theorem aesimc_eq (x : Nat) : aesMixColumns true x = invMixColumns x := invMixColumns_eq x

theorem subWord_eq (w : Nat) : Janus.Amd64.ExecCrypto.subWord w = subWord w := by
  simp only [Janus.Amd64.ExecCrypto.subWord, subWord]
  exact ofElems_congr 8 4 fun i _ => by rw [sbox_table _ (elem_8_lt _ _)]

/-- `RotWord` on a word (`< 2^32`) is the rotation of `AESKEYGENASSIST`. -/
theorem rotWord_eq (w : Nat) (hw : w < 2 ^ 32) : Janus.Amd64.ExecCrypto.rotWord w = rotWord w := by
  simp only [Janus.Amd64.ExecCrypto.rotWord, rotWord, ofElems, elem]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.reduceAdd, Nat.mul_zero, Nat.pow_zero,
    Nat.div_one] at hw ⊢
  omega

theorem subWord_lt (w : Nat) : subWord w < 2 ^ 32 := ofElems_lt 8 4 _

open Janus.Amd64.ExecCrypto in
/-- **`AESKEYGENASSIST`**: with `X1`/`X3` dwords 1 and 3 of the source, dword 0 of the result is
`SubWord(X1)`, dword 1 `RotWord(SubWord(X1)) XOR RCON`, dword 2 `SubWord(X3)`, dword 3
`RotWord(SubWord(X3)) XOR RCON`. -/
theorem keygenAssist_eq (b imm : Nat) :
    keygenAssist b imm = ofElems 32 4 fun i =>
      if i = 0 then subWord (elem b 32 1) else if i = 1 then rotWord (subWord (elem b 32 1)) ^^^ imm
      else if i = 2 then subWord (elem b 32 3) else rotWord (subWord (elem b 32 3)) ^^^ imm := by
  simp only [keygenAssist, subWord_eq, rotWord_eq, subWord_lt]

/-! ## A key schedule in memory -/

/-- The `n` words of a key schedule stored at `xk`: word `i` is the 4 bytes at `xk + 4i` (byte
`k` of the word at `xk + 4i + k`, FIPS-197's `w[i]` as Go's `expandKeyAsm` stores it). -/
def schedule (m : Janus.Arm64.Memory) (xk n : Nat) : List Nat :=
  (List.range n).map fun i => m.readLE (xk + 4 * i) 4

/-- Round key `r` of a stored schedule is the 16 bytes at `xk + 16r`. -/
theorem roundKey_schedule (m : Janus.Arm64.Memory) (xk n r : Nat) (h : 4 * r + 4 ≤ n) :
    roundKey (schedule m xk n) r = m.readLE (xk + 16 * r) 16 := by
  have hl : m.readLE (xk + 16 * r) 16 < 2 ^ (32 * 4) := Janus.Arm64.Memory.readLE_lt m _ 16
  rw [← ofElems_elem_gen 32 4 _ hl, roundKey]
  apply ofElems_congr 32 4
  intro c hc
  have he := Janus.Tactic.elem_readLE m (a := xk + 16 * r) (n := 16) (k := 4) (i := c) (by omega)
  simp only [Nat.reduceMul] at he
  rw [he, schedule, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  rw [show xk + 4 * (4 * r + c) = xk + 16 * r + 4 * c by omega]

theorem length_schedule (m : Janus.Arm64.Memory) (xk n : Nat) : (schedule m xk n).length = n := by
  simp [schedule]

theorem length_expandN (nk key : Nat) : ∀ k, (expandN nk key k).length = nk + k
  | 0 => by simp [expandN]
  | k + 1 => by simp only [expandN, List.length_append, length_expandN nk key k, List.length_singleton]; omega

theorem length_keyExpansion (nk nr key : Nat) (h : nk ≤ 4 * (nr + 1)) :
    (keyExpansion nk nr key).length = 4 * (nr + 1) := by
  rw [keyExpansion, length_expandN]; omega

/-- A stored schedule whose words are those of `l` is `l`. -/
theorem schedule_eq (m : Janus.Arm64.Memory) (xk n : Nat) (l : List Nat) (hl : l.length = n)
    (h : ∀ i, i < n → m.readLE (xk + 4 * i) 4 = l.getD i 0) : schedule m xk n = l := by
  apply List.ext_getElem (by rw [length_schedule, hl])
  intro i h1 h2
  rw [length_schedule] at h1
  simp only [schedule, List.getElem_map, List.getElem_range]
  rw [h i h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

end Janus.Spec.AES
