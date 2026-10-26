import Janus.Spec.AES

/-!
# Go's fixed-size memory hashes on amd64: `memhash32`, `memhash64`

`runtime.memhash64(p, h)` hashes the 8 bytes at `p` with the seed `h`
(`runtime/asm_amd64.s`, `runtime/hash64.go`, Go 1.26). It is the hash of every map whose key is
8 bytes of plain memory (`map[uint64]V`, `map[int64]V`, pointers, ...; `memhash32` for 4-byte
keys). Which algorithm runs is decided once at startup (`runtime.useAeshash`, set when the CPU has
AES-NI, SSE3 and SSE4.1):

* **AES** (`aesHash64`): the seed in the low quadword of `X0` and the data in the high quadword
  (`MOVQ BX, X0; PINSRQ $1, (AX), X0`), three `AESENC` rounds keyed by the process's random
  `runtime.aeskeysched` (three 16-byte round keys `k0 k1 k2`), the low quadword returned. With
  `Janus.Spec.AES.aesenc_eq` an `AESENC` is one FIPS-197 cipher round, so the hash is stated with
  `Janus.Spec.AES.round'` (`SubBytes`, `ShiftRows`, `MixColumns`, `AddRoundKey`). `memhash32`
  inserts the 4 data bytes at dword 2 (`PINSRD $2`) instead (`aesHash32`).
* **fallback** (`fallbackHash64`), `memhash64Fallback`: `mix(m5 ^ 8, mix(a ^ hashkey[1],
  a ^ seed ^ hashkey[0]))` with `mix(a, b) = hi ^ lo` of the 128-bit product, keyed by the random
  `runtime.hashkey`.

In terms of `Janus.Contracts.Hash.HashModel` (agent/eqhash), the AES path is the model whose
`mem64 h v = aesHash64 k0 k1 k2 h v` for the process's key schedule.
-/

namespace Janus.Spec.MemHash

open Janus.Spec.AES

/-- One AES cipher round with round key `k` (FIPS-197 §5.1): what `AESENC` computes. -/
def round' (x k : Nat) : Nat := addRoundKey (mixColumns (shiftRows (subBytes x))) k

/-- The AES `memhash64` of the 8-byte value `v` with seed `h` under the round keys `k0 k1 k2`. -/
def aesHash64 (k0 k1 k2 h v : Nat) : Nat :=
  round' (round' (round' (h % 2 ^ 64 + 2 ^ 64 * (v % 2 ^ 64)) k0) k1) k2 % 2 ^ 64

/-- The AES `memhash32` of the 4-byte value `v`: the data in dword 2. -/
def aesHash32 (k0 k1 k2 h v : Nat) : Nat :=
  round' (round' (round' (h % 2 ^ 64 + 2 ^ 64 * (v % 2 ^ 32)) k0) k1) k2 % 2 ^ 64

/-- `mix(a, b)`: the XOR of the halves of the 128-bit product. -/
def mix (a b : Nat) : Nat := (a * b / 2 ^ 64) ^^^ (a * b % 2 ^ 64)

/-- `m5`. -/
def m5 : Nat := 0x1d8e4e27c47d124f

/-- `memhash64Fallback(p, seed)` with `hashkey[0] = hk0`, `hashkey[1] = hk1`. -/
def fallbackHash64 (hk0 hk1 h v : Nat) : Nat := mix (m5 ^^^ 8) (mix (v ^^^ hk1) (v ^^^ h ^^^ hk0))

/-- `memhash32Fallback(p, seed)`: as `fallbackHash64` with the 4-byte value and `m5 ^ 4`. -/
def fallbackHash32 (hk0 hk1 h v : Nat) : Nat := mix (m5 ^^^ 4) (mix (v ^^^ hk1) (v ^^^ h ^^^ hk0))

end Janus.Spec.MemHash

/-! ## Lemmas for the machine-code proofs -/

namespace Janus.Spec.MemHash

theorem mix_comm (a b : Nat) : mix a b = mix b a := by simp only [mix, Nat.mul_comm a b]

theorem mix_lt (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : mix a b < 2 ^ 64 := by
  have h1 : a * b / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    exact Nat.mul_lt_mul_of_lt_of_lt ha hb
  exact Nat.xor_lt_two_pow h1 (Nat.mod_lt _ (Nat.two_pow_pos _))

theorem ofNat_xor (n a b : Nat) : BitVec.ofNat n (a ^^^ b) = BitVec.ofNat n a ^^^ BitVec.ofNat n b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_xor]
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  cases decide (j < n) <;> simp

/-- The `MULQ`; `XORQ DX, AX` of `mix`. -/
theorem mix_bv (a b : Nat) :
    BitVec.ofNat 64 (a * b) ^^^ BitVec.ofNat 64 (a * b / 18446744073709551616) = BitVec.ofNat 64 (mix a b) := by
  rw [mix, ofNat_xor, BitVec.xor_comm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.mod_mod]

/-- `fallbackHash64` with its operands in the order the code multiplies them. -/
theorem fallbackHash64_eq (hk0 hk1 h v : Nat) :
    fallbackHash64 hk0 hk1 h v = mix 2129725606500045383 (mix (v ^^^ h ^^^ hk0) (hk1 ^^^ v)) := by
  rw [fallbackHash64, mix_comm (v ^^^ hk1), Nat.xor_comm v hk1]; rfl

/-- `fallbackHash32` likewise. -/
theorem fallbackHash32_eq (hk0 hk1 h v : Nat) :
    fallbackHash32 hk0 hk1 h v = mix 2129725606500045387 (mix (v ^^^ h ^^^ hk0) (hk1 ^^^ v)) := by
  rw [fallbackHash32, mix_comm (v ^^^ hk1), Nat.xor_comm v hk1]; rfl

theorem readLE_lt64 (m : Janus.Arm64.Memory) (a n : Nat) (hn : n ≤ 8) : m.readLE a n < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Janus.Arm64.Memory.readLE_lt m a n)
    (by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega))

theorem readLE_mod64 (m : Janus.Arm64.Memory) (a n : Nat) (hn : n ≤ 8) : m.readLE a n % 2 ^ 64 = m.readLE a n :=
  Nat.mod_eq_of_lt (readLE_lt64 m a n hn)

theorem readLE8_mod (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 8 % 2 ^ 64 = m.readLE a 8 :=
  Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt m a 8)

theorem readLE4_mod (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 4 % 2 ^ 32 = m.readLE a 4 :=
  Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt m a 4)

/-- `MOVQ BX, X0; PINSRQ $1, v, X0`: the seed in the low quadword, the data in the high one. -/
theorem pinsrq_hi (h v : Nat) :
    (Janus.Amd64.ExecSSE.lanes 64 fun i => if i = 1 then v else Janus.Arm64.elem (h % 340282366920938463463374607431768211456) 64 i) %
      340282366920938463463374607431768211456 = h % 2 ^ 64 + 2 ^ 64 * (v % 2 ^ 64) := by
  simp only [Janus.Amd64.ExecSSE.lanes, Janus.Arm64.ofElems, Janus.Arm64.elem]
  simp only [Nat.reducePow, Nat.pow_zero, Nat.div_one, Nat.mul_zero, Nat.zero_add, Nat.mul_one,
    show ¬ (0 = 1) from by decide, ↓reduceIte]
  omega

/-- `MOVQ BX, X0; PINSRD $2, v, X0`: the data in dword 2. -/
theorem pinsrd_2 (h v : Nat) (hh : h < 2 ^ 64) :
    (Janus.Amd64.ExecSSE.lanes 32 fun i => if i = 2 then v else Janus.Arm64.elem (h % 340282366920938463463374607431768211456) 32 i) %
      340282366920938463463374607431768211456 = h % 2 ^ 64 + 2 ^ 64 * (v % 2 ^ 32) := by
  simp only [Janus.Amd64.ExecSSE.lanes, Janus.Arm64.ofElems, Janus.Arm64.elem]
  simp only [Nat.reducePow, Nat.pow_zero, Nat.div_one, Nat.mul_zero,
    Nat.zero_add, Nat.mul_one, show ¬ (0 = 2) from by decide, show ¬ (1 = 2) from by decide,
    show ¬ (3 = 2) from by decide, ↓reduceIte] at hh ⊢
  omega

/-- `pinsrq_hi` with the lane count evaluated (`ExecSSE.lanes 64 = ofElems 64 2`), the form the
proof automation leaves since the integration of WP-E with WP-F/WP-G (a `Nat` division simproc
in the stepping simp set evaluates `128 / 64`). -/
theorem pinsrq_hi' (h v : Nat) :
    (Janus.Arm64.ofElems 64 2 fun i => if i = 1 then v else Janus.Arm64.elem (h % 340282366920938463463374607431768211456) 64 i) %
      340282366920938463463374607431768211456 = h % 2 ^ 64 + 2 ^ 64 * (v % 2 ^ 64) :=
  pinsrq_hi h v

/-- `pinsrd_2` with the lane count evaluated (`ofElems 32 4`), as `pinsrq_hi'`. -/
theorem pinsrd_2' (h v : Nat) (hh : h < 2 ^ 64) :
    (Janus.Arm64.ofElems 32 4 fun i => if i = 2 then v else Janus.Arm64.elem (h % 340282366920938463463374607431768211456) 32 i) %
      340282366920938463463374607431768211456 = h % 2 ^ 64 + 2 ^ 64 * (v % 2 ^ 32) :=
  pinsrd_2 h v hh

/-- `pinsrq_hi'` without the reduction modulo `2^128` (a lane image is below `2^128`), the form
left once the stepping simp set has dropped it. -/
theorem pinsrq_hi_eq (h v : Nat) :
    (Janus.Arm64.ofElems 64 2 fun i => if i = 1 then v else Janus.Arm64.elem (h % 340282366920938463463374607431768211456) 64 i) =
      h % 2 ^ 64 + 2 ^ 64 * (v % 2 ^ 64) := by
  rw [← pinsrq_hi' h v, Nat.mod_eq_of_lt (Janus.Tactic.ofElems_lt 64 2 _)]

/-- `pinsrd_2'` without the reduction modulo `2^128`, as `pinsrq_hi_eq`. -/
theorem pinsrd_2_eq (h v : Nat) (hh : h < 2 ^ 64) :
    (Janus.Arm64.ofElems 32 4 fun i => if i = 2 then v else Janus.Arm64.elem (h % 340282366920938463463374607431768211456) 32 i) =
      h % 2 ^ 64 + 2 ^ 64 * (v % 2 ^ 32) := by
  rw [← pinsrd_2' h v hh, Nat.mod_eq_of_lt (Janus.Tactic.ofElems_lt 32 4 _)]

/-- `MOVQ X0, AX` of a 128-bit value. -/
theorem setWidth_ofNat_128 (x : Nat) : BitVec.setWidth 64 (BitVec.ofNat 128 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

/-- A byte read as `CMPB` compares it: zero as a `BitVec 8` iff zero. -/
theorem readLE1_eq_zero {m : Janus.Arm64.Memory} {a : Nat}
    (h : BitVec.ofNat 8 (m.readLE a 1) = 0#8) : m.readLE a 1 = 0 := by
  have hl := Janus.Arm64.Memory.readLE_lt m a 1
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
  omega

theorem readLE1_ne_zero {m : Janus.Arm64.Memory} {a : Nat}
    (h : ¬ BitVec.ofNat 8 (m.readLE a 1) = 0#8) : m.readLE a 1 ≠ 0 := by
  intro h0; exact h (by rw [h0])

end Janus.Spec.MemHash
