import Janus.Amd64.ExecSSE
import Janus.Arm64.MemoryLemmas

/-!
# CRC-32C (Castagnoli): a reference specification

The textbook bit-reflected CRC with the Castagnoli polynomial (`1EDC6F41H`, reflected
`82F63B78H`), as RFC 3720 (iSCSI) §B.4 and Go's `hash/crc32` (`crc32.Castagnoli`) define it,
byte by byte:

* `crcShift k c`: `k` steps of the reflected shift register (`c` shifted right, the reflected
  polynomial added when the bit shifted out is set);
* `updByte crc b`: one byte, XORed into the low byte of the register, then 8 steps;
* `update crc bs`: the bytes `bs` in order (the raw register update, without the initial and
  final inversion: what the SSE4.2 `CRC32` instruction and `hash/crc32.castagnoliSSE42` compute);
* `checksum crc bs = ~update (~crc) bs` on 32 bits: `crc32.Update(crc, castagnoliTable, bs)`.
  Its check value is `checksum 0 "123456789" = E3069283H` (`checksum_check`).

`crc32c_eq_update` relates it to the model of the instruction (`Janus.Amd64.ExecSSE.crc32c`,
which feeds the data bit by bit): for an `8k`-bit operand the instruction is `update` over the
operand's `k` bytes, lowest first.
-/

namespace Janus.Spec.CRC32C

/-- One step of the reflected shift register. -/
def crcStep (c : Nat) : Nat := if c % 2 = 1 then (c / 2) ^^^ 0x82F63B78 else c / 2

/-- `k` steps. -/
def crcShift : Nat → Nat → Nat
  | 0, c => c
  | k + 1, c => crcShift k (crcStep c)

/-- One byte. -/
def updByte (crc b : Nat) : Nat := crcShift 8 (crc ^^^ b)

/-- The register `crc` updated with the bytes `bs`. -/
def update (crc : Nat) : List Nat → Nat
  | [] => crc
  | b :: bs => update (updByte crc b) bs

/-- `hash/crc32.Update(crc, MakeTable(Castagnoli), bs)`. -/
def checksum (crc : Nat) (bs : List Nat) : Nat := update (crc ^^^ 0xFFFFFFFF) bs ^^^ 0xFFFFFFFF

/-- The `n` bytes of memory at `a`, in order. -/
def bytesOf (m : Janus.Arm64.Memory) (a : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => m.readLE a 1 :: bytesOf m (a + 1) n

/-- The CRC-32C check value. -/
theorem checksum_check :
    checksum 0 [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0xE3069283 := by
  decide +kernel

theorem update_append (crc : Nat) (xs ys : List Nat) :
    update crc (xs ++ ys) = update (update crc xs) ys := by
  induction xs generalizing crc with
  | nil => rfl
  | cons b bs ih => exact ih _

theorem bytesOf_add (m : Janus.Arm64.Memory) (a : Nat) :
    ∀ n k, bytesOf m a (n + k) = bytesOf m a n ++ bytesOf m (a + n) k
  | 0, k => by simp [bytesOf]
  | n + 1, k => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [bytesOf, List.cons_append, bytesOf_add m (a + 1) n k,
      show a + 1 + n = a + (n + 1) by omega]

/-- `(x XOR y) / 2 = x / 2 XOR y / 2`. -/
theorem xor_div_two (x y : Nat) : (x ^^^ y) / 2 = x / 2 ^^^ y / 2 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_div_two, Nat.testBit_xor]

/-- `(x XOR y) mod 2` is the XOR of the low bits. -/
theorem xor_mod_two (x y : Nat) : (x ^^^ y) % 2 = (x % 2 ^^^ y % 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [show (2 : Nat) = 2 ^ 1 by rfl]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  by_cases hi : i < 1 <;> simp [hi]

/-- The instruction's bit-serial update is the shift register run on `crc XOR data`. -/
theorem crc32c_eq_shift : ∀ n crc d, d < 2 ^ n →
    Janus.Amd64.ExecSSE.crc32c n crc d = crcShift n (crc ^^^ d)
  | 0, crc, d, h => by
    have : d = 0 := by simpa using h
    subst this; simp [Janus.Amd64.ExecSSE.crc32c, crcShift]
  | n + 1, crc, d, h => by
    simp only [Janus.Amd64.ExecSSE.crc32c, crcShift]
    rw [crc32c_eq_shift n _ (d / 2) (by rw [Nat.pow_succ] at h; omega)]
    congr 1
    -- one step: XOR the data bit, shift, then XOR the remaining data
    have hm : (crc ^^^ d % 2) % 2 = (crc ^^^ d) % 2 := by
      rw [xor_mod_two, xor_mod_two, Nat.mod_mod]
    have hq : (crc ^^^ d % 2) / 2 ^^^ d / 2 = (crc ^^^ d) / 2 := by
      rw [xor_div_two, xor_div_two, show d % 2 / 2 = 0 by omega, Nat.xor_zero]
    unfold crcStep
    rw [hm]
    split
    · rw [Nat.xor_assoc, Nat.xor_comm 0x82F63B78 (d / 2), ← Nat.xor_assoc, hq]
    · exact hq

/-- Splitting the data of the bit-serial update. -/
theorem crc32c_add : ∀ n k crc d,
    Janus.Amd64.ExecSSE.crc32c (n + k) crc d =
      Janus.Amd64.ExecSSE.crc32c k (Janus.Amd64.ExecSSE.crc32c n crc (d % 2 ^ n)) (d / 2 ^ n)
  | 0, k, crc, d => by simp [Janus.Amd64.ExecSSE.crc32c]
  | n + 1, k, crc, d => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [Janus.Amd64.ExecSSE.crc32c]
    rw [crc32c_add n k _ (d / 2)]
    have h1 : d % 2 ^ (n + 1) % 2 = d % 2 := by
      rw [Nat.pow_succ', Nat.mod_mul_right_mod]
    have h2 : d % 2 ^ (n + 1) / 2 = d / 2 % 2 ^ n := by
      rw [Nat.pow_succ', Nat.mod_mul_right_div_self]
    have h3 : d / 2 / 2 ^ n = d / 2 ^ (n + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ']
    rw [h1, h2, h3]

/-- The `CRC32` instruction on a `8k`-bit memory operand is `update` over its bytes. -/
theorem crc32c_eq_update (m : Janus.Arm64.Memory) (k : Nat) : ∀ crc a,
    Janus.Amd64.ExecSSE.crc32c (8 * k) crc (m.readLE a k) = update crc (bytesOf m a k) := by
  induction k with
  | zero => intro crc a; rfl
  | succ k ih =>
    intro crc a
    have e := crc32c_add 8 (8 * k) crc (m.readLE a (k + 1))
    have hb : m.readLE a (k + 1) % 2 ^ 8 = m.readLE a 1 := by
      have := Janus.Arm64.Memory.readLE_mod m a (k + 1) 1 (by omega)
      simpa using this
    have hr : m.readLE a (k + 1) / 2 ^ 8 = m.readLE (a + 1) k := by
      have := Janus.Arm64.Memory.readLE_div m a (k + 1) 1 (by omega)
      simpa using this
    have hl : m.readLE a 1 < 2 ^ 8 := by
      have := Janus.Arm64.Memory.readLE_lt m a 1
      simpa using this
    rw [hb, hr, crc32c_eq_shift 8 crc _ hl, ih] at e
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, e]
    rfl

/-- The CRC register stays a 32-bit value. -/
theorem crc32c_lt : ∀ n crc d, crc < 2 ^ 32 → Janus.Amd64.ExecSSE.crc32c n crc d < 2 ^ 32
  | 0, crc, d, h => by simpa [Janus.Amd64.ExecSSE.crc32c] using h
  | n + 1, crc, d, h => by
    simp only [Janus.Amd64.ExecSSE.crc32c]
    apply crc32c_lt
    have hx : crc ^^^ d % 2 < 2 ^ 32 := Nat.xor_lt_two_pow h (by omega)
    split
    · exact Nat.xor_lt_two_pow (by omega) (by decide)
    · omega

/-- `XOR FFFFFFFFH` is the 32-bit complement. -/
theorem xor_ones32 (x : Nat) (h : x < 2 ^ 32) : x ^^^ 4294967295 = 4294967295 - x := by
  have := congrArg BitVec.toNat (BitVec.xor_allOnes (x := BitVec.ofNat 32 x))
  simp [BitVec.toNat_xor, BitVec.toNat_not, Nat.mod_eq_of_lt h] at this
  omega

/-- Two `CRC32Q` over 16 bytes of memory. -/
theorem crc32c_two_qwords (m : Janus.Arm64.Memory) (crc a : Nat) :
    Janus.Amd64.ExecSSE.crc32c 64 (Janus.Amd64.ExecSSE.crc32c 64 crc (m.readLE a 8)) (m.readLE (a + 8) 8) =
      update crc (bytesOf m a 16) := by
  have h := crc32c_eq_update m 8
  simp only [show 8 * 8 = 64 by rfl] at h
  rw [h, h, ← update_append, ← bytesOf_add]

end Janus.Spec.CRC32C
