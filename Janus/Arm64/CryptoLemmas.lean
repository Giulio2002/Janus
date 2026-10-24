import Janus.Arm64.Crypto
import Janus.Arm64.MemoryLemmas

/-!
# CRC32 instructions as the bitwise CRC-32 (proved, not trusted)

`crc32Op` (`Janus.Arm64.Crypto`) transcribes the ASL of CRC32B/H/W/X and CRC32CB/H/W/X:
bit-reversed operands, the polynomial remainder `Poly32Mod2`, and a bit-reversed result. This
file proves that it computes the familiar reflected shift-register CRC (RFC 1952 section 8,
ISO 3309 / ITU-T V.42 for CRC-32, RFC 3720 for CRC-32C), so that a theorem about code using these
instructions can be stated against the textbook definition:

* `CRC.update R m c p n`: the non-inverted CRC register `c` updated with the `n` bytes at `p`,
  one byte at a time (`c := c XOR byte`, then eight times
  `c := if c odd then (c >> 1) XOR R else c >> 1`), with the reflected polynomial `R`
  (`0xEDB88320` for CRC-32, `0x82F63B78` for CRC-32C);
* `crc32Op_eq_update`: `CRC32{B,H,W,X}` (`size = 8 · 2^sz`) of `acc` and the little-endian
  `2^sz`-byte word at `p` is `CRC.update` over those bytes.

The key step (`poly32Mod2_rbit`) is an induction over the bits of the data: one iteration of
`Poly32Mod2` on the bit-reversed register is one shift of the reflected register.
-/

namespace Janus.Arm64

/-! ## Bit lemmas -/

theorem rbitNat_lt_two_pow (n x : Nat) : rbitNat n x < 2 ^ n := by
  induction n generalizing x with
  | zero => simp [rbitNat]
  | succ n ih =>
    simp only [rbitNat, Nat.pow_succ]
    have := ih (x / 2)
    have : x % 2 ≤ 1 := by omega
    have : x % 2 * 2 ^ n ≤ 2 ^ n := by
      have := Nat.mul_le_mul_right (2 ^ n) this; simpa using this
    omega

theorem testBit_rbitNat (n x j : Nat) :
    (rbitNat n x).testBit j = (decide (j < n) && x.testBit (n - 1 - j)) := by
  induction n generalizing x j with
  | zero => simp [rbitNat]
  | succ n ih =>
    simp only [rbitNat]
    rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (rbitNat_lt_two_pow n _)]
    by_cases hj : j < n
    · simp only [hj, ite_true, ih, decide_true, Bool.true_and,
        show j < n + 1 from by omega, Nat.testBit_div_two]
      congr 1; omega
    · simp only [hj, ite_false]
      by_cases hjn : j = n
      · subst hjn; simp [Nat.testBit_zero]
      · have h2 : x % 2 < 2 ^ (j - n) := by
          have := Nat.one_lt_two_pow (n := j - n) (by omega)
          have := Nat.mod_lt x (show 2 > 0 by decide)
          omega
        rw [Nat.testBit_lt_two_pow h2]
        simp; omega

theorem testBit_mod_two (v i : Nat) : (v % 2).testBit i = (decide (i = 0) && v.testBit 0) := by
  have := Nat.testBit_mod_two_pow v 1 i
  rw [show (2 : Nat) ^ 1 = 2 by rfl] at this
  rw [this]
  cases i <;> simp

namespace CRC

/-! ## The bitwise CRC -/

/-- One shift of the reflected CRC register: `if c odd then (c >> 1) XOR R else c >> 1`. -/
def shift1 (R c : Nat) : Nat := if c % 2 = 1 then c / 2 ^^^ R else c / 2

/-- `k` shifts. -/
def shiftN (R : Nat) : Nat → Nat → Nat
  | 0, c => c
  | k + 1, c => shiftN R k (shift1 R c)

/-- One byte: `c := c XOR b`, then eight shifts (RFC 1952, section 8, `update_crc`). -/
def updateByte (R c b : Nat) : Nat := shiftN R 8 (c ^^^ b)

/-- The non-inverted CRC register `c` updated with the `n` bytes at `p`. -/
def update (R : Nat) (m : Memory) (c p : Nat) : Nat → Nat
  | 0 => c
  | n + 1 => update R m (updateByte R c (m.bytes p).toNat) (p + 1) n

/-- The bit-serial form: feed the low `k` bits of `v`, least significant first. -/
def bits (R : Nat) : Nat → Nat → Nat → Nat
  | 0, c, _ => c
  | k + 1, c, v => bits R k (shift1 R (c ^^^ v % 2)) (v / 2)

theorem shift1_lt {R c : Nat} (hR : R < 2 ^ 32) (hc : c < 2 ^ 32) : shift1 R c < 2 ^ 32 := by
  unfold shift1
  have : c / 2 < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hc
  split
  · exact Nat.xor_lt_two_pow this hR
  · exact this

theorem testBit_shift1 (R c i : Nat) :
    (shift1 R c).testBit i = (c.testBit (i + 1) ^^ (c.testBit 0 && R.testBit i)) := by
  unfold shift1
  split <;> rename_i h <;> simp [h, Nat.testBit_xor, Nat.testBit_div_two]

theorem bits_add (R a b c v : Nat) : bits R (a + b) c v = bits R b (bits R a c v) (v / 2 ^ a) := by
  induction a generalizing c v with
  | zero => simp [bits]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, bits, ih, bits, Nat.div_div_eq_div_mul,
      Nat.pow_succ, Nat.mul_comm (2 ^ a) 2]

/-- `bits` only reads the low `k` bits of `v`. -/
theorem bits_mod (R k c v : Nat) : bits R k c (v % 2 ^ k) = bits R k c v := by
  induction k generalizing c v with
  | zero => rfl
  | succ k ih =>
    simp only [bits]
    rw [show v % 2 ^ (k + 1) % 2 = v % 2 by
          rw [Nat.pow_succ, Nat.mod_mul_left_mod],
        show v % 2 ^ (k + 1) / 2 = v / 2 % 2 ^ k by
          rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self], ih]

/-- Feeding one bit, then the rest of `v`, as a register update: the identity behind
`bits_eq_shiftN`. -/
theorem shift1_xor (R c v k : Nat) :
    shift1 R (c ^^^ v % 2) ^^^ v / 2 % 2 ^ k = shift1 R (c ^^^ v % 2 ^ (k + 1)) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor, testBit_shift1, Nat.testBit_mod_two_pow, Nat.testBit_div_two,
    testBit_mod_two]
  simp only [show (i + 1 = 0) = False by simp, show (0 < k + 1) = True by simp,
    show (i + 1 < k + 1) = (i < k) by simp, decide_false, decide_true, Bool.false_and,
    Bool.true_and, Bool.xor_false]
  cases c.testBit (i + 1) <;> cases decide (i < k) <;> cases v.testBit (i + 1) <;>
    cases R.testBit i <;> cases c.testBit 0 <;> cases v.testBit 0 <;> simp

/-- The bit-serial form is the shift register run on `c XOR (v mod 2^k)`. -/
theorem bits_eq_shiftN (R k c v : Nat) : bits R k c v = shiftN R k (c ^^^ v % 2 ^ k) := by
  induction k generalizing c v with
  | zero => simp [bits, shiftN, Nat.mod_one]
  | succ k ih => simp only [bits, shiftN, ih, shift1_xor]

/-- One byte of the bit-serial form is `updateByte`. -/
theorem bits_eight (R c b : Nat) (hb : b < 256) : bits R 8 c b = updateByte R c b := by
  rw [bits_eq_shiftN, Nat.mod_eq_of_lt (by simpa using hb)]; rfl

/-- `update` over `n` bytes is the bit-serial form over their `8n`-bit little-endian value. -/
theorem update_eq_bits (R : Nat) (m : Memory) (c p n : Nat) :
    update R m c p n = bits R (8 * n) c (m.readLE p n) := by
  induction n generalizing c p with
  | zero => show c = c; rfl
  | succ n ih =>
    have hb : (m.bytes p).toNat < 256 := (m.bytes p).isLt
    show update R m (updateByte R c (m.bytes p).toNat) (p + 1) n = _
    rw [ih, show 8 * (n + 1) = 8 + 8 * n by omega, bits_add, ← bits_mod R 8,
      Memory.readLE_succ]
    have e1 : ((m.bytes p).toNat + 256 * m.readLE (p + 1) n) % 2 ^ 8 = (m.bytes p).toNat := by
      rw [show (2 : Nat) ^ 8 = 256 by rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
    have e2 : ((m.bytes p).toNat + 256 * m.readLE (p + 1) n) / 2 ^ 8 = m.readLE (p + 1) n := by
      rw [show (2 : Nat) ^ 8 = 256 by rfl, Nat.add_mul_div_left _ _ (by decide),
        Nat.div_eq_of_lt hb, Nat.zero_add]
    rw [e1, e2, bits_eight R c _ hb]

theorem bits_lt {R : Nat} (hR : R < 2 ^ 32) : ∀ k c v, c < 2 ^ 32 → bits R k c v < 2 ^ 32
  | 0, _, _, hc => hc
  | k + 1, c, v, hc =>
    bits_lt hR k _ _ (shift1_lt hR (Nat.xor_lt_two_pow hc (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))))

end CRC

/-! ## `Poly32Mod2` on bit-reversed operands -/

theorem poly32Mod2Loop_zero (P D : Nat) : poly32Mod2Loop P 0 D = D := rfl

theorem poly32Mod2Loop_succ (P k D : Nat) :
    poly32Mod2Loop P (k + 1) D =
      poly32Mod2Loop P k (if D.testBit (32 + k) then D ^^^ P * 2 ^ k else D) := by
  rw [poly32Mod2Loop]; simp only [Nat.add_sub_cancel_left]

/-- The loop's result modulo `2^32` only depends on the low `32 + k` bits of the data. -/
theorem poly32Mod2Loop_mod (P : Nat) :
    ∀ k D, poly32Mod2Loop P k D % 2 ^ 32 = poly32Mod2Loop P k (D % 2 ^ (32 + k)) % 2 ^ 32
  | 0, D => by rw [poly32Mod2Loop_zero, poly32Mod2Loop_zero, Nat.add_zero, Nat.mod_mod]
  | k + 1, D => by
    rw [poly32Mod2Loop_succ, poly32Mod2Loop_succ]
    rw [poly32Mod2Loop_mod P k, poly32Mod2Loop_mod P k (if (D % 2 ^ (32 + (k + 1))).testBit (32 + k) then _ else _)]
    have hb : (D % 2 ^ (32 + (k + 1))).testBit (32 + k) = D.testBit (32 + k) := by
      rw [Nat.testBit_mod_two_pow]; simp
    rw [hb]
    congr 2
    apply Nat.eq_of_testBit_eq; intro j
    by_cases hc : D.testBit (32 + k) <;>
      simp only [hc, ite_true, ite_false, Bool.false_eq_true, Nat.testBit_mod_two_pow,
        Nat.testBit_xor] <;>
      by_cases hj : j < 32 + k
    all_goals first
      | simp [hj, show j < 32 + (k + 1) by omega]
      | simp [hj]

theorem rbitNat_rbitNat (n x : Nat) (h : x < 2 ^ n) : rbitNat n (rbitNat n x) = x := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_rbitNat, testBit_rbitNat]
  by_cases hj : j < n
  · simp only [hj, decide_true, Bool.true_and, show n - 1 - j < n by omega]
    congr 1; omega
  · simp only [hj, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))).symm

/-- The bit identity of one `Poly32Mod2` step (`poly32Mod2Loop_rbit`), bit `j < 32 + k`. -/
theorem poly32_step_bit (P k c v j : Nat) (hc : ∀ i, 32 ≤ i → c.testBit i = false)
    (hj : j < 32 + k) :
    (decide (k + 1 ≤ j) && (decide (j - (k + 1) < 32) && c.testBit (32 - 1 - (j - (k + 1)))) ^^
        decide (32 ≤ j) && (decide (j - 32 < k + 1) && v.testBit (k + 1 - 1 - (j - 32))) ^^
      (c.testBit 0 ^^ v.testBit 0) && (decide (k ≤ j) && P.testBit (j - k))) =
    (decide (k ≤ j) &&
        (decide (j - k < 32) &&
          (c.testBit (32 - 1 - (j - k) + 1) ^^ decide (32 - 1 - (j - k) + 1 = 0) && v.testBit 0 ^^
            (c.testBit 0 ^^ v.testBit 0) &&
              (decide (32 - 1 - (j - k) < 32) && P.testBit (32 - 1 - (32 - 1 - (j - k)))))) ^^
      decide (32 ≤ j) && (decide (j - 32 < k) && v.testBit (k - 1 - (j - 32) + 1))) := by
  have hv : ∀ (_ : 32 ≤ j), k + 1 - 1 - (j - 32) = k - 1 - (j - 32) + 1 := fun _ => by omega
  have hz' : (32 + k - j = 0) = False := by simp; omega
  rcases Nat.lt_or_ge j k with h | h
  · simp only [show (k + 1 ≤ j) = False by simp; omega, show (k ≤ j) = False by simp; omega,
      decide_false, Bool.false_and, Bool.false_xor]
    by_cases h32 : 32 ≤ j
    · simp only [h32, show j - 32 < k + 1 by omega, show j - 32 < k by omega, decide_true,
        Bool.true_and, hv h32, Bool.and_false, Bool.xor_false]
    · simp [h32]
  · have e1 : 32 - 1 - (j - k) + 1 = 32 + k - j := by omega
    have e2 : 32 - 1 - (32 - 1 - (j - k)) = j - k := by omega
    simp only [h, show j - k < 32 by omega, show 32 - 1 - (j - k) < 32 by omega, decide_true,
      Bool.true_and, decide_false, Bool.false_and, Bool.xor_false, e1, e2, hz']
    by_cases hk : k + 1 ≤ j
    · have e3 : 32 - 1 - (j - (k + 1)) = 32 + k - j := by omega
      simp only [hk, show j - (k + 1) < 32 by omega, decide_true, Bool.true_and, e3]
      by_cases h32 : 32 ≤ j
      · simp only [h32, show j - 32 < k + 1 by omega, show j - 32 < k by omega, decide_true,
          Bool.true_and, hv h32]
        all_goals cases c.testBit (32 + k - j) <;> cases v.testBit (k - 1 - (j - 32) + 1) <;>
          cases c.testBit 0 <;> cases v.testBit 0 <;> cases P.testBit (j - k) <;> simp
      · simp only [h32, decide_false, Bool.false_and, Bool.xor_false]
        all_goals cases c.testBit (32 + k - j) <;> cases c.testBit 0 <;> cases v.testBit 0 <;>
          cases P.testBit (j - k) <;> simp
    · have hjk : j = k := by omega
      have e4 : 32 + k - j = 32 := by omega
      simp only [hk, decide_false, Bool.false_and, Bool.false_xor, e4, hc 32 (Nat.le_refl _)]
      by_cases h32 : 32 ≤ j
      · simp only [h32, show j - 32 < k + 1 by omega, show j - 32 < k by omega, decide_true,
          Bool.true_and, hv h32]
        all_goals cases v.testBit (k - 1 - (j - 32) + 1) <;> cases c.testBit 0 <;> cases v.testBit 0 <;>
          cases P.testBit (j - k) <;> simp
      · simp only [h32, decide_false, Bool.false_and, Bool.xor_false, Bool.false_xor]

/-- One iteration of `Poly32Mod2` on `BitReverse(c) : Zeros(k) EOR BitReverse(v) : Zeros(32)` is
one shift of the reflected register `c` by bit 0 of `v` (`R = BitReverse(P)`). -/
theorem poly32Mod2Loop_rbit (P : Nat) :
    ∀ k c v, c < 2 ^ 32 →
      poly32Mod2Loop P k (rbitNat 32 c * 2 ^ k ^^^ rbitNat k v * 2 ^ 32) % 2 ^ 32 =
        rbitNat 32 (CRC.bits (rbitNat 32 P) k c v) := by
  intro k
  induction k with
  | zero =>
    intro c v hc
    rw [poly32Mod2Loop_zero, show CRC.bits (rbitNat 32 P) 0 c v = c from rfl,
      show rbitNat 0 v = 0 from rfl]
    simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_mul, Nat.xor_zero]
    exact Nat.mod_eq_of_lt (rbitNat_lt_two_pow 32 c)
  | succ k ih =>
    intro c v hc
    have hR := rbitNat_lt_two_pow 32 P
    have hc' : CRC.shift1 (rbitNat 32 P) (c ^^^ v % 2) < 2 ^ 32 :=
      CRC.shift1_lt hR (Nat.xor_lt_two_pow hc (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)))
    rw [poly32Mod2Loop_succ,
      show CRC.bits (rbitNat 32 P) (k + 1) c v =
        CRC.bits (rbitNat 32 P) k (CRC.shift1 (rbitNat 32 P) (c ^^^ v % 2)) (v / 2) from rfl,
      poly32Mod2Loop_mod P k, ← ih _ (v / 2) hc']
    congr 2
    have hcb : ∀ i, 32 ≤ i → c.testBit i = false := fun i hi =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) hi))
    have hf : (rbitNat 32 c * 2 ^ (k + 1) ^^^ rbitNat (k + 1) v * 2 ^ 32).testBit (32 + k) =
        (c.testBit 0 ^^ v.testBit 0) := by
      simp only [Nat.testBit_xor, Nat.testBit_mul_two_pow, testBit_rbitNat]
      simp only [show k + 1 ≤ 32 + k by omega, show 32 + k - (k + 1) < 32 by omega,
        show 32 - 1 - (32 + k - (k + 1)) = 0 by omega, show 32 ≤ 32 + k by omega,
        show 32 + k - 32 < k + 1 by omega, show k + 1 - 1 - (32 + k - 32) = 0 by omega,
        decide_true, Bool.true_and]
    rw [hf]
    apply Nat.eq_of_testBit_eq; intro j
    have key : ∀ f : Bool,
        ((if (c.testBit 0 ^^ v.testBit 0) = true then
            (rbitNat 32 c * 2 ^ (k + 1) ^^^ rbitNat (k + 1) v * 2 ^ 32) ^^^ P * 2 ^ k
          else rbitNat 32 c * 2 ^ (k + 1) ^^^ rbitNat (k + 1) v * 2 ^ 32) % 2 ^ (32 + k)).testBit j =
        (decide (j < 32 + k) && ((rbitNat 32 c * 2 ^ (k + 1)).testBit j ^^
          (rbitNat (k + 1) v * 2 ^ 32).testBit j ^^
          ((c.testBit 0 ^^ v.testBit 0) && (P * 2 ^ k).testBit j))) := by
      intro _
      cases (c.testBit 0 ^^ v.testBit 0) <;> simp [Nat.testBit_mod_two_pow, Nat.testBit_xor]
    rw [key true]
    simp only [Nat.testBit_xor, Nat.testBit_mul_two_pow, testBit_rbitNat, CRC.testBit_shift1,
      Nat.testBit_div_two, testBit_mod_two]
    by_cases hj : j < 32 + k
    · simp only [hj, decide_true, Bool.true_and]
      exact poly32_step_bit P k c v j hcb hj
    · simp only [hj, decide_false, Bool.false_and]
      symm
      simp only [show (j - k < 32) = False by simp; omega, show (j - 32 < k) = False by simp; omega,
        decide_false, Bool.false_and, Bool.and_false, Bool.xor_false]

/-- `crc32Op` is the bit-serial reflected CRC with `R = BitReverse(poly)`. -/
theorem crc32Op_eq_bits (C : Bool) (size acc val : Nat) (hacc : acc < 2 ^ 32) :
    crc32Op C size acc val =
      CRC.bits (rbitNat 32 (if C then 0x1EDC6F41 else 0x04C11DB7)) size acc val := by
  simp only [crc32Op, poly32Mod2]
  rw [poly32Mod2Loop_rbit _ size acc val hacc,
    rbitNat_rbitNat 32 _ (CRC.bits_lt (rbitNat_lt_two_pow 32 _) size acc val hacc)]

/-- The bit-reversed CRC-32 polynomial `0x04C11DB7` is the reflected `0xEDB88320`. -/
theorem rbitNat_crc32_poly : rbitNat 32 0x04C11DB7 = 0xEDB88320 := by decide

/-- The bit-reversed CRC-32C polynomial `0x1EDC6F41` is the reflected `0x82F63B78`. -/
theorem rbitNat_crc32c_poly : rbitNat 32 0x1EDC6F41 = 0x82F63B78 := by decide

/-- **CRC32{B,H,W,X} / CRC32C{B,H,W,X} are the bytewise CRC.** The instruction of size
`8 · 2^sz` on the register `acc` and the little-endian `2^sz`-byte value at `p` is
`CRC.update` over those bytes, with the reflected polynomial `0xEDB88320` (CRC-32) or
`0x82F63B78` (CRC-32C). -/
theorem crc32Op_eq_update (C : Bool) (m : Memory) (sz acc p : Nat) (hacc : acc < 2 ^ 32) :
    crc32Op C (8 * 2 ^ sz) acc (m.readLE p (2 ^ sz)) =
      CRC.update (if C then 0x82F63B78 else 0xEDB88320) m acc p (2 ^ sz) := by
  rw [crc32Op_eq_bits _ _ _ _ hacc, CRC.update_eq_bits]
  cases C <;> simp only [rbitNat_crc32_poly, rbitNat_crc32c_poly, ite_true, ite_false,
    Bool.false_eq_true]

end Janus.Arm64
