import Janus.Amd64.Exec

/-!
# The portable population count of `math/bits` equals `POPCNT`

`math/bits.OnesCount64` (Go 1.26, the code the compiler calls when the CPU has no `POPCNT`,
`runtime.x86HasPOPCNT = false`) counts the set bits of a 64-bit word with the SWAR reduction of
Hacker's Delight 5-2:

```go
x = x>>1&m0 + x&m0       // m0 = 0x5555…: 2-bit fields hold their popcount
x = x>>2&m1 + x&m1       // m1 = 0x3333…: 4-bit fields
x = (x>>4 + x) & m2      // m2 = 0x0f0f…: bytes
x += x >> 8; x += x >> 16; x += x >> 32
return int(x) & (1<<7 - 1)
```

`swar_eq_popNat` proves that it returns `Amd64.popNat 64 x`, the count `POPCNT` produces (the
model's `execCount .popcnt`), for every `x`. The proof works byte by byte: the first three
steps never move a bit across a byte boundary (`land_split` and the per-byte facts, checked for
all 256 bytes by `decide`), so they act on each byte separately and leave its popcount there;
the last three add the eight byte counts (each at most 8) into the low byte.
-/

namespace Janus.Spec.PopCount

open Janus.Amd64

/-! ## Bytes -/

/-- The byte `c` repeated `n` times (`rep 0x55 8 = 0x5555555555555555`). -/
def rep (c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => c + 256 * rep c n

/-- `f` applied to each of the `n` low bytes of `x`. -/
def bw (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => f (x % 256) + 256 * bw f n (x / 256)

/-- An `AND` splits at a byte boundary. -/
theorem land_split {a c : Nat} (b d : Nat) (ha : a < 256) (hc : c < 256) :
    (a + 256 * b) &&& (c + 256 * d) = (a &&& c) + 256 * (b &&& d) := by
  have hac : a &&& c < 2 ^ 8 := Nat.and_lt_two_pow a (by simpa using hc)
  apply Nat.eq_of_testBit_eq
  intro i
  have e1 : a + 256 * b = 2 ^ 8 * b + a := by omega
  have e2 : c + 256 * d = 2 ^ 8 * d + c := by omega
  have e3 : (a &&& c) + 256 * (b &&& d) = 2 ^ 8 * (b &&& d) + (a &&& c) := by omega
  rw [e1, e2, e3, Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (by simpa using ha),
    Nat.testBit_two_pow_mul_add _ (by simpa using hc), Nat.testBit_two_pow_mul_add _ hac]
  split <;> simp [Nat.testBit_and]

/-! ## The per-byte steps -/

def t1 (b : Nat) : Nat := (b / 2 &&& 0x55) + (b &&& 0x55)
def t2 (b : Nat) : Nat := (b / 4 &&& 0x33) + (b &&& 0x33)
def t3 (b : Nat) : Nat := (b / 16 + b) &&& 0x0f

theorem t1_lt : ∀ b, b < 256 → t1 b < 256 := by decide +kernel
theorem t2_lt : ∀ b, b < 256 → t2 b < 256 := by decide +kernel
theorem t3_lt : ∀ b, b < 256 → t3 b < 256 := by decide +kernel

/-- The byte popcount, three steps on one byte. -/
theorem t321 : ∀ b, b < 256 → t3 (t2 (t1 b)) = popNat 8 b := by decide +kernel

theorem t3t2t1_le : ∀ b, b < 256 → t3 (t2 (t1 b)) ≤ 8 := by decide +kernel

/-- Shifting in bits from the next byte up does not reach the masked bits. -/
theorem sh1 : ∀ b, b < 256 → ∀ r, r < 2 → (b / 2 + 128 * r) &&& 0x55 = b / 2 &&& 0x55 := by
  decide +kernel
theorem sh2 : ∀ b, b < 256 → ∀ r, r < 4 → (b / 4 + 64 * r) &&& 0x33 = b / 4 &&& 0x33 := by
  decide +kernel
/-- After `t2` every nibble is at most 4, so step 3 has no carry out of a byte and the bits from
the next byte up do not reach the masked ones. -/
theorem sh3 : ∀ b, b < 256 → ∀ r, r < 5 →
    (t2 (t1 b) / 16 + 16 * r + t2 (t1 b)) &&& 0x0f = t3 (t2 (t1 b)) ∧
      t2 (t1 b) / 16 + 16 * r + t2 (t1 b) < 256 := by
  decide +kernel
theorem t2_lo : ∀ b, b < 256 → t2 (t1 b) % 16 < 5 := by decide +kernel
theorem t21_lt : ∀ b, b < 256 → t2 (t1 b) < 256 := by decide +kernel

theorem bw_lt (f : Nat → Nat) (hf : ∀ b, b < 256 → f b < 256) :
    ∀ n x, bw f n x < 256 ^ n
  | 0, _ => by simp [bw]
  | n + 1, x => by
    have h1 := hf (x % 256) (Nat.mod_lt _ (by decide))
    have h2 := bw_lt f hf n (x / 256)
    simp only [bw, Nat.pow_succ]
    have : 256 * bw f n (x / 256) + 256 ≤ 256 * 256 ^ n := by
      have := Nat.mul_le_mul_left 256 (show bw f n (x / 256) + 1 ≤ 256 ^ n by omega)
      rwa [Nat.mul_add, Nat.mul_one] at this
    rw [Nat.mul_comm (256 ^ n)]; omega

theorem bw_mod (f : Nat → Nat) (n x : Nat) : bw f (n + 1) x % 256 = f (x % 256) % 256 := by
  simp only [bw]; omega

theorem bw_div (f : Nat → Nat) (n x : Nat) (hf : f (x % 256) < 256) :
    bw f (n + 1) x / 256 = bw f n (x / 256) := by
  simp only [bw]; omega

/-- Step 1 acts on each byte. -/
theorem step1 : ∀ n x, x < 256 ^ n →
    (x / 2 &&& rep 0x55 n) + (x &&& rep 0x55 n) = bw t1 n x
  | 0, x, h => by simp at h; subst h; simp [rep, bw]
  | n + 1, x, h => by
    have hb : x % 256 < 256 := Nat.mod_lt _ (by decide)
    have hy : x / 256 < 256 ^ n := by rw [Nat.pow_succ] at h; omega
    have e1 : x / 2 = (x % 256 / 2 + 128 * (x / 256 % 2)) + 256 * (x / 256 / 2) := by omega
    have e2 : x &&& (0x55 + 256 * rep 0x55 n) = (x % 256 &&& 0x55) + 256 * (x / 256 &&& rep 0x55 n) := by
      conv => lhs; rw [show x = x % 256 + 256 * (x / 256) by omega]
      exact land_split _ _ hb (by decide)
    simp only [rep]
    rw [e1, land_split _ _ (by omega) (by decide), sh1 _ hb _ (Nat.mod_lt _ (by decide)), e2]
    have ih := step1 n (x / 256) hy
    simp only [bw, t1]; omega

/-- Step 2 acts on each byte. -/
theorem step2 : ∀ n x, x < 256 ^ n →
    (x / 4 &&& rep 0x33 n) + (x &&& rep 0x33 n) = bw t2 n x
  | 0, x, h => by simp at h; subst h; simp [rep, bw]
  | n + 1, x, h => by
    have hb : x % 256 < 256 := Nat.mod_lt _ (by decide)
    have hy : x / 256 < 256 ^ n := by rw [Nat.pow_succ] at h; omega
    have e1 : x / 4 = (x % 256 / 4 + 64 * (x / 256 % 4)) + 256 * (x / 256 / 4) := by omega
    have e2 : x &&& (0x33 + 256 * rep 0x33 n) = (x % 256 &&& 0x33) + 256 * (x / 256 &&& rep 0x33 n) := by
      conv => lhs; rw [show x = x % 256 + 256 * (x / 256) by omega]
      exact land_split _ _ hb (by decide)
    simp only [rep]
    rw [e1, land_split _ _ (by omega) (by decide), sh2 _ hb _ (Nat.mod_lt _ (by decide)), e2]
    have ih := step2 n (x / 256) hy
    simp only [bw, t2]; omega

theorem bw_t21_mod16 : ∀ n z, bw (fun b => t2 (t1 b)) n z % 16 < 5
  | 0, _ => by simp [bw]
  | n + 1, z => by
    have := t2_lo (z % 256) (Nat.mod_lt _ (by decide))
    simp only [bw]; omega

/-- Step 3 acts on each byte of a word that steps 1 and 2 produced. -/
theorem step3 : ∀ n z, (bw (fun b => t2 (t1 b)) n z / 16 + bw (fun b => t2 (t1 b)) n z) &&& rep 0x0f n =
    bw (fun b => t3 (t2 (t1 b))) n z
  | 0, z => by simp [rep, bw]
  | n + 1, z => by
    have hb : z % 256 < 256 := Nat.mod_lt _ (by decide)
    have hr := bw_t21_mod16 n (z / 256)
    obtain ⟨h1, h2⟩ := sh3 (z % 256) hb (bw (fun b => t2 (t1 b)) n (z / 256) % 16) hr
    have e : bw (fun b => t2 (t1 b)) (n + 1) z / 16 + bw (fun b => t2 (t1 b)) (n + 1) z =
        (t2 (t1 (z % 256)) / 16 + 16 * (bw (fun b => t2 (t1 b)) n (z / 256) % 16) + t2 (t1 (z % 256))) +
          256 * (bw (fun b => t2 (t1 b)) n (z / 256) / 16 + bw (fun b => t2 (t1 b)) n (z / 256)) := by
      simp only [bw]; omega
    rw [e, rep, land_split _ _ h2 (by decide), h1, step3 n (z / 256)]
    simp only [bw]

theorem bw_comp (f g : Nat → Nat) (hf : ∀ b, b < 256 → f b < 256) :
    ∀ n x, bw g n (bw f n x) = bw (fun b => g (f b)) n x
  | 0, _ => rfl
  | n + 1, x => by
    have h := hf (x % 256) (Nat.mod_lt _ (by decide))
    simp only [bw]
    rw [show (f (x % 256) + 256 * bw f n (x / 256)) % 256 = f (x % 256) by omega,
      show (f (x % 256) + 256 * bw f n (x / 256)) / 256 = bw f n (x / 256) by omega,
      bw_comp f g hf n (x / 256)]

/-! ## Population count by bytes -/

theorem popNat_le : ∀ n x, popNat n x ≤ n
  | 0, _ => Nat.le_refl _
  | n + 1, x => by have := popNat_le n (x / 2); simp only [popNat]; omega

theorem popNat_mod : ∀ k x, popNat k (x % 2 ^ k) = popNat k x
  | 0, _ => rfl
  | k + 1, x => by
    simp only [popNat]
    rw [show x % 2 ^ (k + 1) % 2 = x % 2 from Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero (by
        rw [Nat.pow_succ]; simp)),
      show x % 2 ^ (k + 1) / 2 = x / 2 % 2 ^ k by rw [Nat.pow_succ', Nat.mod_mul_right_div_self],
      popNat_mod k (x / 2)]

theorem popNat_add : ∀ k m x, popNat (k + m) x = popNat k x + popNat m (x / 2 ^ k)
  | 0, m, x => by simp [popNat]
  | k + 1, m, x => by
    rw [show k + 1 + m = (k + m) + 1 by omega]
    simp only [popNat]
    rw [popNat_add k m (x / 2), Nat.div_div_eq_div_mul, ← Nat.pow_succ', Nat.succ_eq_add_one]
    omega

/-- The popcount of `n` bytes, byte by byte. -/
def sumBytes : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => popNat 8 (x % 256) + sumBytes n (x / 256)

theorem popNat_bytes : ∀ n x, popNat (8 * n) x = sumBytes n x
  | 0, _ => rfl
  | n + 1, x => by
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, popNat_add, sumBytes, ← popNat_bytes n,
      show (2 : Nat) ^ 8 = 256 by rfl, ← popNat_mod 8 x]

theorem bw_congr {f g : Nat → Nat} (h : ∀ b, b < 256 → f b = g b) : ∀ n x, bw f n x = bw g n x
  | 0, _ => rfl
  | n + 1, x => by simp only [bw, h (x % 256) (Nat.mod_lt _ (by decide)), bw_congr h n (x / 256)]

/-! ## The last three steps: adding the eight byte counts -/

theorem divb (a X : Nat) (h : a < 256) : (a + 256 * X) / 2 ^ 8 = X := by
  rw [show (2:Nat) ^ 8 = 256 by rfl, Nat.add_mul_div_left a X (by decide), Nat.div_eq_of_lt h, Nat.zero_add]

theorem tail_d (c0 c1 c2 c3 c4 c5 c6 c7 : Nat) (h0 : c0 ≤ 8) (h1 : c1 ≤ 8) (h2 : c2 ≤ 8) (h3 : c3 ≤ 8)
    (h4 : c4 ≤ 8) (h5 : c5 ≤ 8) (h6 : c6 ≤ 8) (h7 : c7 ≤ 8) :
    let c := c0 + 256 * (c1 + 256 * (c2 + 256 * (c3 + 256 * (c4 + 256 * (c5 + 256 * (c6 + 256 * c7))))))
    (c + c / 2 ^ 8) % 2 ^ 64 = (c0 + c1) + 256 * ((c1 + c2) + 256 * ((c2 + c3) + 256 * ((c3 + c4) +
      256 * ((c4 + c5) + 256 * ((c5 + c6) + 256 * ((c6 + c7) + 256 * c7)))))) := by
  intro c
  rw [divb _ _ (by omega)]
  exact (Nat.mod_eq_of_lt (by omega)).trans (by omega)

theorem tail_e (c0 c1 c2 c3 c4 c5 c6 c7 : Nat) (h0 : c0 ≤ 8) (h1 : c1 ≤ 8) (h2 : c2 ≤ 8) (h3 : c3 ≤ 8)
    (h4 : c4 ≤ 8) (h5 : c5 ≤ 8) (h6 : c6 ≤ 8) (h7 : c7 ≤ 8) :
    let d := (c0 + c1) + 256 * ((c1 + c2) + 256 * ((c2 + c3) + 256 * ((c3 + c4) +
      256 * ((c4 + c5) + 256 * ((c5 + c6) + 256 * ((c6 + c7) + 256 * c7))))))
    (d + d / 2 ^ 16) % 2 ^ 64 = (c0 + c1 + c2 + c3) + 256 * ((c1 + c2 + c3 + c4) + 256 * ((c2 + c3 + c4 + c5) +
      256 * ((c3 + c4 + c5 + c6) + 256 * ((c4 + c5 + c6 + c7) +
      256 * ((c5 + c6 + c7) + 256 * ((c6 + c7) + 256 * c7)))))) := by
  intro d
  rw [show (2:Nat) ^ 16 = 2 ^ 8 * 2 ^ 8 by rfl, ← Nat.div_div_eq_div_mul, divb _ _ (by omega),
      divb _ _ (by omega)]
  exact (Nat.mod_eq_of_lt (by omega)).trans (by omega)

theorem tail_f (c0 c1 c2 c3 c4 c5 c6 c7 : Nat) (h0 : c0 ≤ 8) (h1 : c1 ≤ 8) (h2 : c2 ≤ 8) (h3 : c3 ≤ 8)
    (h4 : c4 ≤ 8) (h5 : c5 ≤ 8) (h6 : c6 ≤ 8) (h7 : c7 ≤ 8) :
    let e := (c0 + c1 + c2 + c3) + 256 * ((c1 + c2 + c3 + c4) + 256 * ((c2 + c3 + c4 + c5) +
      256 * ((c3 + c4 + c5 + c6) + 256 * ((c4 + c5 + c6 + c7) +
      256 * ((c5 + c6 + c7) + 256 * ((c6 + c7) + 256 * c7))))))
    (e + e / 2 ^ 32) % 2 ^ 64 % 128 = c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 := by
  intro e
  rw [show (2:Nat) ^ 32 = 2 ^ 8 * 2 ^ 8 * 2 ^ 8 * 2 ^ 8 by rfl, ← Nat.div_div_eq_div_mul,
      ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, divb _ _ (by omega), divb _ _ (by omega),
      divb _ _ (by omega), divb _ _ (by omega)]
  rw [Nat.mod_eq_of_lt (a := e + _) (by omega)]
  omega

/-! ## The whole reduction -/

/-- `OnesCount64` on the natural number of a 64-bit word, step by step as the code does it
(steps 1–3 cannot exceed `2^64`; the last three wrap explicitly, as `ADDQ` does). -/
def swar (x : Nat) : Nat :=
  let a := (x / 2 &&& 0x5555555555555555) + (x &&& 0x5555555555555555)
  let b := (a / 4 &&& 0x3333333333333333) + (a &&& 0x3333333333333333)
  let c := (b / 16 + b) &&& 0x0f0f0f0f0f0f0f0f
  let d := (c + c / 2 ^ 8) % 2 ^ 64
  let e := (d + d / 2 ^ 16) % 2 ^ 64
  let f := (e + e / 2 ^ 32) % 2 ^ 64
  f % 128

/-- `math/bits.OnesCount64` returns the number of set bits. -/
theorem swar_eq_popNat (x : Nat) (hx : x < 2 ^ 64) : swar x = popNat 64 x := by
  have hx' : x < 256 ^ 8 := by simpa using hx
  have hm0 : (0x5555555555555555 : Nat) = rep 0x55 8 := by decide
  have hm1 : (0x3333333333333333 : Nat) = rep 0x33 8 := by decide
  have hm2 : (0x0f0f0f0f0f0f0f0f : Nat) = rep 0x0f 8 := by decide
  have ha := step1 8 x hx'
  have hb := step2 8 (bw t1 8 x) (bw_lt t1 t1_lt 8 x)
  rw [bw_comp t1 t2 t1_lt] at hb
  have hc := step3 8 x
  rw [bw_congr t321] at hc
  simp only [swar, hm0, hm1, hm2, ha, hb, hc]
  rw [show 64 = 8 * 8 by rfl, popNat_bytes]
  have hle : ∀ y, popNat 8 (y % 256) ≤ 8 := fun y => by
    have := t3t2t1_le (y % 256) (Nat.mod_lt _ (by decide))
    rwa [t321 _ (Nat.mod_lt _ (by decide))] at this
  simp only [bw, sumBytes, Nat.mul_zero, Nat.add_zero]
  rw [tail_d _ _ _ _ _ _ _ _ (hle _) (hle _) (hle _) (hle _) (hle _) (hle _) (hle _) (hle _),
    tail_e _ _ _ _ _ _ _ _ (hle _) (hle _) (hle _) (hle _) (hle _) (hle _) (hle _) (hle _),
    tail_f _ _ _ _ _ _ _ _ (hle _) (hle _) (hle _) (hle _) (hle _) (hle _) (hle _) (hle _)]
  omega

theorem mod64_mod128 (n : Nat) : n % 18446744073709551616 % 128 = n % 128 :=
  Nat.mod_mod_of_dvd n (by decide)

/-- `swar` with every 64-bit wrap the machine code performs (`ADDQ`, `LEAQ`), the form the
symbolic executor produces for `math/bits.OnesCount64`. -/
def swarM (x : Nat) : Nat :=
  let a := ((x &&& 0x5555555555555555) + (x / 2 &&& 0x5555555555555555)) % 2 ^ 64
  let b := ((a / 4 &&& 0x3333333333333333) + (a &&& 0x3333333333333333)) % 2 ^ 64
  let c := (b / 16 + b) % 2 ^ 64 &&& 0x0f0f0f0f0f0f0f0f
  let d := (c + c / 2 ^ 8) % 2 ^ 64
  let e := (d + d / 2 ^ 16) % 2 ^ 64
  let f := (e + e / 2 ^ 32) % 2 ^ 64
  f % 128

theorem swarM_eq_popNat (x : Nat) (hx : x < 2 ^ 64) : swarM x = popNat 64 x := by
  rw [← swar_eq_popNat x hx]
  have h1 : x &&& 0x5555555555555555 ≤ 0x5555555555555555 := Nat.and_le_right
  have h2 : x / 2 &&& 0x5555555555555555 ≤ 0x5555555555555555 := Nat.and_le_right
  simp only [swarM, swar]
  rw [Nat.mod_eq_of_lt (a := (x &&& _) + _) (by omega), Nat.add_comm (x &&& _)]
  generalize (x / 2 &&& 6148914691236517205) + (x &&& 6148914691236517205) = a
  have h3 : a / 4 &&& 0x3333333333333333 ≤ 0x3333333333333333 := Nat.and_le_right
  have h4 : a &&& 0x3333333333333333 ≤ 0x3333333333333333 := Nat.and_le_right
  rw [Nat.mod_eq_of_lt (a := (a / 4 &&& _) + _) (by omega)]
  have h5 : (a / 4 &&& 3689348814741910323) + (a &&& 3689348814741910323) ≤ 2 * 0x3333333333333333 := by
    omega
  generalize (a / 4 &&& 3689348814741910323) + (a &&& 3689348814741910323) = b at h5 ⊢
  rw [Nat.mod_eq_of_lt (a := b / 16 + b) (by omega)]

end Janus.Spec.PopCount
