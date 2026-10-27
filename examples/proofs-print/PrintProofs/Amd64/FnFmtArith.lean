import PrintProofs.Amd64.FnHead

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

namespace PrintFn

/-! ## `internal/strconv.formatBase10` -/

/-- The table `internal/strconv.smalls` ("00010203…99", `LEAQ` in `formatBase10`). -/
def SM : Nat := ripTarget P (segAddr P "internal/strconv.formatBase10" + 0x91)

/-- Byte `j` of `smalls`: the two decimal digits of every number below 100, in order. -/
def smallsByte (j : Nat) : Nat := if j % 2 = 0 then 48 + j / 20 else 48 + j / 2 % 10

theorem smalls_data : ∀ j, j < 200 → dataRead P (SM + j) 1 = some (smallsByte j) := by
  janus_eval_nat h : SM
  rw [h]
  have hall : (List.range 200).all (fun j => dataRead P (SM + j) 1 == some (smallsByte j)) = true := by
    rw [h]; decide +kernel
  intro j hj
  have := List.all_eq_true.mp hall j (List.mem_range.mpr hj)
  rw [h] at this
  simpa using this

theorem smalls_hi (k : Nat) (hk : k < 100) :
    BitVec.ofNat 8 (smallsByte (k * 2)) = Janus.Spec.Print.digit (k / 10) := by
  unfold smallsByte Janus.Spec.Print.digit
  rw [if_pos (by omega)]; congr 1; omega

theorem smalls_lo (k : Nat) (hk : k < 100) :
    BitVec.ofNat 8 (smallsByte (k * 2 + 1)) = Janus.Spec.Print.digit (k % 10) := by
  unfold smallsByte Janus.Spec.Print.digit
  rw [if_neg (by omega)]; congr 1; omega

theorem smallsByte_mod256 (j : Nat) (h : j < 200) : smallsByte j % 256 = smallsByte j := by
  unfold smallsByte; split <;> omega

/-! The magic multiplications of `formatBase10` (at the bit-vector level: `simp` with
`BitVec.toNat_mul` and `BitVec.toNat_ofNat` does not terminate on these products). -/

theorem mul_lsr37 (y : Nat) (h : y < 2 ^ 31) :
    (BitVec.ofNat 64 y * 2748779070#64) >>> 37 = BitVec.ofNat 64 (y / 50) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 2748779070 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show y * 2748779070 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show y / 50 < 2 ^ 64 by omega)]
  exact magic50 y h

/-- `MOVL` (zero-extend the low 32 bits), `SHRQ $1`, `IMULQ $0xa3d70a3e`, `SHRQ $37`: `x / 100`. -/
theorem div100_magic64 (x : Nat) (h : x < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x)) >>> 1 * 2748779070#64) >>> 37 =
      BitVec.ofNat 64 (x / 100) := by
  have e : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x)) >>> 1 = BitVec.ofNat 64 (x / 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  rw [e, mul_lsr37 (x / 2) (by omega)]
  congr 1; omega

/-- `SHRQ $1`, `MULQ` by `0x89705f4136b4a598` (the high half), `SHRQ $28`: `U / 10^9`. -/
theorem div1e9_64 (U : Nat) (hU : U < 2 ^ 64) :
    BitVec.ofNat 64 (9903520314283042200 * (BitVec.ofNat 64 U >>> 1).toNat / 18446744073709551616) >>> 28 =
      BitVec.ofNat 64 (U / 1000000000) := by
  have e1 : (BitVec.ofNat 64 U >>> 1).toNat = U / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hU]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, e1, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show 9903520314283042200 * (U / 2) / 18446744073709551616 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show U / 1000000000 < 2 ^ 64 by omega), Nat.div_div_eq_div_mul,
    show (18446744073709551616 : Nat) * 2 ^ 28 = 2 ^ 92 by decide, Nat.mul_comm, magic5e8 (U / 2) (by omega)]
  omega

/-- `IMULQ $10^9` and `SUBQ`: `U % 10^9`. -/
theorem mod1e9_64 (U : Nat) (hU : U < 2 ^ 64) :
    BitVec.ofNat 64 U - BitVec.ofNat 64 (U / 1000000000) * 1000000000#64 = BitVec.ofNat 64 (U % 1000000000) := by
  rw [show (1000000000#64 : BitVec 64) = BitVec.ofNat 64 1000000000 from rfl, BitVec.ofNat_mul_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The remainder after `/ 100` (32-bit `IMULL $100`, `SUBL`). -/
theorem mod100_32 (x : Nat) (h : x < 2 ^ 32) :
    (4294967296 - x / 100 * 100 % 4294967296 + x % 4294967296) % 4294967296 = x % 100 := by
  omega

theorem mul100_32 (q : Nat) (h : q * 100 < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 q) * 100#32).toNat = q * 100 := by
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem two_mul32 (x : Nat) (h : x < 2 ^ 31) : (x + x) % 4294967296 = x * 2 := by omega
theorem two_mul32' (x : Nat) (h : x < 2 ^ 31) : ((x + x) % 4294967296 + 1) % 4294967296 = x * 2 + 1 := by omega

theorem ofNat8_smallsByte_mod (j : Nat) (h : j < 200) :
    BitVec.ofNat 8 (smallsByte j % 256) = BitVec.ofNat 8 (smallsByte j) := by
  rw [smallsByte_mod256 j h]

theorem bhi (w r : Nat) (hr : r < 100) (hw : w = r * 2) :
    BitVec.ofNat 8 (smallsByte w % 256) = Janus.Spec.Print.digit (r / 10) := by
  subst hw; rw [smallsByte_mod256 _ (by omega)]; exact smalls_hi r hr

theorem blo (w r : Nat) (hr : r < 100) (hw : w = r * 2 + 1) :
    BitVec.ofNat 8 (smallsByte w % 256) = Janus.Spec.Print.digit (r % 10) := by
  subst hw; rw [smallsByte_mod256 _ (by omega)]; exact smalls_lo r hr

/-- What the rest of `formatBase10` from the final chunk's loop head guarantees: it returns
`i - |decimal lo|` with the digits of `lo` written in front of the bytes already at `[a + i, a + 20)`. -/
def FbTail (s : State) (SP a i lo : Nat) (m0 : Memory) (s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory),
    s' = retState64 s junk [BitVec.ofNat 64 (i - (Janus.Spec.Print.decimal lo).length)] f x yh m ∧
    MemFrame s.mem m [(SP - 8, SP), (SP + 8, SP + 16), (a, a + 20)] ∧
    readBytes m (a + (i - (Janus.Spec.Print.decimal lo).length))
        (20 - (i - (Janus.Spec.Print.decimal lo).length)) =
      Janus.Spec.Print.decimal lo ++ readBytes m0 (a + i) (20 - i)

end PrintFn
