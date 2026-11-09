import JanusX86.Proofs.ShiftSpec

/-! # SHLD/SHRD: Janus' value and flags, and the model's double-width value -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

/-- Janus' `execShd` result (`left` = SHLD), masked count `c`. -/
def shdVal (left : Bool) {w : Nat} (x y : BitVec w) (c : Nat) : BitVec w :=
  if left then BitVec.ofNat w ((x.toNat * 2 ^ w + y.toNat) * 2 ^ c / 2 ^ w)
  else BitVec.ofNat w ((y.toNat * 2 ^ w + x.toNat) / 2 ^ c)

/-- Janus' `execShd` flags (`c = 0`: unchanged). -/
def shdFl (left : Bool) {w : Nat} (x y : BitVec w) (c : Nat) (f : Flags) : Flags :=
  if c = 0 then f else
  { cf := some (if left then x.getLsbD (w - c) else x.getLsbD (c - 1)),
    pf := some (parity (shdVal left x y c).toNat), af := none,
    zf := some (decide (shdVal left x y c = 0)), sf := some (shdVal left x y c).msb,
    ovf := if c = 1 then some ((shdVal left x y c).msb != x.msb) else none }

theorem shdVal_zero (left : Bool) {w : Nat} (x y : BitVec w) : shdVal left x y 0 = x := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  cases left <;> simp only [shdVal, Bool.false_eq_true, ↓reduceIte, Nat.pow_zero, Nat.mul_one, Nat.div_one,
    BitVec.toNat_ofNat]
  · rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hx
  · have hp : 0 < 2 ^ w := Nat.two_pow_pos w
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hy, Nat.zero_add]; exact Nat.mod_eq_of_lt hx

theorem concat_val (W n : Nat) (hn : n = W + W) {x y : BitVec W} :
    Sail.BitVec.toNatInt (bits_of_int (ash_left_int (Sail.BitVec.toNatInt x) W) n ||| Sail.BitVec.zeroExtend y n) =
      ((x.toNat * 2 ^ W + y.toNat : Nat) : Int) := by
  subst hn
  have hx := x.isLt; have hy := y.isLt
  have ha : ash_left_int (Sail.BitVec.toNatInt x) W = ((x.toNat * 2 ^ W : Nat) : Int) := by
    simp only [ash_left_int, Sail.BitVec.toNatInt, ipowI]; push_cast; rfl
  have hlt : x.toNat * 2 ^ W < 2 ^ (W + W) := by
    rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos W)
  have hylt : y.toNat < 2 ^ (W + W) := Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega))
  rw [ha]
  simp only [Sail.BitVec.toNatInt, BitVec.toNat_or, bits_of_int_natCast_toNat, Sail.BitVec.zeroExtend,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hylt]
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hy]; rfl

theorem bits_natCast (N W : Nat) : bits_of_int (N : Int) W = BitVec.ofNat W N := by
  apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp

theorem shld_val (W : Nat) {x y : BitVec W} (c : Nat) (hc : c ≤ W) (A : Nat) (hA : A = x.toNat * 2 ^ W + y.toNat) :
    bits_of_int (ash_int (A : Int) ((c : Int) - (W : Int))) W = shdVal true x y c := by
  have e : (c : Int) - (W : Int) = -((W - c : Nat) : Int) := by omega
  rw [e, ash_neg, show ((2 : Int) ^ (W - c)) = ((2 ^ (W - c) : Nat) : Int) by push_cast; rfl,
    ← Int.natCast_ediv, bits_natCast]
  simp only [shdVal, ↓reduceIte, ← hA]
  congr 1
  have : 2 ^ W = 2 ^ (W - c) * 2 ^ c := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos c)]

theorem shrd_val (W : Nat) {x y : BitVec W} (c : Nat) (A : Nat) (hA : A = y.toNat * 2 ^ W + x.toNat) :
    bits_of_int (ash_int (A : Int) (-(c : Int))) W = shdVal false x y c := by
  rw [ash_neg, show ((2 : Int) ^ c) = ((2 ^ c : Nat) : Int) by push_cast; rfl, ← Int.natCast_ediv, bits_natCast]
  simp only [shdVal, Bool.false_eq_true, ↓reduceIte, ← hA]

theorem toNatInt_ze6 (c n : Nat) (hc : c < 64) (hn : 6 ≤ n) :
    Sail.BitVec.toNatInt (Sail.BitVec.zeroExtend (BitVec.ofNat 6 c) n) = (c : Int) := by
  have h1 : c < 2 ^ 6 := by omega
  have h2 : c < 2 ^ n := Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) hn)
  have e : (Sail.BitVec.zeroExtend (BitVec.ofNat 6 c) n).toNat = c := by
    simp only [Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  simp only [Sail.BitVec.toNatInt, e]; rfl

end JanusX86.Proofs
