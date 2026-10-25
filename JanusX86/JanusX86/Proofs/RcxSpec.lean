import JanusX86.Proofs.Shd

/-! # RCL/RCR at 32/64 bits: Janus' value and the model's rotate through carry -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

/-- Janus' `execRcx` rotated `w+1`-bit value (`cf:x` rotated by `c`). -/
def rcxRaw (left : Bool) {w : Nat} (b : Bool) (x : BitVec w) (c : Nat) : Nat :=
  let t := b.toNat * 2 ^ w + x.toNat
  if left then t * 2 ^ c % 2 ^ (w + 1) + t / 2 ^ (w + 1 - c)
  else t / 2 ^ c + t * 2 ^ (w + 1 - c) % 2 ^ (w + 1)

theorem ofNat_cat (w : Nat) (x : BitVec w) (b : Bool) :
    BitVec.ofNat (w + 1) (b.toNat * 2 ^ w + x.toNat) = BitVec.cast (by omega) (BitVec.ofBool b ++ x) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hb : b.toNat < 2 := by cases b <;> decide
  have hlt : b.toNat * 2 ^ w + x.toNat < 2 ^ (w + 1) := by rw [Nat.pow_succ]; cases b <;> simp <;> omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, BitVec.toNat_cast, BitVec.toNat_append, BitVec.toNat_ofBool,
    ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]

theorem chs_val (w n : Nat) (hn : n = w + 1) (x : BitVec w) (b : Bool) :
    changeSlice_bits (Sail.BitVec.zeroExtend x n) w 1 (BitVec.ofBool b) =
      BitVec.ofNat n (b.toNat * 2 ^ w + x.toNat) := by
  subst hn
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [changeSlice_bits, Sail.BitVec.updateSubrange]
  rw [getLsbD_updateSubrange' _ w _ _ i (by omega), ofNat_cat, BitVec.getLsbD_cast, BitVec.getLsbD_append]
  have e : ((w : Int) + (1 : Nat) - 1).toNat - w + 1 = 1 := by omega
  by_cases hiw : i < w
  · rw [if_neg (by omega), if_pos hiw]
    simp [Sail.BitVec.zeroExtend, BitVec.getLsbD_setWidth, hiw]; omega
  · rw [if_pos (by omega), if_neg hiw]
    have : i - w = 0 := by omega
    rw [this]
    simp [BitVec.getLsbD_setWidth]

theorem rotl_nat (n c t : Nat) (hc : c < n) (ht : t < 2 ^ n) :
    ((BitVec.ofNat n t).rotateLeft c).toNat = t * 2 ^ c % 2 ^ n + t / 2 ^ (n - c) := by
  rw [BitVec.toNat_rotateLeft, Nat.mod_eq_of_lt hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have h2 : 2 ^ n = 2 ^ (n - c) * 2 ^ c := by rw [← Nat.pow_add]; congr 1; omega
  have hlt : t / 2 ^ (n - c) < 2 ^ c := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← h2]; exact ht
  rw [h2, Nat.mul_mod_mul_right, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hlt]

theorem rotr_nat (n c t : Nat) (hc : c < n) (ht : t < 2 ^ n) :
    ((BitVec.ofNat n t).rotateRight c).toNat = t / 2 ^ c + t * 2 ^ (n - c) % 2 ^ n := by
  rw [BitVec.toNat_rotateRight, Nat.mod_eq_of_lt hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have h2 : 2 ^ n = 2 ^ c * 2 ^ (n - c) := by rw [← Nat.pow_add]; congr 1; omega
  have hlt : t / 2 ^ c < 2 ^ (n - c) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← h2]; exact ht
  rw [h2, Nat.mul_mod_mul_right, ← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.add_comm]

/-- The rotated `w+1`-bit value `cf:x`. -/
def rcxR (left : Bool) (b : Bool) {w : Nat} (x : BitVec w) (c : Nat) : BitVec (w + 1) :=
  if left then (BitVec.ofNat (w + 1) (b.toNat * 2 ^ w + x.toNat)).rotateLeft c
  else (BitVec.ofNat (w + 1) (b.toNat * 2 ^ w + x.toNat)).rotateRight c

def rcxVal (left : Bool) (b : Bool) {w : Nat} (x : BitVec w) (c : Nat) : BitVec w :=
  if c = 0 then x else (rcxR left b x c).setWidth w

def rcxFl (left : Bool) (b : Bool) {w : Nat} (x : BitVec w) (c : Nat) (f : Flags) : Flags :=
  let ncf := (rcxR left b x c).getLsbD w
  let o : Option Bool :=
    if c = 1 then some (if left then (rcxVal left b x c).msb != ncf else x.msb != b) else none
  if c = 0 then { f with ovf := none } else { f with cf := some ncf, ovf := o }

theorem ofBool_get0 (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := by
  have : v = 0#1 ∨ v = 1#1 := by
    have := v.isLt; rcases (show v.toNat = 0 ∨ v.toNat = 1 by omega) with h | h
    · left; exact BitVec.eq_of_toNat_eq h
    · right; exact BitVec.eq_of_toNat_eq h
  rcases this with rfl | rfl <;> rfl

theorem tr_ofNat_cat (w n : Nat) (hn : n = w + 1) (x : BitVec w) (b : Bool) :
    Sail.BitVec.truncate (BitVec.ofNat n (b.toNat * 2 ^ w + x.toNat)) w = x := by
  subst hn
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Sail.BitVec.truncate, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, ofNat_cat,
    BitVec.getLsbD_cast, BitVec.getLsbD_append, hi, decide_true, Bool.true_and, ↓reduceIte]

end JanusX86.Proofs
