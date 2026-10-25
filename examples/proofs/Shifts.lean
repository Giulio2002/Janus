import Extracted

/-!
# `Shifts(x uint64, y int64, n uint64) (uint64, int64, uint64)`: shifts by a variable amount

**Guarantee.** For all 64-bit `x`, `y`, `n` (every shift count, including `n ≥ 64`) and every Go
call state of `example.com/basic.Shifts`, the call returns (never faulting or panicking), obeys
the ABI, and the results have Go's shift semantics, stated arithmetically:
* `X0 = x << n` is `x · 2^n mod 2^64` (so `0` when `n ≥ 64`);
* `X1 = y >> n`, with `y` signed, is `⌊y / 2^n⌋` (so `-1` or `0` when `n ≥ 64`);
* `X2 = x >> n`, with `x` unsigned, is `⌊x / 2^n⌋` (so `0` when `n ≥ 64`).

The hardware shifts (`lsl`, `lsr`, `asr` by register) use only `n mod 64`; the compiler adds
`cmp n, #64` and `csel`s that select `0` (or a shift by 63 for `asr`) when `n ≥ 64`. The theorem
covers both sides.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- An arithmetic shift right by `m ≥ 63` of a 64-bit signed value is its sign. -/
theorem ediv_big (y : BitVec 64) (m : Nat) (hm : 63 ≤ m) :
    y.toInt / ((2 ^ m : Nat) : Int) = if y.toInt < 0 then -1 else 0 := by
  have h1 := BitVec.toInt_lt (x := y); have h2 := BitVec.le_toInt (x := y)
  have hp : 2 ^ 63 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  simp only [Nat.add_one_sub_one] at h1 h2
  rw [Int.ediv_eq_iff_of_pos (by omega)]
  generalize 2 ^ m = D at *
  rw [show (2 : Int) ^ 63 = ((2 ^ 63 : Nat) : Int) from rfl] at h1 h2
  split <;> omega

theorem shl_spec (x n : BitVec 64) :
    (if n.toNat < 64 then x <<< (n.toNat % 64) else 0#64).toNat = x.toNat * 2 ^ n.toNat % 2 ^ 64 := by
  split
  · rename_i h; rw [Nat.mod_eq_of_lt h, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · rename_i h
    rw [show n.toNat = 64 + (n.toNat - 64) by omega, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm _ (2 ^ 64),
      Nat.mul_assoc, Nat.mul_mod_right]; rfl

theorem shr_spec (x n : BitVec 64) :
    (if n.toNat < 64 then x >>> (n.toNat % 64) else 0#64).toNat = x.toNat / 2 ^ n.toNat := by
  split
  · rename_i h; rw [Nat.mod_eq_of_lt h, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · rename_i h
    have : x.toNat < 2 ^ n.toNat :=
      Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.div_eq_of_lt this]; rfl

theorem sar_spec (y n : BitVec 64) :
    (y.sshiftRight ((if n.toNat < 64 then n else 63#64).toNat % 64)).toInt =
      y.toInt / ((2 ^ n.toNat : Nat) : Int) := by
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  split
  · rename_i h; rw [Nat.mod_eq_of_lt h]
  · rename_i h
    rw [show (63#64).toNat % 64 = 63 from rfl, ediv_big y 63 (by omega), ediv_big y _ (by omega)]

theorem correctness (x y n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y, n] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = x.toNat * 2 ^ n.toNat % 2 ^ 64 ∧
        (s'.regs 1).toInt = y.toInt / ((2 ^ n.toNat : Nat) : Int) ∧ (s'.regs 2).toNat = x.toNat / 2 ^ n.toNat) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  exact ⟨shl_spec x n, sar_spec y n, shr_spec x n⟩

end Proof
