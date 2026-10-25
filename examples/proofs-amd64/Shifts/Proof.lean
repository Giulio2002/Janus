import Janus
import Extracted

/-! `example.com/basic.Shifts(x uint64, y int64, n uint64)` on amd64: shifts by a variable amount.

For all 64-bit `x`, `y`, `n` (every count, including `n ≥ 64`), the results have Go's shift
semantics, stated arithmetically: `RAX = x << n` is `x · 2^n mod 2^64` (`0` for `n ≥ 64`),
`RBX = y >> n` (signed) is `⌊y / 2^n⌋` (`-1` or `0` for `n ≥ 64`), `RCX = x >> n` (unsigned) is
`⌊x / 2^n⌋`. The hardware shifts (`SHLQ`/`SHRQ`/`SARQ CL`) use `n mod 64`; the compiler builds a
mask with `CMPQ n, $64; SBBQ` that clears the logical results and saturates the arithmetic count
to 63 when `n ≥ 64`. A shift by a count that is `0 mod 64` leaves the flags unchanged, so the
executor splits on it; every path is covered. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

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

/-- The mask the code builds with `CMPQ n, $64; SBBQ`: all ones iff `n < 64`. -/
abbrev mask (n : BitVec 64) : BitVec 64 := if n.toNat < 64 then 18446744073709551615#64 else 0#64

theorem shl_spec (x n : BitVec 64) :
    (x <<< (n.toNat % 64) &&& mask n).toNat = x.toNat * 2 ^ n.toNat % 2 ^ 64 := by
  simp only [mask]; split
  · rename_i h
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes,
      Nat.mod_eq_of_lt h, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · rename_i h
    rw [BitVec.and_zero,
      show n.toNat = 64 + (n.toNat - 64) by omega, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm _ (2 ^ 64),
      Nat.mul_assoc, Nat.mul_mod_right]; rfl

theorem shr_spec (x n : BitVec 64) :
    (x >>> (n.toNat % 64) &&& mask n).toNat = x.toNat / 2 ^ n.toNat := by
  simp only [mask]; split
  · rename_i h
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes,
      Nat.mod_eq_of_lt h, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · rename_i h
    have : x.toNat < 2 ^ n.toNat :=
      Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [BitVec.and_zero, Nat.div_eq_of_lt this]; rfl

theorem sar_spec (y n : BitVec 64) :
    (y.sshiftRight ((n ||| ~~~mask n).toNat % 64)).toInt = y.toInt / ((2 ^ n.toNat : Nat) : Int) := by
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  simp only [mask]; split
  · rename_i h
    rw [show (~~~18446744073709551615#64) = 0#64 from rfl, BitVec.or_zero, Nat.mod_eq_of_lt h]
  · rename_i h
    rw [show (~~~0#64) = BitVec.allOnes 64 from rfl, BitVec.or_allOnes,
      show (BitVec.allOnes 64).toNat % 64 = 63 from rfl, ediv_big y 63 (by omega),
      ediv_big y _ (by omega)]

theorem correctness (x y n : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y, n] 3
      (fun s => StackWritable s 0 8)
      (fun r => ∃ a b c, r = [a, b, c] ∧ a.toNat = x.toNat * 2 ^ n.toNat % 2 ^ 64 ∧
        b.toInt = y.toInt / ((2 ^ n.toNat : Nat) : Int) ∧ c.toNat = x.toNat / 2 ^ n.toNat) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  all_goals refine ⟨_, _, _, rfl, ?_⟩
  -- Shifts by a count that is 0 mod 64 leave the flags alone; the executor splits on it, and on
  -- those paths the shift was simplified away.
  all_goals
    have e1 := shl_spec x n; have e2 := sar_spec y n; have e3 := shr_spec x n
    try (rename_i h0; simp only [h0, hbr, BitVec.shiftLeft_zero, BitVec.ushiftRight_zero,
      BitVec.sshiftRight_zero] at e1 e2 e3)
    exact ⟨e1, e2, e3⟩

end Proof
