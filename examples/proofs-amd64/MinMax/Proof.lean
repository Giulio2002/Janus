import Janus
import Extracted

/-! `example.com/basic.MinMax(x, y, z int64) (lo, hi int64, spread uint64)` on amd64: the
`min`/`max` builtins.

For all 64-bit `x`, `y`, `z`, read as signed (two's complement) integers: `lo = RAX` is the
smallest of `x`, `y`, `z`, `hi = RBX` the largest, and `spread = RCX` (unsigned) is the exact
distance `hi - lo`, which may exceed the `int64` range but always fits in `uint64`. `min` and
`max` compile to `CMPQ` and conditional moves (`CMOVL`, `CMOVG`), without branches. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The unsigned difference `b - a` (computed modulo `2^64`) of two words with `a ≤ b` as signed
integers is their exact distance. -/
theorem dist_toNat (a b : BitVec 64) (h : a.toInt ≤ b.toInt) :
    (((2 ^ 64 - a.toNat + b.toNat) % 2 ^ 64 : Nat) : Int) = b.toInt - a.toInt := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at *
  have := a.isLt; have := b.isLt
  by_cases ha : 2 * a.toNat < 2 ^ 64 <;> by_cases hb : 2 * b.toNat < 2 ^ 64 <;>
    simp only [ha, hb, ite_true, ite_false] at h ⊢ <;> omega

theorem spec_of (x y z lo hi : BitVec 64) (hlo : lo.toInt = min (min x.toInt y.toInt) z.toInt)
    (hhi : hi.toInt = max (max x.toInt y.toInt) z.toInt) :
    lo.toInt = min (min x.toInt y.toInt) z.toInt ∧ hi.toInt = max (max x.toInt y.toInt) z.toInt ∧
      ((hi - lo).toNat : Int) = hi.toInt - lo.toInt :=
  ⟨hlo, hhi, by rw [BitVec.toNat_sub]; exact dist_toNat lo hi (by omega)⟩

theorem correctness (x y z : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y, z] 3
      (fun s => StackWritable s 0 8)
      (fun r => ∃ lo hi spread, r = [lo, hi, spread] ∧
        lo.toInt = min (min x.toInt y.toInt) z.toInt ∧ hi.toInt = max (max x.toInt y.toInt) z.toInt ∧
        (spread.toNat : Int) = hi.toInt - lo.toInt) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  refine ⟨_, _, _, rfl, ?_⟩
  refine spec_of x y z _ _ ?_ ?_ <;> (repeat' split) <;> omega

end Proof
