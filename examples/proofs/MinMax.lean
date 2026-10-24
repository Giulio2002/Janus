import Extracted

/-!
# `MinMax(x, y, z int64) (lo, hi int64, spread uint64)`: the `min`/`max` builtins

**Guarantee.** For all 64-bit `x`, `y`, `z` and every Go call state of `example.com/basic.MinMax`,
the call returns (never faulting or panicking), obeys the ABI, and, reading the arguments as
signed (two's complement) integers: `lo = X0` is the smallest of `x`, `y`, `z`, `hi = X1` the
largest, and `spread = X2` (unsigned) is the exact distance `hi - lo`, which may exceed the
`int64` range (e.g. `max - min` of `-2^63` and `2^63 - 1`) but always fits in `uint64`.

`min` and `max` compile to compare-and-select (`cmp`, `csel lt` / `csel gt`), without branches.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

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
      (((18446744073709551616 - lo.toNat + hi.toNat) % 18446744073709551616 : Nat) : Int) =
        hi.toInt - lo.toInt :=
  ⟨hlo, hhi, dist_toNat lo hi (by omega)⟩

theorem correctness (x y z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y, z] (fun _ => True)
      (fun _ s' => (s'.regs 0).toInt = min (min x.toInt y.toInt) z.toInt ∧
        (s'.regs 1).toInt = max (max x.toInt y.toInt) z.toInt ∧
        ((s'.regs 2).toNat : Int) = (s'.regs 1).toInt - (s'.regs 0).toInt) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  refine spec_of x y z _ _ ?_ ?_ <;> (repeat' split) <;> omega

end Proof
