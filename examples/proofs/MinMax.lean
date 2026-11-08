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


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (3) else if i = 1 then (5) else if i = 2 then (4) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(3 : BitVec 64), (5 : BitVec 64), (4 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y, z] s ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toInt = min (min x.toInt y.toInt) z.toInt ∧
        (s'.regs 1).toInt = max (max x.toInt y.toInt) z.toInt ∧
        ((s'.regs 2).toNat : Int) = (s'.regs 1).toInt - (s'.regs 0).toInt)) := by
  refine ⟨ret, s0, (3), (5), (4), hret, setup, ?pre, correctness (3) (5) (4) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
