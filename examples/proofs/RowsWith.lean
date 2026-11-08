import Extracted

/-!
# `RowsWith(m *[2][3]uint64, x uint64) uint64`: nested loops and a labeled `continue`

**Guarantee.** For every pointer `m` to 48 readable bytes (`Ptr`; the `2×3` array, row-major)
and every 64-bit `x`, and every Go call state of `example.com/basic.RowsWith`, the call returns
(never faulting or panicking), obeys the ABI, and `X0` is the number of rows `i ∈ {0, 1}` that
contain `x`, i.e. for which some `j ∈ {0, 1, 2}` has `m[i][j] = x`.

`continue rows` abandons the inner loop at the first match and continues the outer one. Both
loops have constant trip counts, so `janus_run` executes them; each row ends in one of four
ways (a match at column 0, 1 or 2, or none), so there are sixteen paths.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Row `i` of the `n×3` array at `m` (in memory `mem`) contains `x`. -/
def rowHas (mem : Memory) (m : Nat) (x : Nat) (i : Nat) : Bool :=
  (List.range 3).any fun j => mem.readLE (m + 8 * (3 * i + j)) 8 == x

theorem correctness (m x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [m, x] (fun s => Ptr s.mem m 48 false)
      (fun s s' => (s'.regs 0).toNat = ((List.range 2).filter (rowHas s.mem m.toNat x.toNat)).length) := by
  intro ret hret s hs ⟨hp, hp'⟩
  janus_intro hs
  janus_run
  all_goals
    simp only [rowHas, List.range, List.range.loop, List.any_cons, List.any_nil, List.filter_cons,
      List.filter_nil, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.mul_zero, Bool.or_false]
    simp only [Bool.or_eq_true, beq_iff_eq]
    repeat' split
    all_goals (try simp only [List.length_cons, List.length_nil, true_or, or_true,
      not_true_eq_false] at *)
    all_goals omega


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (0) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (0 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (m : BitVec 64) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [m, x] s ∧ (Ptr s.mem m 48 false) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = ((List.range 2).filter (rowHas s.mem m.toNat x.toNat)).length)) := by
  refine ⟨ret, s0, (0x300000), (0), hret, setup, ?pre, correctness (0x300000) (0) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
