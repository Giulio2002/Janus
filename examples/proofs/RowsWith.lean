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

end Proof
