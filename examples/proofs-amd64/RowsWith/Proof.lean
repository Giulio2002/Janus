import Janus
import Extracted

/-! `example.com/basic.RowsWith(m *[2][3]uint64, x uint64) uint64` on amd64: nested loops and a
labeled `continue`.

For every pointer `m` to 48 readable bytes (`Buffer`; the `2×3` array, row-major) and every
64-bit `x`, the result `RAX` is the number of rows `i ∈ {0, 1}` that contain `x` (some
`j ∈ {0, 1, 2}` has `m[i][j] = x`). `continue rows` abandons a row at its first match; the loop
counters are literals in every iteration, so the run has sixteen paths (four ways to end each
row). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- Row `i` of the `n×3` array at `m` (in memory `mem`) contains `x`. -/
def rowHas (mem : Memory) (m : Nat) (x : Nat) (i : Nat) : Bool :=
  (List.range 3).any fun j => mem.readLE (m + 8 * (3 * i + j)) 8 == x

set_option maxHeartbeats 1000000 in
theorem correctness (m x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [m, x]
      (fun s => StackWritable s 0 8 ∧ Buffer s m 48 false)
      (fun s s' => (s'.regs 0).toNat = ((List.range 2).filter (rowHas s.mem m.toNat x.toNat)).length) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hpw, hp⟩⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  all_goals
    simp only [rowHas, List.range, List.range.loop, List.any_cons, List.any_nil, List.filter_cons,
      List.filter_nil, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.mul_zero, Bool.or_false]
    simp only [Bool.or_eq_true, beq_iff_eq]
    repeat' split
    all_goals (try simp only [List.length_cons, List.length_nil, true_or, or_true,
      not_true_eq_false] at *)
    all_goals (try simp only [show 24 + m.toNat = m.toNat + 24 from Nat.add_comm _ _,
      Nat.add_assoc, Nat.reduceAdd] at *)
    all_goals janus64_arith

end Proof
