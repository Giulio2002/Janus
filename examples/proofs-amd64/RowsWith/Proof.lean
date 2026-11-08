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

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def m : BitVec 64 := 0x30800#64
def x : BitVec 64 := 7#64

def s0 : State :=
  { regs := fun i => if i = 0 then m else if i = 3 then x else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [m, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ Buffer s m 48 false) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (m : BitVec 64) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [m, x] s ∧ (StackWritable s 0 8 ∧ Buffer s m 48 false) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (s'.regs 0).toNat = ((List.range 2).filter (rowHas s.mem m.toNat x.toNat)).length) :=
  ⟨ret, s0, m, x, hret, setup, hpre, correctness m x ret hret s0 setup hpre⟩

end Witness

end Proof
