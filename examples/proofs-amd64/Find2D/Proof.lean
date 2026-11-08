import Janus
import Extracted

/-! `example.com/basic.Find2D(m *[3][3]uint64, x uint64) uint64` on amd64: nested loops left by a
labeled `break`.

For every pointer `m` to 72 readable bytes (`Buffer`; the `3×3` array, row-major) and every
64-bit `x`, the result `r = RAX` is the row-major index `3i + j` of the first element of `m`
equal to `x`, or `9` if there is none: `r ≤ 9`, no element before position `r` equals `x`, and
if `r < 9` the element at position `r` does. `break outer` jumps past the end of the outer loop;
the loop counters are literals in every iteration, so the run has one path per position at
which the search can stop. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (m x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [m, x]
      (fun s => StackWritable s 0 8 ∧ Buffer s m 72 false)
      (fun s s' => (s'.regs 0).toNat ≤ 9 ∧
        (∀ j < (s'.regs 0).toNat, s.mem.readLE (m.toNat + 8 * j) 8 ≠ x.toNat) ∧
        ((s'.regs 0).toNat < 9 → s.mem.readLE (m.toNat + 8 * (s'.regs 0).toNat) 8 = x.toNat)) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hpw, hp⟩⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | exact fun h => h.elim
    | (intro j hj
       janus64_cases hj
       all_goals (try simp only [Nat.reduceMul, Nat.add_zero]) <;> janus64_arith)
    | janus64_arith

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def m : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def x : BitVec 64 := 7#64

def s0 : State :=
  { regs := fun i => if i = 0 then m else if i = 3 then x else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [m, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ Buffer s m 72 false) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (m : BitVec 64) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [m, x] s ∧ (StackWritable s 0 8 ∧ Buffer s m 72 false) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (s'.regs 0).toNat ≤ 9 ∧
        (∀ j < (s'.regs 0).toNat, s.mem.readLE (m.toNat + 8 * j) 8 ≠ x.toNat) ∧
        ((s'.regs 0).toNat < 9 → s.mem.readLE (m.toNat + 8 * (s'.regs 0).toNat) 8 = x.toNat)) :=
  ⟨ret, s0, m, x, hret, setup, hpre, correctness m x ret hret s0 setup hpre⟩

end Witness

end Proof
