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

end Proof
