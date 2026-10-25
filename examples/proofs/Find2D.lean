import Extracted

/-!
# `Find2D(m *[3][3]uint64, x uint64) uint64`: nested loops left by a labeled `break`

**Guarantee.** For every pointer `m` to 72 readable bytes (`Ptr`; the `3×3` array, row-major)
and every 64-bit `x`, and every Go call state of `example.com/basic.Find2D`, the call returns
(never faulting or panicking), obeys the ABI, and `r = X0` is the row-major index `3i + j` of
the first element of `m` equal to `x`, or `9` if there is none: `r ≤ 9`, no element before
position `r` equals `x`, and if `r < 9` the element at position `r` does.

`break outer` jumps from the inner loop past the end of the outer one. Both loops have constant
trip counts, so the counters are literals in every iteration and `janus_run` executes them; the
search has one path per position at which it can stop (ten in all).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (m x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [m, x] (fun s => Ptr s.mem m 72 false)
      (fun s s' => (s'.regs 0).toNat ≤ 9 ∧
        (∀ j < (s'.regs 0).toNat, s.mem.readLE (m.toNat + 8 * j) 8 ≠ x.toNat) ∧
        ((s'.regs 0).toNat < 9 → s.mem.readLE (m.toNat + 8 * (s'.regs 0).toNat) 8 = x.toNat)) := by
  intro ret hret s hs ⟨hp, hp'⟩
  janus_intro hs
  janus_run
  all_goals try refine ⟨?_, fun h => h.elim⟩
  all_goals
    intro j hj
    janus_cases hj
    all_goals (try simp only [Nat.reduceMul, Nat.add_zero]) <;> omega

end Proof
