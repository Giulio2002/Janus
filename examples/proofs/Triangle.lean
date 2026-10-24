import Extracted

/-!
# `Triangle(n uint64) uint64`: an expression switch with `fallthrough`, compiled to a jump table

**Guarantee.** For every 64-bit `n` and every Go call state of `example.com/basic.Triangle` whose
memory holds the function's read-only jump table (`DataLoaded`), the call returns (never faulting
or panicking), obeys the ABI, and `X0` is the triangular number `n·(n+1)/2 = 0 + 1 + … + n` when
`n ≤ 8`, and `0` otherwise.

The nine dense cases become a bounds check (`cmp x0, #8; b.hi default`) and an indirect jump
through a table of code addresses in `.rodata` (`ldr x27, [x1, x0, lsl #3]; br x27`). The
`fallthrough` chain becomes straight-line code that each case enters at a different point. The
proof splits on the nine in-range values, for each of which the jump target is read from the
extracted table.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n]
      (fun s => Extracted.program.DataLoaded s.mem)
      (fun _ s' => (s'.regs 0).toNat = if n.toNat ≤ 8 then n.toNat * (n.toNat + 1) / 2 else 0) := by
  intro ret hret s hs hd
  janus_intro hs
  janus_data hd
  by_cases hn : n.toNat ≤ 8
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 9 ∧ n = BitVec.ofNat 64 k :=
      ⟨n.toNat, by omega, by simp⟩
    janus_cases hk
    all_goals janus_run
  · janus_run
    simp [hn]

end Proof
