import Extracted

/-!
# `IncTwice(c *Counter, d uint64) uint64`: static calls of a pointer-receiver method

**Guarantee.** For every pointer `c` to 8 writable bytes (`c.N`) outside the stack window and
every 64-bit `d`, and every Go call state `s` of `example.com/basic.IncTwice` whose stack-growth
prologue falls through (`GuardOK s 0`, the guard word outside the window) and whose `SP` is
aligned with `[SP-56, SP+24)` writable (the frame, and the spill slots of `c` and `d` in the
caller's frame), the call returns (never faulting or panicking), obeys the ABI, and with `N` the
value of `c.N` before the call: afterwards `c.N = N + 2d` and `X0 = (N + d) + (N + 2d)`, all
modulo `2^64`.

`c.Inc(d)` with `c` a pointer is a direct `bl` to `(*Counter).Inc` with the receiver in `X0`;
the second call sees the first one's store.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (c d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, d]
      (fun s => Ptr s.mem c 8 true ∧ GuardOK s 0 ∧ StackOK s 56 24 ∧
        Disjoint c.toNat 8 (s.sp.toNat - 56) 80 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 56) 80 ∧ Disjoint c.toNat 8 ((s.regs 28).toNat + 16) 8)
      (fun s s' => s'.mem.readLE c.toNat 8 = (s.mem.readLE c.toNat 8 + 2 * d.toNat) % 2 ^ 64 ∧
        (s'.regs 0).toNat = ((s.mem.readLE c.toNat 8 + d.toNat) + (s.mem.readLE c.toNat 8 + 2 * d.toNat)) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hc, hc'⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hgd, hcg⟩
  janus_intro hs
  simp only [Disjoint] at hd hgd hcg
  janus_run
  constructor <;> omega

end Proof
