import Extracted

/-!
# `Max(x, y uint64) uint64` returns the larger argument

**Guarantee.** For all 64-bit `x`, `y` and every Go call state of `example.com/basic.Max` with
`x` in `X0` and `y` in `X1` (everything else arbitrary), the compiled code returns (never faulting or panicking), obeys the
ABI (`SP`, `X18`, `X28`, `X29` restored), and `X0` holds `x` if `x > y` (unsigned) and `y`
otherwise. Both sides of the compiled branch (`cmp x1, x0; b.cs`) are covered.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega

end Proof
