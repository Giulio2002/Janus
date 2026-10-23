import Extracted

/-!
# `Mul64(x, y uint64) (hi, lo uint64)` is the full 128-bit product

**Guarantee.** For all 64-bit `x`, `y` and every Go call state of `example.com/basic.Mul64`
(`x` in `X0`, `y` in `X1`), the compiled code (`mul`, `umulh`) returns (never faulting or panicking), obeys the ABI, and the
results `hi = X0`, `lo = X1` satisfy `hi·2^64 + lo = x·y` exactly (no overflow is possible).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat * 2 ^ 64 + (s'.regs 1).toNat = x.toNat * y.toNat) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  janus_arith

end Proof
