import Extracted

/-!
# `Add128(xh, xl, yh, yl uint64) (hi, lo uint64)` is 128-bit addition

**Guarantee.** For all 64-bit `xh, xl, yh, yl` and every Go call state of
`example.com/basic.Add128` with the arguments in `X0`–`X3`, the compiled code (an `adds`/`adcs`
carry chain) returns, obeys the ABI, and the results `hi = X0`, `lo = X1` satisfy
`hi·2^64 + lo = (X + Y) mod 2^128` where `X = xh·2^64 + xl` and `Y = yh·2^64 + yl`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (xh xl yh yl : BitVec 64) :
    Ensures Extracted.program Extracted.entry [xh, xl, yh, yl] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat * 2 ^ 64 + (s'.regs 1).toNat =
        ((xh.toNat * 2 ^ 64 + xl.toNat) + (yh.toNat * 2 ^ 64 + yl.toNat)) % 2 ^ 128) := by
  intro s hs _
  janus_intro hs
  janus_run
  janus_arith

end Proof
