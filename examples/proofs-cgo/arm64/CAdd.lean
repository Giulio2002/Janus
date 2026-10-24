import Extracted

/-!
# `uint64_t c_add(uint64_t a, uint64_t b)` (C, arm64): returns `a + b`

**Guarantee.** For all 64-bit `a` and `b`, every AAPCS64 call of the gcc-compiled `c_add` (any
admissible return address in `X30`, `SP` 16-byte aligned; every other register, the flags and
memory arbitrary) returns after finitely many steps without faulting, restores `SP` and the
callee-saved registers `X19`–`X29` (`CReturn`), and leaves `(a + b) mod 2^64` in `X0`.

The code is `add x0, x0, x1; ret`, copied from the cgo example binary.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic

namespace Proof

theorem correctness (a b : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [a, b] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (a.toNat + b.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs.call
  janus_run

end Proof
