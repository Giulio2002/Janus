import Extracted

/-!
# `DeferAdd(x, y uint64) (r uint64)` returns `x + y` through an open-coded `defer`

**Guarantee.** For all `x`, `y` and every Go call state `s` of `example.com/basic.DeferAdd` in
which the stack-growth prologue falls through and `[SP-72, SP)` is writable with `SP` aligned,
the call returns, obeys the ABI, and `X0 = (x + y) mod 2^64`: the function sets `r = x`, and the
deferred closure (which captured `&r` and `y`) runs at the exit and adds `y` to `r` before it is
returned.

**How.** Go 1.26 open-codes this defer: the closure's funcval lives in the frame (with a
`deferBits` byte, which the panic path consults), and the exit clears the byte and calls the
closure with `BLR` (context `X26` = the funcval).
The closure is built by the code being proved, so the call target is read back from the stack
and no hypothesis is needed; `janus_run` executes the closure inline. The function also contains
`bl runtime.deferreturn`, reached only when a panic is recovered (out of scope, see
docs/SOUNDNESS.md): the extractor does not copy it (`omittedCalls` in `identity.json`), and the
theorem shows it is not reached.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun s => GuardOK s 0 ∧ StackOK s 72 0)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hal, hb, ha, hw⟩
  janus_intro hs
  janus_run

end Proof
