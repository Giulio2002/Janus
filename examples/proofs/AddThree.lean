import Extracted

/-!
# `AddThree(x, y, z uint64) uint64` returns `x + y + z`, by composing two calls to `Add`

**Guarantee.** For all 64-bit `x`, `y`, `z` and every Go call state `s` of
`example.com/basic.AddThree` (arguments in `X0`–`X2`) in which the stack-growth prologue falls
through (`GuardOK s 0`) and `SP` is aligned with `[SP-40, SP+32)` writable (`StackOK s 40 32`:
its 32-byte frame, the saved frame pointer, and the spill slot of `z` in the caller's frame),
the call returns (never faulting or panicking), obeys the ABI, and `X0 = (x + y + z) mod 2^64`.

**How.** The callee `Add` (extracted with `AddThree`) is proved once, from *any* state at its
entry, as a `Summary`: it returns to `X30` with `X0 := X0 + X1` and nothing else changed. The
proof of `AddThree` executes its own instructions and uses that summary at both `bl Add`s; the
callee's code is not re-executed.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- `Add` as a callee: from any state at its entry with a well-formed return address in `X30`
(4-aligned, below the top-byte range), it returns there with `X0 = X0 + X1`. -/
theorem add_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.Add")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56)
      (fun s s' => s' = { s with regs := setReg s.regs 0 (s.regs 0 + s.regs 1),
                                 pc := s.regs 30 }) := by
  intro s hpc ⟨h1, h2⟩
  janus_run

theorem correctness (x y z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y, z]
      (fun s => GuardOK s 0 ∧ StackOK s 40 32)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat + z.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hal, hb, ha, hw⟩
  janus_intro hs
  janus_run calls [add_summary]
  janus_arith

end Proof
