import Extracted

/-!
# `SumSquares(x, y uint64) uint64` returns `x² + y²` (mod `2^64`), calling `square` twice

**Guarantee.** For all 64-bit `x`, `y` and every Go call state `s` of
`example.com/basic.SumSquares` (`x` in `X0`, `y` in `X1`) in which the stack-growth prologue falls
through (`GuardOK s 0`) and `SP` is aligned with `[SP-40, SP+56)` writable (`StackOK s 40 56`:
its frame, the saved frame pointer, and the spill slot of `y` in the caller's frame), the call
returns (never faulting or panicking), obeys the ABI, and `X0 = (x·x + y·y) mod 2^64`.

**How.** `square` is proved once as a callee `Summary` (from any state at its entry it returns
to `X30` with `X0 := X0 · X0`), and the proof of `SumSquares` uses it at both call sites; the
spilled `y` and the first square are kept in the stack frame across the calls.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem square_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.square")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56)
      (fun s s' => s' = { s with regs := setReg s.regs 0 (s.regs 0 * s.regs 0),
                                 pc := s.regs 30 }) := by
  intro s hpc ⟨h1, h2⟩
  janus_run

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y]
      (fun s => GuardOK s 0 ∧ StackOK s 40 56)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat * x.toNat + y.toNat * y.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hal, hb, ha, hw⟩
  janus_intro hs
  janus_run calls [square_summary]
  janus_arith

end Proof
