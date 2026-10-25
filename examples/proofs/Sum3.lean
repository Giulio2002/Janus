import Extracted

/-!
# `Sum3(a, b, c uint64) uint64`: a variadic call

**Guarantee.** For all 64-bit `a`, `b`, `c` and every Go call state `s` of
`example.com/basic.Sum3` whose stack-growth prologue falls through (`GuardOK s 0`, the guard
word outside the stack window) and whose `SP` is aligned with `[SP-80, SP)` writable, the call
returns (never faulting or panicking), obeys the ABI, and `X0 = a + b + c mod 2^64`.

**What is exercised.** `sumv(a, b, c)` passes the variadic arguments as a slice: the compiler
stores `a`, `b`, `c` in a `[3]uint64` in `Sum3`'s frame (it does not escape, so no allocation)
and passes `(&arr, 3, 3)` in `X0`–`X2`. `sumv` is an ordinary `range` loop over that slice; with
the literal length 3 the executor runs it to the end.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (a b c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, c]
      (fun s => GuardOK s 0 ∧ StackOK s 80 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 80) 80)
      (fun _ s' => (s'.regs 0).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hgd
  janus_run
  janus_arith

end Proof
