import Extracted

/-!
# `Div(x, y uint64) uint64` panics exactly when `y = 0`, and otherwise returns `x / y`

**Guarantee.** For all 64-bit `x`, `y`, every admissible return address `ret` (`RetAddr`:
4-aligned, below `2^48`, outside the extracted code and stubs) and every Go call state `s` of
`example.com/basic.Div` returning to `ret` (`x` in `X0`, `y` in `X1`, `ret` in `X30`) in which
* the stack-growth prologue falls through (`g.stackguard0`, read through `X28`, is readable and
  below `SP`; `GuardOK s 0`), and
* `SP` is 16-byte aligned with the 24 bytes below it writable (the 16-byte frame and the saved
  frame pointer; `StackOK s 24 0`),

the call reaches the Go panic stub (`runtime.panicdivide`) **if and only if** `y = 0`, and when
`y ≠ 0` it returns to `ret` (never faulting or panicking), obeys the ABI (including restoring
`X29` from the stack) and `X0 = ⌊x / y⌋`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (x y : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 0) :
    (Panics (Extracted.program.withExit ret) s ↔ y = 0) ∧
    (y ≠ 0 → Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧
      (s'.regs 0).toNat = x.toNat / y.toNat)) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  have hok : y ≠ 0 → Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧
      (s'.regs 0).toNat = x.toNat / y.toNat) := by
    intro hy
    have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq h)
    janus_run [hy']
  have hpan : y = 0 → Panics (Extracted.program.withExit ret) s := by
    intro hy
    subst hy
    janus_run
  refine ⟨⟨fun hp => ?_, hpan⟩, hok⟩
  by_cases hy : y = 0
  · exact hy
  · exact absurd hp (hok hy).not_panics

end Proof
