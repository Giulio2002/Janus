import Extracted

/-!
# `MustNonNeg(x int64) int64`: returns `x`, or ends in a breakpoint trap (arm64)

```go
func MustNonNeg(x int64) int64 {
	if x < 0 {
		runtime.Breakpoint()
	}
	return x
}
```

`runtime.Breakpoint` calls `runtime.breakpoint` (assembly: `BRK #0`), so the negative path of
the function ends in a trap: the extractor puts a `.trap` stub on the `BRK`, and `traps` proves
that every run from a call with a negative `x` reaches it (`Janus.Kernel.Traps`, which checks
that the word there is a trap instruction: executed, it faults with `Fault.trap pc 5`, the
`SIGTRAP` Linux delivers).

**Guarantees.** For every call state of `example.com/sys.MustNonNeg` whose stack-growth check
falls through (`GuardOK s 0`) with the 24 bytes below `SP` and the 16 above writable
(`StackOK s 24 16`: its frame and the spill slot of `x`):

* `correctness`: if `0 ≤ x` (as a signed 64-bit integer) the call returns `x` in `X0`;
* `traps`: if `x < 0` the run ends in the breakpoint trap.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Kernel

namespace Proof

theorem lsb63_of_nonneg (x : BitVec 64) (hx : 0 ≤ x.toInt) : x.getLsbD 63 = false := by
  have h : x.toNat < 2 ^ 63 := by
    rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h | h
    · exact h
    · exact absurd ((BitVec.toInt_neg_iff (x := x)).mpr (by omega)) (by omega)
  simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have : x.toNat / 2 ^ 63 = 0 := by omega
  simp [this]

theorem lsb63_of_neg (x : BitVec 64) (hx : x.toInt < 0) : x.getLsbD 63 = true := by
  have h : 2 ^ 63 ≤ x.toNat := by have := (BitVec.toInt_neg_iff (x := x)).mp hx; omega
  have h2 := x.isLt
  simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have : x.toNat / 2 ^ 63 = 1 := by omega
  simp [this]

theorem correctness (x : BitVec 64) (hx : 0 ≤ x.toInt) :
    Ensures Extracted.program Extracted.entry [x] (fun s => GuardOK s 0 ∧ StackOK s 24 16)
      (fun _ s' => s'.regs 0 = x) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩⟩
  have h63 := lsb63_of_nonneg x hx
  janus_intro hs
  janus_run [h63]

theorem traps (x : BitVec 64) (hx : x.toInt < 0) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 16) :
    Traps (Extracted.program.withExit ret) s := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  have h63 := lsb63_of_neg x hx
  janus_intro hs
  unfold Traps
  janus_run [h63]
  rw [trapAt_withExit]
  decide

end Proof
