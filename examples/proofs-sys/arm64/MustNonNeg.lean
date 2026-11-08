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

namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000

def wmem : Memory := ⟨fun _ => 0, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then 5 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(5 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by intro i h; simp only [List.length_cons, List.length_nil] at h
                rcases (by omega : i = 0) with rfl; rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 24 16 := by
  simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, s0, wmem, sp0, g0]
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩⟩

/-- All the hypotheses of `correctness` hold together at a concrete call, and it returns `x`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ 0 ≤ x.toInt ∧
    (GuardOK s 0 ∧ StackOK s 24 16) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ s'.regs 0 = x) :=
  ⟨ret, s0, 5, hret, setup, by decide, hpre, correctness 5 (by decide) ret hret s0 setup hpre⟩

def sT : State :=
  { regs := fun i => if i = 0 then 0xFFFFFFFFFFFFFFFF else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }


theorem setupT : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0xFFFFFFFFFFFFFFFF : BitVec 64)] sT :=
  ⟨rfl, rfl, by intro i h; simp only [List.length_cons, List.length_nil] at h
                rcases (by omega : i = 0) with rfl; rfl⟩

theorem hpreT : GuardOK sT 0 ∧ StackOK sT 24 16 := by
  simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, sT, wmem, sp0, g0]
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩⟩


/-- All the hypotheses of `traps` hold together at a concrete call with a negative `x`, and the call traps. -/
theorem traps : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ x.toInt < 0 ∧
    (GuardOK s 0 ∧ StackOK s 24 16) ∧
    Traps (Extracted.program.withExit ret) s :=
  ⟨ret, sT, 0xFFFFFFFFFFFFFFFF, hret, setupT, by decide, hpreT, Proof.traps 0xFFFFFFFFFFFFFFFF (by decide) ret hret sT setupT hpreT.1 hpreT.2⟩

end Witness

end Proof
