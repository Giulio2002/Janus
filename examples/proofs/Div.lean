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

namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then (100) else if i = 1 then (7)  else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(100 : BitVec 64), (7 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hg : GuardOK s0 0 := by
  simp only [Janus.Spec.GuardOK, s0, wmem, wbytes, sp0, g0, hp]
  decide

theorem hst : StackOK s0 24 0 := by
  simp only [Janus.Spec.StackOK, s0, wmem, wbytes, sp0, g0, hp]
  decide

def s1 : State :=
  { regs := fun i => if i = 0 then (100) else if i = 1 then (0) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup1 : CallSetup (Extracted.program.withExit ret) Extracted.entry [(100 : BitVec 64), (0 : BitVec 64)] s1 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hg1 : GuardOK s1 0 := by
  simp only [Janus.Spec.GuardOK, s1, wmem, wbytes, sp0, g0, hp]
  decide

theorem hst1 : StackOK s1 24 0 := by
  simp only [Janus.Spec.StackOK, s1, wmem, wbytes, sp0, g0, hp]
  decide

/-- All hypotheses of `correctness` hold together at a concrete call (the returning conjunct fires). -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ GuardOK s 0 ∧ StackOK s 24 0 ∧ y ≠ 0 ∧
    Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat = x.toNat / y.toNat) ∧
    (∃ (x2 y2 : BitVec 64) (s2 : State), CallSetup (Extracted.program.withExit ret) Extracted.entry [x2, y2] s2 ∧ GuardOK s2 0 ∧ StackOK s2 24 0 ∧ y2 = 0 ∧ Panics (Extracted.program.withExit ret) s2) :=
  ⟨ret, s0, (100), (7), hret, setup, hg, hst, (by decide), (correctness 100 7 ret hret s0 setup hg hst).2 (by decide),
    ⟨(100), (0), s1, setup1, hg1, hst1 , rfl, (correctness 100 0 ret hret s1 setup1 hg1 hst1).1.2 rfl⟩⟩

end Witness

end Proof
