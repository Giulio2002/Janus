import Extracted

/-!
# `Get(xs []uint64, i int) uint64` returns `xs[i]` in bounds and panics out of bounds

**Guarantee.** For every slice header `(ptr, len, cap)` in `X0`–`X2`, index `i` in `X3`, every
admissible return address `ret` (`RetAddr`) and every Go call state `s` of
`example.com/basic.Get` returning to `ret` in which the stack-growth prologue falls through
(`GuardOK s 0`) and `SP` is aligned with `[SP-24, SP+16)` writable (`StackOK s 24 16`: the frame
below `SP` and the spill slot of `xs.ptr` above it):

* if `i < len` (as unsigned 64-bit numbers, which is what the compiled `cmp; b.cs` checks), the
  `8·len` bytes at `ptr` are readable and do not overlap that stack window, then the call
  returns to `ret`, obeys the ABI, and `X0` is the 64-bit little-endian word at `ptr + 8·i` in
  the memory **before** the call (so it never faults or panics);
* if `len ≤ i` (unsigned, so this includes negative `i`), the call reaches the bounds-check panic
  stub `runtime.panicBounds`, whatever the buffer.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (ptr len cap i : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 16) :
    (i.toNat < len.toNat → Ptr s.mem ptr (8 * len.toNat) false →
      Disjoint ptr.toNat (8 * len.toNat) (s.sp.toNat - 24) 40 →
      Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = s.mem.readLE (ptr.toNat + 8 * i.toNat) 8)) ∧
    (len.toNat ≤ i.toNat → Panics (Extracted.program.withExit ret) s) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  constructor
  · intro hi ⟨hp, hp'⟩ hd
    simp only [Disjoint] at hd
    janus_run
  · intro hi
    janus_run

namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (4) else if i = 2 then (4) else if i = 3 then (1) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (4 : BitVec 64), (4 : BitVec 64), (1 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem hg : GuardOK s0 0 := by
  simp only [Janus.Spec.GuardOK, s0, wmem, wbytes, sp0, g0, hp]
  decide

theorem hst : StackOK s0 24 16 := by
  simp only [Janus.Spec.StackOK, s0, wmem, wbytes, sp0, g0, hp]
  decide

theorem hgd : Janus.Spec.Disjoint ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 24) 40 := by
  simp only [Janus.Spec.Disjoint, s0, sp0, g0]
  decide

theorem hptr : Ptr s0.mem (0x300000 : BitVec 64) (8 * (4 : BitVec 64).toNat) false := by
  simp only [Janus.Spec.Ptr, s0, wmem, wbytes, sp0, g0, hp]
  decide

theorem hdj : Disjoint (0x300000 : BitVec 64).toNat (8 * (4 : BitVec 64).toNat) (s0.sp.toNat - 24) 40 := by
  simp only [Janus.Spec.Disjoint, s0, sp0, g0, hp]
  decide

def s1 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (4) else if i = 2 then (4) else if i = 3 then (5) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup1 : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (4 : BitVec 64), (4 : BitVec 64), (5 : BitVec 64)] s1 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem hg1 : GuardOK s1 0 := by
  simp only [Janus.Spec.GuardOK, s1, wmem, wbytes, sp0, g0, hp]
  decide

theorem hst1 : StackOK s1 24 16 := by
  simp only [Janus.Spec.StackOK, s1, wmem, wbytes, sp0, g0, hp]
  decide

/-- All hypotheses of `correctness` hold together at a concrete call (the returning conjunct fires). -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (ptr len cap i : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i] s ∧ GuardOK s 0 ∧ StackOK s 24 16 ∧
    i.toNat < len.toNat ∧ Ptr s.mem ptr (8 * len.toNat) false ∧ Disjoint ptr.toNat (8 * len.toNat) (s.sp.toNat - 24) 40 ∧
    Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧
      (s'.regs 0).toNat = s.mem.readLE (ptr.toNat + 8 * i.toNat) 8) ∧
    (∃ (ptr2 len2 cap2 i2 : BitVec 64) (s2 : State), CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr2, len2, cap2, i2] s2 ∧ GuardOK s2 0 ∧ StackOK s2 24 16 ∧ len2.toNat ≤ i2.toNat ∧ Panics (Extracted.program.withExit ret) s2) :=
  ⟨ret, s0, (0x300000), (4), (4), (1), hret, setup, hg, hst, (by decide), hptr, hdj,
    (correctness 0x300000 4 4 1 ret hret s0 setup hg hst).1 (by decide) hptr hdj,
    ⟨(0x300000), (4), (4), (5), s1, setup1, hg1, hst1, (by decide), (correctness 0x300000 4 4 5 ret hret s1 setup1 hg1 hst1).2 (by decide)⟩⟩

end Witness

end Proof
