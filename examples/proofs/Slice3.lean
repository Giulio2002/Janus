import Extracted

/-!
# `Slice3(xs []uint64, i, j, k int) []uint64`: the full slice expression `xs[i:j:k]`

**Guarantee.** For every slice header `(ptr, len, cap)` with `cap < 2^63` (a Go capacity), all
64-bit `i`, `j`, `k`, every admissible return address `ret` and every Go call state `s` of
`example.com/basic.Slice3` whose stack-growth prologue falls through (`GuardOK s 0`, the guard
word outside the stack window) and whose `SP` is aligned with `[SP-24, SP+16)` writable (the
frame and the spill slot of `ptr` in the caller's frame):

* the call reaches the Go panic stub (`runtime.panicBounds`) **if and only if** Go's condition
  `0 ≤ i ≤ j ≤ k ≤ cap` on the signed `int`s fails (`InRange`);
* when it holds, the call returns (never faulting), obeys the ABI, and the result is the slice
  `(ptr + 8·i, j - i, k - i)` in `X0`–`X2`; when the result's capacity `k - i` is `0` the
  pointer stays `ptr`, so that it never points past the end of the array.

The compiled code checks `k ≤ cap`, `j ≤ k` and `i ≤ j` with unsigned comparisons (a negative
`int` is a huge unsigned value, so one comparison covers both bounds; `inRange_iff`), and masks
the pointer adjustment `8·i` with the sign of `i - k` (`ptr_adj`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Go's condition for `xs[i:j:k]` not to panic, on the (signed) `int` arguments. -/
def InRange (i j k cap : BitVec 64) : Prop :=
  0 ≤ i.toInt ∧ i.toInt ≤ j.toInt ∧ j.toInt ≤ k.toInt ∧ k.toInt ≤ cap.toInt

theorem inRange_iff (i j k cap : BitVec 64) (hc : cap.toNat < 2 ^ 63) :
    InRange i j k cap ↔ i.toNat ≤ j.toNat ∧ j.toNat ≤ k.toNat ∧ k.toNat ≤ cap.toNat := by
  simp only [InRange, BitVec.toInt_eq_toNat_cond]
  have := i.isLt; have := j.isLt; have := k.isLt
  by_cases hi : 2 * i.toNat < 2 ^ 64 <;> by_cases hj : 2 * j.toNat < 2 ^ 64 <;>
    by_cases hk : 2 * k.toNat < 2 ^ 64 <;> simp only [hi, hj, hk, ite_true, ite_false] <;>
    simp only [show 2 * cap.toNat < 2 ^ 64 by omega, ite_true] <;> omega

/-- The pointer adjustment: `i·8` masked by the sign of `i - k`, i.e. kept only when the result's
capacity `k - i` is positive (so a zero-capacity slice never points past the array). -/
theorem ptr_adj (ptr i k : BitVec 64) (hik : i.toNat ≤ k.toNat) (hk : k.toNat < 2 ^ 63) :
    ptr + (i &&& (i - k).sshiftRight 63) <<< 3 = if i.toNat < k.toNat then ptr + 8#64 * i else ptr := by
  split
  · rename_i h
    have hm : (i - k).sshiftRight 63 = BitVec.allOnes 64 := by
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, BitVec.toInt_allOnes]
      have e : (i - k).toInt = (i.toNat : Int) - k.toNat := by
        rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub]
        have := i.isLt; have := k.isLt
        split <;> omega
      rw [e, Int.ediv_eq_iff_of_pos (by decide)]
      simp; omega
    rw [hm, BitVec.and_allOnes]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_mul]
    simp only [BitVec.toNat_ofNat]; omega
  · rename_i h
    have : i = k := BitVec.eq_of_toNat_eq (by omega)
    subst this
    simp

theorem correctness (ptr len cap i j k : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i, j, k] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 16) (hgd : Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 24) 40)
    (hc : cap.toNat < 2 ^ 63) :
    (Panics (Extracted.program.withExit ret) s ↔ ¬ InRange i j k cap) ∧
    (InRange i j k cap → Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧
      s'.regs 0 = (if i.toNat < k.toNat then ptr + 8 * i else ptr) ∧
      s'.regs 1 = j - i ∧ s'.regs 2 = k - i)) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  simp only [Disjoint] at hgd
  janus_intro hs
  have hok : InRange i j k cap → Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧
      s'.regs 0 = (if i.toNat < k.toNat then ptr + 8 * i else ptr) ∧
      s'.regs 1 = j - i ∧ s'.regs 2 = k - i) := by
    intro h
    rw [inRange_iff i j k cap hc] at h
    obtain ⟨h1, h2, h3⟩ := h
    janus_run
    exact ptr_adj ptr i k (by omega) (by omega)
  have hpan : ¬ InRange i j k cap → Panics (Extracted.program.withExit ret) s := by
    intro h
    rw [inRange_iff i j k cap hc] at h
    janus_run
  refine ⟨⟨fun hp => ?_, hpan⟩, hok⟩
  intro h
  exact absurd hp (hok h).not_panics

namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (4) else if i = 2 then (4) else if i = 3 then (1) else if i = 4 then (3) else if i = 5 then (4) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (4 : BitVec 64), (4 : BitVec 64), (1 : BitVec 64), (3 : BitVec 64), (4 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl⟩

theorem hg : GuardOK s0 0 := by
  simp only [Janus.Spec.GuardOK, s0, wmem, wbytes, sp0, g0, hp]
  decide

theorem hst : StackOK s0 24 16 := by
  simp only [Janus.Spec.StackOK, s0, wmem, wbytes, sp0, g0, hp]
  decide

theorem hgd : Janus.Spec.Disjoint ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 24) 40 := by
  simp only [Janus.Spec.Disjoint, s0, sp0, g0]
  decide

theorem hir : InRange 1 3 4 4 := by
  unfold InRange
  decide

def s1 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (4) else if i = 2 then (4) else if i = 3 then (1) else if i = 4 then (5) else if i = 5 then (4) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup1 : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (4 : BitVec 64), (4 : BitVec 64), (1 : BitVec 64), (5 : BitVec 64), (4 : BitVec 64)] s1 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl⟩

theorem hg1 : GuardOK s1 0 := by
  simp only [Janus.Spec.GuardOK, s1, wmem, wbytes, sp0, g0, hp]
  decide

theorem hst1 : StackOK s1 24 16 := by
  simp only [Janus.Spec.StackOK, s1, wmem, wbytes, sp0, g0, hp]
  decide

theorem hgd1 : Janus.Spec.Disjoint ((s1.regs 28).toNat + 16) 8 (s1.sp.toNat - 24) 40 := by
  simp only [Janus.Spec.Disjoint, s1, sp0, g0]
  decide

theorem hnir : ¬ InRange 1 5 4 4 := by
  unfold InRange
  decide

/-- All hypotheses of `correctness` hold together at a concrete call (the returning conjunct fires). -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (ptr len cap i j k : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i, j, k] s ∧ GuardOK s 0 ∧ StackOK s 24 16 ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 24) 40 ∧ cap.toNat < 2 ^ 63 ∧ InRange i j k cap ∧
    Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ s'.regs 0 = (if i.toNat < k.toNat then ptr + 8 * i else ptr) ∧ s'.regs 1 = j - i ∧ s'.regs 2 = k - i) ∧
    (∃ (ptr2 len2 cap2 i2 j2 k2 : BitVec 64) (s2 : State), CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr2, len2, cap2, i2, j2, k2] s2 ∧ GuardOK s2 0 ∧ StackOK s2 24 16 ∧ Disjoint ((s2.regs 28).toNat + 16) 8 (s2.sp.toNat - 24) 40 ∧ cap2.toNat < 2 ^ 63 ∧ ¬ InRange i2 j2 k2 cap2 ∧ Panics (Extracted.program.withExit ret) s2) :=
  ⟨ret, s0, (0x300000), (4), (4), (1), (3), (4), hret, setup, hg, hst, hgd, (by decide), hir, (correctness 0x300000 4 4 1 3 4 ret hret s0 setup hg hst hgd (by decide)).2 hir,
    ⟨(0x300000), (4), (4), (1), (5), (4), s1, setup1, hg1, hst1, hgd1, (by decide), hnir, (correctness 0x300000 4 4 1 5 4 ret hret s1 setup1 hg1 hst1 hgd1 (by decide)).1.2 hnir⟩⟩

end Witness

end Proof
