import Extracted

/-!
# `Slice2(xs []uint64, i, j int) []uint64`: the slice expression `xs[i:j]`

**Guarantee.** For every slice header `(ptr, len, cap)` with `cap < 2^63` (a Go capacity), all
64-bit `i`, `j`, `k`, every admissible return address `ret` and every Go call state `s` of
`example.com/basic.Slice2` whose stack-growth prologue falls through (`GuardOK s 0`, the guard
word outside the stack window) and whose `SP` is aligned with `[SP-24, SP+16)` writable (the
frame and the spill slot of `ptr` in the caller's frame):

* the call reaches the Go panic stub (`runtime.panicBounds`) **if and only if** Go's condition
  `0 ≤ i ≤ j ≤ cap` on the signed `int`s fails (`InRange`; the bound of a slice of a slice is
  its capacity, not its length);
* when it holds, the call returns (never faulting), obeys the ABI, and the result is the slice
  `(ptr + 8·i, j - i, cap - i)` in `X0`–`X2`; when the result's capacity `cap - i` is `0` the
  pointer stays `ptr`, so that it never points past the end of the array.

The compiled code checks `j ≤ cap` and `i ≤ j` with unsigned comparisons (a negative `int` is a
huge unsigned value, so one comparison covers both bounds; `inRange_iff`), and masks the pointer
adjustment `8·i` with the sign of `i - cap` (`ptr_adj`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Go's condition for `xs[i:j]` not to panic, on the (signed) `int` arguments. -/
def InRange (i j cap : BitVec 64) : Prop :=
  0 ≤ i.toInt ∧ i.toInt ≤ j.toInt ∧ j.toInt ≤ cap.toInt

theorem inRange_iff (i j cap : BitVec 64) (hc : cap.toNat < 2 ^ 63) :
    InRange i j cap ↔ i.toNat ≤ j.toNat ∧ j.toNat ≤ cap.toNat := by
  simp only [InRange, BitVec.toInt_eq_toNat_cond]
  have := i.isLt; have := j.isLt
  by_cases hi : 2 * i.toNat < 2 ^ 64 <;> by_cases hj : 2 * j.toNat < 2 ^ 64 <;>
    simp only [hi, hj, ite_true, ite_false] <;>
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

theorem correctness (ptr len cap i j : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i, j] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 16) (hgd : Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 24) 40)
    (hc : cap.toNat < 2 ^ 63) :
    (Panics (Extracted.program.withExit ret) s ↔ ¬ InRange i j cap) ∧
    (InRange i j cap → Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧
      s'.regs 0 = (if i.toNat < cap.toNat then ptr + 8 * i else ptr) ∧
      s'.regs 1 = j - i ∧ s'.regs 2 = cap - i)) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  simp only [Disjoint] at hgd
  janus_intro hs
  have hok : InRange i j cap → Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧
      s'.regs 0 = (if i.toNat < cap.toNat then ptr + 8 * i else ptr) ∧
      s'.regs 1 = j - i ∧ s'.regs 2 = cap - i) := by
    intro h
    rw [inRange_iff i j cap hc] at h
    obtain ⟨h1, h2⟩ := h
    janus_run
    exact ptr_adj ptr i cap (by omega) (by omega)
  have hpan : ¬ InRange i j cap → Panics (Extracted.program.withExit ret) s := by
    intro h
    rw [inRange_iff i j cap hc] at h
    janus_run
  refine ⟨⟨fun hp => ?_, hpan⟩, hok⟩
  intro h
  exact absurd hp (hok h).not_panics

end Proof
