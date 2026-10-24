import Janus
import Extracted

/-! `example.com/basic.Slice2(xs []uint64, i, j int) []uint64` on amd64: the slice expression
`xs[i:j]`.

For a slice header `(ptr, len, cap)` with `cap < 2^63` and `[RSP-16, RSP+16)` writable (the saved
frame pointer, the panic call's return address, the return address and the spill slot of `ptr`):
* `correctness`: when Go's condition `0 ≤ i ≤ j ≤ cap` on the signed `int`s holds (`InRange`;
  the bound is the capacity), the call returns the slice `(ptr + 8·i, j - i, cap - i)` in `RAX`,
  `RBX`, `RCX` (with the pointer left at `ptr` when the capacity `cap - i` is `0`);
* `panics`: when it fails, the call reaches the panic stub `runtime.panicBounds`.

The code checks `j ≤ cap` and `i ≤ j` with unsigned comparisons (a negative `int` is a huge
unsigned value, `inRange_iff`) and masks the pointer adjustment `8·i` with the sign of `i - cap`
(`NEGQ`, `SARQ $63`, `ANDQ`). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

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

/-- The pointer adjustment `8·i`, masked by the sign of `i - k` (computed as `-(k - i)`). -/
theorem ptr_adj (ptr i k : BitVec 64) (hik : i.toNat ≤ k.toNat) (hk : k.toNat < 2 ^ 63) :
    ptr + (i <<< 3 &&& (0#64 - (k - i)).sshiftRight 63) =
      if i.toNat < k.toNat then ptr + 8#64 * i else ptr := by
  have e0 : (0#64 - (k - i)) = i - k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := i.isLt; have := k.isLt; omega
  rw [e0]
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

theorem correctness (ptr len cap i j : BitVec 64) (hc : cap.toNat < 2 ^ 63) :
    EnsuresResults Extracted.program Extracted.entry [ptr, len, cap, i, j] 3
      (fun s => StackWritable s 16 16 ∧ InRange i j cap)
      (fun r => r = [if i.toNat < cap.toNat then ptr + 8 * i else ptr, j - i, cap - i]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨hle, hnw, hacc⟩, h⟩ := hpre
  simp only [regSP] at hacc hle hnw
  rw [inRange_iff i j cap hc] at h
  obtain ⟨h1, h2⟩ := h
  janus64_run
  rw [ptr_adj ptr i cap (by omega) (by omega)]

theorem panics (ptr len cap i j : BitVec 64) (hc : cap.toNat < 2 ^ 63) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i, j] s)
    (hpre : StackWritable s 16 16) (h : ¬ InRange i j cap) :
    Panics (Extracted.program.withExit ret) s := by
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hpre
  simp only [regSP] at hacc hle hnw
  rw [inRange_iff i j cap hc] at h
  janus64_run

end Proof
