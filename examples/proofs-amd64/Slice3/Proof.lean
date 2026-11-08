import Janus
import Extracted

/-! `example.com/basic.Slice3(xs []uint64, i, j, k int) []uint64` on amd64: the full slice
expression `xs[i:j:k]`.

For a slice header `(ptr, len, cap)` with `cap < 2^63` and `[RSP-16, RSP+16)` writable (the saved
frame pointer, the panic call's return address, the return address and the spill slot of `ptr`):
* `correctness`: when Go's condition `0 ≤ i ≤ j ≤ k ≤ cap` on the signed `int`s holds
  (`InRange`), the call returns the slice `(ptr + 8·i, j - i, k - i)` in `RAX`, `RBX`, `RCX`
  (with the pointer left at `ptr` when the capacity `k - i` is `0`);
* `panics`: when it fails, the call reaches the panic stub `runtime.panicBounds`.

The code checks `k ≤ cap`, `j ≤ k`, `i ≤ j` with unsigned comparisons (`JB`; a negative `int`
is a huge unsigned value, `inRange_iff`) and masks the pointer adjustment `8·i` with the sign of
`i - k` (`NEGQ`, `SARQ $63`, `ANDQ`). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

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

theorem correctness (ptr len cap i j k : BitVec 64) (hc : cap.toNat < 2 ^ 63) :
    EnsuresResults Extracted.program Extracted.entry [ptr, len, cap, i, j, k] 3
      (fun s => StackWritable s 16 16 ∧ InRange i j k cap)
      (fun r => r = [if i.toNat < k.toNat then ptr + 8 * i else ptr, j - i, k - i]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨hle, hnw, hacc⟩, h⟩ := hpre
  simp only [regSP] at hacc hle hnw
  rw [inRange_iff i j k cap hc] at h
  obtain ⟨h1, h2, h3⟩ := h
  janus64_run
  rw [ptr_adj ptr i k (by omega) (by omega)]

theorem panics (ptr len cap i j k : BitVec 64) (hc : cap.toNat < 2 ^ 63) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i, j, k] s)
    (hpre : StackWritable s 16 16) (h : ¬ InRange i j k cap) :
    Panics (Extracted.program.withExit ret) s := by
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hpre
  simp only [regSP] at hacc hle hnw
  rw [inRange_iff i j k cap hc] at h
  janus64_run

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def ptr : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def len : BitVec 64 := 4#64
def cap : BitVec 64 := 8#64
def i : BitVec 64 := 1#64
def j : BitVec 64 := 3#64
def k : BitVec 64 := 6#64
theorem hc : cap.toNat < 2 ^ 63 := by decide

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then ptr else if r_ = 3 then len else if r_ = 1 then cap else if r_ = 7 then i else if r_ = 6 then j else if r_ = 8 then k else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i, j, k] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 16 16 ∧ InRange i j k cap) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (ptr : BitVec 64) (len : BitVec 64) (cap : BitVec 64) (i : BitVec 64) (j : BitVec 64) (k : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i, j, k] s ∧ (cap.toNat < 2 ^ 63) ∧ (StackWritable s 16 16 ∧ InRange i j k cap) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (results 3 s') = [if i.toNat < k.toNat then ptr + 8 * i else ptr, j - i, k - i]) :=
  ⟨ret, s0, ptr, len, cap, i, j, k, hret, setup, hc, hpre, correctness ptr len cap i j k hc ret hret s0 setup hpre⟩

end Witness

end Proof
