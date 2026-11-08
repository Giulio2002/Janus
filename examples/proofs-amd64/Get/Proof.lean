import Janus
import Extracted

/-! `example.com/basic.Get(xs []uint64, i int)` on amd64: `xs[i]` when `i < len(xs)` (unsigned), a bounds panic otherwise. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- In bounds: the element at index `i` is returned. The slice must not overlap the frame
slots the function writes (`[RSP-8, RSP+16)`: saved `RBP`, return address, spilled pointer). -/
theorem correctness (ptr len cap i : BitVec 64) (hi : i.toNat < len.toNat) :
    Ensures Extracted.program Extracted.entry [ptr, len, cap, i]
      (fun s => StackWritable s 8 16 ∧ Buffer s ptr (8 * len.toNat) false ∧
        Disjoint ptr (8 * len.toNat) (s.regs regSP - 8) 24)
      (fun s s' => results 1 s' = [BitVec.ofNat 64 (valueAt s (ptr + 8 * i) 8)]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨hle, hnw, hacc⟩, ⟨hbw, hb⟩, hd⟩ := hpre
  simp only [regSP] at hacc hle hnw hd
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  simp only [Disjoint, BitVec.toNat_sub, h8] at hd
  have hd' : ptr.toNat + 8 * len.toNat ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 16 ≤ ptr.toNat := by
    have := (s.regs 4).isLt; omega
  clear hd
  have hidx : (ptr + 8 * i).toNat = ptr.toNat + i.toNat * 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, h8]; omega
  simp only [valueAt, hidx]
  janus64_run

/-- Out of bounds (unsigned `i ≥ len`): `runtime.panicBounds`. -/
theorem panics (ptr len cap i : BitVec 64) (hi : len.toNat ≤ i.toNat) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i] s)
    (hpre : StackWritable s 16 16) : Panics (Extracted.program.withExit ret) s := by
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hpre
  simp only [regSP] at hacc hle hnw
  janus64_run

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def ptr : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def len : BitVec 64 := 3#64
def cap : BitVec 64 := 4#64
def i : BitVec 64 := 1#64
theorem hi : i.toNat < len.toNat := by decide

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then ptr else if r_ = 3 then len else if r_ = 1 then cap else if r_ = 7 then i else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 8 16 ∧ Buffer s ptr (8 * len.toNat) false ∧
        Disjoint ptr (8 * len.toNat) (s.regs regSP - 8) 24) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (ptr : BitVec 64) (len : BitVec 64) (cap : BitVec 64) (i : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i] s ∧ (i.toNat < len.toNat) ∧ (StackWritable s 8 16 ∧ Buffer s ptr (8 * len.toNat) false ∧
        Disjoint ptr (8 * len.toNat) (s.regs regSP - 8) 24) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ results 1 s' = [BitVec.ofNat 64 (valueAt s (ptr + 8 * i) 8)]) :=
  ⟨ret, s0, ptr, len, cap, i, hret, setup, hi, hpre, correctness ptr len cap i hi ret hret s0 setup hpre⟩

def iP : BitVec 64 := 3#64
theorem hiP : len.toNat ≤ iP.toNat := by decide
def sP : State :=
  { regs := fun r_ => if r_ = 0 then ptr else if r_ = 3 then len else if r_ = 1 then cap else if r_ = 7 then iP else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setupP : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, iP] sP :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩
theorem hpreP : (fun s => StackWritable s 16 16) sP := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)


/-- All hypotheses of `panics` hold together, and the call panics. -/
theorem panics : ∃ (ret : Nat) (s : State) (ptr len cap i : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i] s ∧ (len.toNat ≤ i.toNat) ∧ (StackWritable s 16 16) ∧
    Panics (Extracted.program.withExit ret) s :=
  ⟨ret, sP, ptr, len, cap, iP, hret, setupP, hiP, hpreP, Proof.panics ptr len cap iP hiP ret hret sP setupP hpreP⟩

end Witness

end Proof
