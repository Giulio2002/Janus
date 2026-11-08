import Janus
import Extracted

/-! `example.com/basic.HashTwice(h, x)` on amd64: `ApplyTwice(h.Hash, x)`, a method value called
twice through `CALL CX` with the funcval in `DX`.

For every call state whose stack-growth checks fall through (`StackGuardOK s 72`, the deepest
check is in the wrapper `(*MulHasher).Hash-fm`), with `[RSP-104, RSP+8)` writable, the guard word
and the receiver's field `K` (8 bytes at `h`) readable outside it, the call returns `x · K · K`.

`HashTwice` stores the funcval (the address of `Hash-fm`, then `h`) in its own frame, so the
dynamic call target is read back from that store: no hypothesis about it is needed. The
extractor copies `Hash-fm` because `HashTwice` computes its address. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (h x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [h, x]
      (fun s => Buffer s h 8 false ∧ StackGuardOK s 72 ∧ StackWritable s 104 8 ∧
        ((s.regs 4).toNat + 8 ≤ h.toNat ∨ h.toNat + 8 ≤ (s.regs 4).toNat - 104) ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 104))
      (fun s s' => s'.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8) *
        BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) := by
  intro ret hret s hs ⟨⟨hhb, hh⟩, hg, ⟨hle, hnw, hacc⟩, hd, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run
  generalize BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem h.toNat 8) = k
  rw [BitVec.mul_comm k x, BitVec.mul_comm k]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def h : BitVec 64 := 0x30800#64
def x : BitVec 64 := 3#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then h else if r_ = 3 then x else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [h, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => Buffer s h 8 false ∧ StackGuardOK s 72 ∧ StackWritable s 104 8 ∧
        ((s.regs 4).toNat + 8 ≤ h.toNat ∨ h.toNat + 8 ≤ (s.regs 4).toNat - 104) ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 104)) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (h : BitVec 64) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [h, x] s ∧ (Buffer s h 8 false ∧ StackGuardOK s 72 ∧ StackWritable s 104 8 ∧
        ((s.regs 4).toNat + 8 ≤ h.toNat ∨ h.toNat + 8 ≤ (s.regs 4).toNat - 104) ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 104)) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ s'.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8) *
        BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) :=
  ⟨ret, s0, h, x, hret, setup, hpre, correctness h x ret hret s0 setup hpre⟩

end Witness

end Proof
