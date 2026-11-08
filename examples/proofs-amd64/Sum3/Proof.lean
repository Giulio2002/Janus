import Janus
import Extracted

/-! `example.com/basic.Sum3(a, b, c uint64) uint64` on amd64: a variadic call.

For every call state whose stack-growth check falls through (`StackGuardOK s 0`) with
`[RSP-64, RSP+8)` writable and the guard word outside it, the call returns `a + b + c mod 2^64`.
`sumv(a, b, c)` receives its variadic arguments as a slice: `Sum3` stores them in a
`[3]uint64` in its own frame (no allocation) and passes `(&arr, 3, 3)` in `RAX`, `RBX`, `RCX`;
`sumv`'s `range` loop over it has the literal length 3, so the run executes it. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (a b c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, c]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 64 8 ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 64))
      (fun _ s' => (s'.regs 0).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨hg, ⟨hle, hnw, hacc⟩, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run
  omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def a : BitVec 64 := 1#64
def b : BitVec 64 := 2#64
def c : BitVec 64 := 3#64

def s0 : State :=
  { regs := fun i => if i = 0 then a else if i = 3 then b else if i = 1 then c else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b, c] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackGuardOK s 0 ∧ StackWritable s 64 8 ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 64)) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (a : BitVec 64) (b : BitVec 64) (c : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b, c] s ∧ (StackGuardOK s 0 ∧ StackWritable s 64 8 ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 64)) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (s'.regs 0).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64) :=
  ⟨ret, s0, a, b, c, hret, setup, hpre, correctness a b c ret hret s0 setup hpre⟩

end Witness

end Proof
