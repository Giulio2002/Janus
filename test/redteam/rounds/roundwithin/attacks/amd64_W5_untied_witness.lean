import Janus
import Extracted

/-! Expected-reason: no witness tied to `within`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

theorem correctness (x y : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 1
      (fun s => StackWritable s 0 8)
      (fun r => r = [if y.toNat < x.toNat then x else y]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  all_goals simp [hbr]

theorem real (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun s => StackWritable s 0 8) (fun _ s' => results 1 s' = [if y.toNat < x.toNat then x else y]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  all_goals simp [hbr]

theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun s => StackWritable s 0 8) (fun _ s' => results 1 s' = [if y.toNat < x.toNat then x else y]) := real x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def x : BitVec 64 := 3#64
def y : BitVec 64 := 4#64
def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 3 then y else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (StackWritable s 0 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (results 1 s') = [if y.toNat < x.toNat then x else y]) :=
  ⟨ret, s0, x, y, hret, setup, hpre, correctness x y ret hret s0 setup hpre⟩
end Witness

end Proof
