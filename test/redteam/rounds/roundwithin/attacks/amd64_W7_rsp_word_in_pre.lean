import Janus
import Extracted

/-! Expected: VERIFIED (v0.4.0). Was rejected by the removed [RSP]-word rule; the precondition is evaluated before the return address is installed, so a conjunct about the word at RSP cannot restrict `ret` and the row is harmless. WHY: under v0.4.0 (option A) the precondition is evaluated on the call state BEFORE the return address is installed, so a conjunct that reads the word at [RSP] reads the pre-call stack word and cannot restrict `ret`. WHAT IS PROVED: for every call state s of Max with the stack window writable (the conjunct `readLE [RSP] 8 = readLE [RSP] 8` is a tautology) and EVERY admissible return address ret, the program started from s.setRet ret returns to ret within the stated bound with the stated result; the ret-pinning the removed rule guarded against is impossible.  -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

theorem real (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun s => StackWritable s 0 8) (fun _ s' => results 1 s' = [if y.toNat < x.toNat then x else y]) := by
  janus64_ensures_old [Janus.Amd64.GoABI.StackWritable, Janus.Amd64.GoABI.regSP]
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  all_goals simp [hbr]

theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y]
      (fun s => StackWritable s 0 8 ∧ s.mem.readLE (s.regs regSP).toNat 8 = s.mem.readLE (s.regs regSP).toNat 8) (fun _ s' => results 1 s' = [if y.toNat < x.toNat then x else y]) :=
  real x y |>.mono (fun _ h => h.1) (fun _ _ _ _ h => h)

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
theorem setup : CallSetup0 Extracted.entry [x, y] s0 :=
  ⟨rfl, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_, ?_⟩ <;> decide) | (refine ⟨?_, ?_, ?_⟩ <;> decide)

theorem within : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup0 Extracted.entry [x, y] s ∧ (StackWritable s 0 8 ∧ s.mem.readLE (s.regs regSP).toNat 8 = s.mem.readLE (s.regs regSP).toNat 8) ∧
    (Returns (Extracted.program.withExit ret) (s.setRet ret) fun s' =>
    ABIReturn (s.setRet ret) s' ∧ (results 1 s') = [if y.toNat < x.toNat then x else y]) :=
  ⟨ret, s0, x, y, hret, setup, ⟨hpre, rfl⟩, ((Proof.real x y) s0 setup hpre ret hret).returns⟩
end Witness

end Proof
