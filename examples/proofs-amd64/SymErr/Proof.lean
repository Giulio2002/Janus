import Janus
import Extracted

/-! `example.com/basic.SymErr()` on amd64: returns the interface value of the package variable
`example.com/basic.errSym`, a sentinel error the linker initialised: the two words are the named
`Extracted.dataAddr.«example.com/basic.errSym→type»` and `…→data»` (generated from the binary's link-time
image), the variable is `Extracted.dataAddr.«example.com/basic.errSym»`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

abbrev v : Nat := Extracted.dataAddr.«example.com/basic.errSym»
abbrev typeWord : Nat := Extracted.dataAddr.«example.com/basic.errSym→type»
abbrev dataWord : Nat := Extracted.dataAddr.«example.com/basic.errSym→data»

def ErrHolds (m : Janus.Arm64.Memory) : Prop :=
  m.accessible v Extracted.dataSize.«example.com/basic.errSym» false = true ∧
    m.readLE v 8 = typeWord ∧ m.readLE (v + 8) 8 = dataWord

theorem correctness :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ ErrHolds s.mem)
      (fun _ s' => results 2 s' = [BitVec.ofNat 64 typeWord, BitVec.ofNat 64 dataWord]) := by
  intro ret hret s hs hpre
  janus64_addrs
  janus64_intro hs
  obtain ⟨⟨-, hnw, hstk⟩, hacc, h0, h1⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hstk hnw
  simp only [v, typeWord, dataWord, Extracted.dataAddr.«example.com/basic.errSym»,
    Extracted.dataAddr.«example.com/basic.errSym→type», Extracted.dataAddr.«example.com/basic.errSym→data»,
    Extracted.dataSize.«example.com/basic.errSym»] at hacc h0 h1 ⊢
  janus64_run
  done

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def s0 : State :=
  { regs := fun r_ => if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := ⟨fun a => if v ≤ a ∧ a < v + 8 then BitVec.ofNat 8 (typeWord / 256 ^ (a - v)) else if v + 8 ≤ a ∧ a < v + 16 then BitVec.ofNat 8 (dataWord / 256 ^ (a - v - 8)) else wmem64.bytes a, wmem64.regions ++ [⟨v, Extracted.dataSize.«example.com/basic.errSym», false⟩]⟩ }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h, rfl⟩
set_option maxRecDepth 100000 in
theorem hpre : (fun s => StackWritable s 0 8 ∧ ErrHolds s.mem) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) , RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧ (StackWritable s 0 8 ∧ ErrHolds s.mem) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ results 2 s' = [BitVec.ofNat 64 typeWord, BitVec.ofNat 64 dataWord]) :=
  ⟨ret, s0, hret, setup, hpre, correctness  ret hret s0 setup hpre⟩

end Witness

end Proof
