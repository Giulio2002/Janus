import Janus
import Extracted

/-! `example.com/basic.GlobalTable(i)` on amd64: `tbl[i&7]`, where `tbl` (`example.com/basic.tbl`,
64 bytes at `tbl` in the writable `.noptrdata`) is memory the caller provides. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- Address of `example.com/basic.tbl`: the RIP-relative operand of the `LEAQ tbl(SB), CX` at
offset 3, read off the extracted code (layout-independent). -/
def tbl : Nat := ripTarget Extracted.program (Extracted.entry + 3)

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i]
      (fun s => StackWritable s 0 8 ∧ s.mem.accessible tbl 64 false = true)
      (fun s s' => results 1 s' = [BitVec.ofNat 64 (s.mem.readLE (tbl + i.toNat % 8 * 8) 8)]) := by
  intro ret hret s hs hpre
  simp only [tbl] at *
  janus64_addrs
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ht⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def i : BitVec 64 := 5#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then i else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := ⟨wmem64.bytes, wmem64.regions ++ [⟨tbl, 64, false⟩]⟩ }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [i] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ s.mem.accessible tbl 64 false = true) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (i : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [i] s ∧ (StackWritable s 0 8 ∧ s.mem.accessible tbl 64 false = true) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ results 1 s' = [BitVec.ofNat 64 (s.mem.readLE (tbl + i.toNat % 8 * 8) 8)]) :=
  ⟨ret, s0, i, hret, setup, hpre, correctness i ret hret s0 setup hpre⟩

end Witness

end Proof
