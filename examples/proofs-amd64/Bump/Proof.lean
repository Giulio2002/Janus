import Janus
import Extracted

/-! `example.com/basic.Bump(d)` on amd64: `counter += d; return counter`, for the writable global `example.com/basic.counter`, which the precondition must provide. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- Address of `example.com/basic.counter` (`.noptrbss`): the RIP-relative operand of the first
instruction (`MOVQ counter(SB), CX`), read off the extracted code, so the proof does not
depend on where the linker put the global. -/
def counter : Nat := ripTarget Extracted.program Extracted.entry

theorem correctness (d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [d]
      (fun s => StackWritable s 0 8 ∧ s.mem.accessible counter 8 true = true ∧
        Disjoint (s.regs regSP) 8 (BitVec.ofNat 64 counter) 8)
      (fun s s' => s'.regs 0 = d + BitVec.ofNat 64 (s.mem.readLE counter 8) ∧
        s'.mem.readLE counter 8 = (s'.regs 0).toNat) := by
  intro ret hret s hs hpre
  simp only [counter] at *
  janus64_addrs
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, hc, hd⟩ := hpre
  simp only [Disjoint, regSP, Nat.sub_zero, Nat.zero_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hacc hd hnw
  janus64_run

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def d : BitVec 64 := 5#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then d else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := ⟨wmem64.bytes, wmem64.regions ++ [⟨counter, 8, true⟩]⟩ }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [d] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ s.mem.accessible counter 8 true = true ∧
        Disjoint (s.regs regSP) 8 (BitVec.ofNat 64 counter) 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (d : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [d] s ∧ (StackWritable s 0 8 ∧ s.mem.accessible counter 8 true = true ∧
        Disjoint (s.regs regSP) 8 (BitVec.ofNat 64 counter) 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ s'.regs 0 = d + BitVec.ofNat 64 (s.mem.readLE counter 8) ∧
        s'.mem.readLE counter 8 = (s'.regs 0).toNat) :=
  ⟨ret, s0, d, hret, setup, hpre, correctness d ret hret s0 setup hpre⟩

end Witness

end Proof
