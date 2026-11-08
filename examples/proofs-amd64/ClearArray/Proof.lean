import Janus
import Extracted

/-! `example.com/basic.ClearArray(p *[5]uint64)` on amd64: `clear` on an array.

For every pointer `p` to 40 writable bytes (`Buffer`) that do not overlap the return-address
slot, all 40 bytes of `*p` are zero after the call (the 320-bit value at `p` is `0`) and nothing
outside `[p, p + 40)` changes (`OnlyWrites`). `clear(p[:])` compiles to three overlapping 16-byte
stores of the zero register `X15` (`MOVUPS X15, 0/16/24(AX)`); `X15 = 0` is part of the Go ABI
call state. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec

theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p]
      (fun s => StackWritable s 0 8 ∧ Buffer s p 40 true ∧ GoABI.Disjoint p 40 (s.regs regSP) 8)
      (fun s s' => s'.mem.readLE p.toNat 40 = 0 ∧ OnlyWrites s.mem s'.mem p.toNat 40) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hpw, hp⟩, hd⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add, GoABI.Disjoint] at hacc hnw hd
  janus64_run
  refine ⟨?_, by janus64_simp [onlyWrites_writeLE_iff, onlyWrites_self]⟩
  rw [show (40 : Nat) = 16 + (8 + 16) from rfl, Janus.Arm64.Memory.readLE_add, Janus.Arm64.Memory.readLE_add]
  janus64_simp [Janus.Tactic.readLE_writeLE_inside, Nat.zero_div, Nat.zero_mod]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def p : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)

def s0 : State :=
  { regs := fun i => if i = 0 then p else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [p] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ Buffer s p 40 true ∧ GoABI.Disjoint p 40 (s.regs regSP) 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (p : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [p] s ∧ (StackWritable s 0 8 ∧ Buffer s p 40 true ∧ GoABI.Disjoint p 40 (s.regs regSP) 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ s'.mem.readLE p.toNat 40 = 0 ∧ OnlyWrites s.mem s'.mem p.toNat 40) :=
  ⟨ret, s0, p, hret, setup, hpre, correctness p ret hret s0 setup hpre⟩

end Witness

end Proof
