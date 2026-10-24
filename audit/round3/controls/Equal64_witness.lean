import Extracted
import «Proof»
/-! Positive control (round 3): the amd64 `Equal64` precondition is satisfiable, so the shipped
`Proof.correctness` is not vacuous. Concrete call state: the return address on the stack, a
readable `g.stackguard0`, a 48-byte writable stack window, two readable 64-byte arrays `a`, `b`,
and a readable `internal/cpu.X86.HasAVX2` feature byte, all pairwise disjoint. The theorem holds
for any value of that byte (both the AVX2 and the SSE path), so the byte is left 0. -/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Equal64Witness

def ret : Nat := 0x1000
def a : BitVec 64 := 0x30000
def b : BitVec 64 := 0x40000

def bytes (x : Nat) : Janus.Arm64.Byte := if x = 0x10001 then 0x10 else 0

def s0 : State :=
  { regs := fun i => if i = 0 then a else if i = 3 then b
      else if i = 4 then 0x10000 else if i = 14 then 0x20000 else 0,
    rip := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0,
    mem := ⟨bytes,
            [⟨0x10000 - 40, 48, true⟩, ⟨0x20010, 8, false⟩,
             ⟨0x30000, 64, false⟩, ⟨0x40000, 64, false⟩, ⟨0x579264, 1, false⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b] s0 := by
  refine ⟨rfl, ?_, rfl, by decide, ?_, rfl⟩
  · show Janus.Arm64.Memory.readLE s0.mem _ 8 = _
    rw [Janus.Amd64.Program.exitAddr_withExit]; decide
  · intro i h; simp only [List.length_cons, List.length_nil] at h
    rcases i with _ | _ | i <;> first | rfl | (simp only [Nat.succ_lt_succ_iff] at h; omega)

set_option maxHeartbeats 2000000 in
theorem pre :
    StackGuardOK s0 0 ∧ StackWritable s0 40 8 ∧ Buffer s0 a 64 false ∧
      Buffer s0 b 64 false ∧
      (a.toNat + 64 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat ≤ a.toNat) ∧
      (b.toNat + 64 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat ≤ b.toNat) ∧
      s0.mem.accessible Proof.hasAVX2 1 false = true ∧
      (Proof.hasAVX2 + 1 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat ≤ Proof.hasAVX2) := by
  have hav : Proof.hasAVX2 = 0x579264 := by
    simp only [Proof.hasAVX2, reduceSegAddr, reduceRipTarget]
  rw [hav]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [StackWritable, Buffer, regSP, s0, a, b] <;> decide

theorem fires : Returns (Extracted.program.withExit ret) s0
    (fun s' => ABIReturn s0 s' ∧
      (s'.regs 0).setWidth 8 = if valueAt s0 a 64 = valueAt s0 b 64 then 1 else 0) :=
  Proof.correctness a b ret hret s0 setup pre

end Equal64Witness
