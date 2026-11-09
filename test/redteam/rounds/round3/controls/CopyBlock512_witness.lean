import Extracted
import «Proof»
/-! Positive control (round 3): the amd64 `CopyBlock512` precondition is satisfiable, so the
shipped `Proof.correctness` is not vacuous. Concrete call state: the return address on the
stack, a readable `g.stackguard0`, a 48-byte writable stack window, a 512-byte writable `dst`,
a 512-byte readable `src`, and a readable `runtime.memmoveBits` byte with the AVX bit set, all
pairwise disjoint. -/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace CopyBlock512Witness

def ret : Nat := 0x1000
def dst : BitVec 64 := 0x30000
def src : BitVec 64 := 0x40000

-- byte 0x10001 = 0x10 encodes ret = 0x1000 at RSP (0x10000); byte 0x578ab0 = 1 is memmoveBits.
def bytes (a : Nat) : Janus.Arm64.Byte :=
  if a = 0x10001 then 0x10 else if a = 0x578ab0 then 1 else 0

def s0 : State :=
  { regs := fun i => if i = 0 then dst else if i = 3 then src
      else if i = 4 then 0x10000 else if i = 14 then 0x20000 else 0,
    rip := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0,
    mem := ⟨bytes,
            [⟨0x10000 - 40, 48, true⟩, ⟨0x20010, 8, false⟩,
             ⟨0x30000, 512, true⟩, ⟨0x40000, 512, false⟩, ⟨0x578ab0, 1, false⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := by
  refine ⟨by decide, ?_, ?_⟩ <;> decide

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [dst, src] s0 := by
  refine ⟨rfl, ?_, rfl, by decide, ?_, rfl⟩
  · show Janus.Arm64.Memory.readLE s0.mem _ 8 = _
    rw [Janus.Amd64.Program.exitAddr_withExit]; decide
  · intro i h; simp only [List.length_cons, List.length_nil] at h
    rcases i with _ | _ | i <;> first | rfl | (simp only [Nat.succ_lt_succ_iff] at h; omega)

set_option maxHeartbeats 2000000 in
theorem pre :
    StackGuardOK s0 0 ∧ StackWritable s0 40 8 ∧ Buffer s0 dst 512 true ∧
      Buffer s0 src 512 false ∧ Disjoint dst 512 src 512 ∧
      (dst.toNat + 512 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat + 8 ≤ dst.toNat) ∧
      (src.toNat + 512 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat ≤ src.toNat) ∧
      s0.mem.accessible Proof.memmoveBits 1 false = true ∧ s0.mem.readLE Proof.memmoveBits 1 % 2 = 1 ∧
      (Proof.memmoveBits + 1 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat ≤ Proof.memmoveBits) ∧
      (dst.toNat + 512 ≤ Proof.memmoveBits ∨ Proof.memmoveBits + 1 ≤ dst.toNat) := by
  have hmb : Proof.memmoveBits = 0x578ab0 := by
    simp only [Proof.memmoveBits, reduceSegAddr, reduceRipTarget]
  rw [hmb]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [StackWritable, Buffer, Disjoint, regSP, s0, dst, src] <;> decide

theorem fires : Returns (Extracted.program.withExit ret) s0
    (fun s' => ABIReturn s0 s' ∧ valueAt s' dst 512 = valueAt s0 src 512) :=
  Proof.correctness dst src ret hret s0 setup pre

end CopyBlock512Witness
