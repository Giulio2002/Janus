import Extracted
import «Proof»
/-! Positive control (round 3): the `A64IndexByte` precondition is satisfiable. Concrete call
state: readable `g.stackguard0`, a 72-byte writable stack window (56 below, 16 above `SP`), a
length-64 slice whose data is 32-byte aligned and readable, disjoint from the stack. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Spec

namespace A64IndexByteWitness

def ret : Nat := 0x1000
def p : BitVec 64 := 0x30000   -- 32-byte aligned
def n : BitVec 64 := 64
def cap : BitVec 64 := 64
def c : BitVec 64 := 7

def s0 : State :=
  { regs := fun i => if i = 0 then p else if i = 1 then n else if i = 2 then cap
      else if i = 3 then c else if i = 28 then 0x20000
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := 0x10000, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0,
            [⟨0x10000 - 56, 72, true⟩, ⟨0x20010, 8, false⟩, ⟨0x30000, 64, false⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [p, n, cap, c] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases i with _|_|_|_|i <;> simp [s0] at h ⊢ <;> omega⟩

theorem pre :
    GuardOK s0 0 ∧ StackOK s0 56 16 ∧ n.toNat = 64 ∧ p.toNat % 32 = 0 ∧
      Ptr s0.mem p 64 false ∧ Disjoint p.toNat 64 (s0.sp.toNat - 56) 72 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [GuardOK, StackOK, Ptr, Disjoint, s0, p, n] <;> decide

theorem fires : Returns (Extracted.program.withExit ret) s0
    (fun s' => ABIReturn s0 s' ∧
      s'.regs 0 = BitVec.ofInt 64 (Proof.indexOf s0.mem p.toNat (c.toNat % 256) 64)) :=
  Proof.correctness p n cap c ret hret s0 setup pre

end A64IndexByteWitness
