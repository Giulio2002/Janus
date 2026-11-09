import Extracted
import «Proof»
/-! Positive control: the CopyBlock precondition is satisfiable (not vacuous). Concrete call
state with a readable `g.stackguard0`, a 56-byte writable stack window, a 128-byte writable
`dst`, a 128-byte readable `src`, all pairwise disjoint. `Proof.correctness` then fires. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Spec

namespace CopyBlockWitness

def ret : Nat := 0x1000
def dst : BitVec 64 := 0x30000
def src : BitVec 64 := 0x40000

def s0 : State :=
  { regs := fun i => if i = 0 then dst else if i = 1 then src
      else if i = 28 then 0x20000 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := 0x10000, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0,
            [⟨0x10000 - 56, 56, true⟩, ⟨0x20010, 8, false⟩,
             ⟨0x30000, 128, true⟩, ⟨0x40000, 128, false⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [dst, src] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases i with _ | _ | i <;> simp [s0] at h ⊢ <;> omega⟩

theorem pre :
    GuardOK s0 0 ∧ StackOK s0 56 0 ∧ Ptr s0.mem dst 128 true ∧ Ptr s0.mem src 128 false ∧
      Disjoint dst.toNat 128 src.toNat 128 ∧ Disjoint dst.toNat 128 (s0.sp.toNat - 56) 56 ∧
      Disjoint src.toNat 128 (s0.sp.toNat - 56) 56 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [GuardOK, StackOK, Ptr, Disjoint, s0, dst, src] <;> decide

theorem fires : Returns (Extracted.program.withExit ret) s0
    (fun s' => ABIReturn s0 s' ∧
      (∀ j < 16, s'.mem.readLE (dst.toNat + 8 * j) 8 = s0.mem.readLE (src.toNat + 8 * j) 8) ∧
      OnlyWrites (Proof.M₀ s0) s'.mem dst.toNat 128) :=
  Proof.correctness dst src ret hret s0 setup pre

end CopyBlockWitness
