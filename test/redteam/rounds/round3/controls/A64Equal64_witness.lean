import Extracted
import «Proof»
/-! Positive control (round 3): the `A64Equal64` precondition is satisfiable, so the shipped
`Proof.correctness` is not vacuous. Concrete call state: readable `g.stackguard0`, 24-byte
writable stack window, two readable 64-byte arrays `a`, `b`, all pairwise disjoint. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Spec

namespace A64Equal64Witness

def ret : Nat := 0x1000
def a : BitVec 64 := 0x30000
def b : BitVec 64 := 0x40000

def s0 : State :=
  { regs := fun i => if i = 0 then a else if i = 1 then b
      else if i = 28 then 0x20000 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := 0x10000, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0,
            [⟨0x10000 - 24, 24, true⟩, ⟨0x20010, 8, false⟩,
             ⟨0x30000, 64, false⟩, ⟨0x40000, 64, false⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases i with _ | _ | i <;> simp [s0] at h ⊢ <;> omega⟩

theorem pre :
    GuardOK s0 0 ∧ StackOK s0 24 0 ∧ Ptr s0.mem a 64 false ∧ Ptr s0.mem b 64 false ∧
      Disjoint a.toNat 64 (s0.sp.toNat - 24) 24 ∧ Disjoint b.toNat 64 (s0.sp.toNat - 24) 24 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [GuardOK, StackOK, Ptr, Disjoint, s0, a, b] <;> decide

theorem fires : Returns (Extracted.program.withExit ret) s0
    (fun s' => ABIReturn s0 s' ∧
      s'.regs 0 = if s0.mem.readLE a.toNat 64 = s0.mem.readLE b.toNat 64 then 1 else 0) :=
  Proof.correctness a b ret hret s0 setup pre

end A64Equal64Witness
