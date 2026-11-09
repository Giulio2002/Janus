import Proof

/-! Positive control (round 2): `CopyWords.correctness` applies to a concrete call
(`dst` has 2 words, `src` = [7, 9, 11]) and yields `n = 2`, `dst = [7, 9]`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI

namespace AuditWitness

def ret : Nat := 0x1000
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def mem : Memory :=
  ⟨fun a => if a = 0x3000 then 7 else if a = 0x3008 then 9 else if a = 0x3010 then 11
      else if a = 0x8000 then BitVec.ofNat 8 ret
      else if a = 0x8001 then BitVec.ofNat 8 (ret / 256) else 0,
   [⟨0x2000, 16, true⟩, ⟨0x3000, 24, false⟩, ⟨0x8000, 40, true⟩]⟩

def rv : List (Nat × Nat) := [(0, 0x2000), (3, 2), (1, 2), (7, 0x3000), (6, 3), (8, 3), (4, 0x8000)]

def s0 : State :=
  { regs := fun i => BitVec.ofNat 64 ((rv.lookup i).getD 0),
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry
    [0x2000, 2, 2, 0x3000, 3, 3] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, ?_⟩
  intro i h; simp at h
  rcases i with _ | _ | _ | _ | _ | _ | i <;> first | rfl | omega

theorem pre : StackWritable s0 0 40 ∧ Buffer s0 0x2000 (8 * (2 : BitVec 64).toNat) true ∧
    Buffer s0 0x3000 (8 * (3 : BitVec 64).toNat) false ∧
    Disjoint 0x2000 (8 * (2 : BitVec 64).toNat) 0x3000 (8 * (3 : BitVec 64).toNat) ∧
    Disjoint 0x2000 (8 * (2 : BitVec 64).toNat) (s0.regs regSP) 40 ∧
    Disjoint 0x3000 (8 * (3 : BitVec 64).toNat) (s0.regs regSP) 40 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_⟩ <;>
    simp [Disjoint, s0, regSP, rv] <;> decide

example : ∃ fuel s', (Extracted.program.withExit ret).run fuel s0 = .ok (.returned s') ∧
    s'.regs 0 = 2 ∧ s'.mem.readLE 0x2000 8 = 7 ∧ s'.mem.readLE 0x2008 8 = 9 := by
  obtain ⟨f, s', h1, _, h2, h3⟩ :=
    Proof.correctness 0x2000 2 2 0x3000 3 3 (by decide) (by decide) ret hret s0 setup pre
  have h0 := h3 0 (by decide); have h1' := h3 1 (by decide)
  simp only [results_one, List.cons.injEq, and_true] at h2
  refine ⟨f, s', h1, by rw [h2]; decide, ?_, ?_⟩
  · have : s0.mem.readLE 0x3000 8 = 7 := by decide
    simpa [this] using h0
  · have : s0.mem.readLE 0x3008 8 = 9 := by decide
    simpa [this] using h1'

end AuditWitness

#print axioms Proof.correctness
