import Proof

/-! Positive control (round 2): the precondition of `AtomicMax.correctness` is satisfiable, and
instantiating the theorem on a concrete call gives the hardware answer
(`*p = 40`, `v = 50` -> returns 40 and `*p = 50`). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI

namespace AuditWitness

def ret : Nat := 0x1000
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- `p = 0x2000` holds 40, `RSP = 0x8000` holds `ret`. -/
def mem : Memory :=
  ⟨fun a => if a = 0x2000 then 40 else if a = 0x8000 then BitVec.ofNat 8 ret
      else if a = 0x8001 then BitVec.ofNat 8 (ret / 256) else 0,
   [⟨0x2000, 8, true⟩, ⟨0x8000, 8, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then 0x2000 else if i = 3 then 50 else if i = 4 then 0x8000 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [0x2000, 50] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, ?_⟩
  intro i h; simp at h; rcases i with _ | _ | i <;> simp_all [s0, argReg, intArgRegs] <;> omega

theorem pre : StackWritable s0 0 8 ∧ Buffer s0 0x2000 8 true ∧ Disjoint 0x2000 8 (s0.regs regSP) 8 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  simp [Disjoint, s0, regSP]

example : ∃ fuel s', (Extracted.program.withExit ret).run fuel s0 = .ok (.returned s') ∧
    s'.regs 0 = 40 ∧ s'.mem.readLE 0x2000 8 = 50 := by
  obtain ⟨f, s', h1, _, h2, h3⟩ := Proof.correctness 0x2000 50 ret hret s0 setup pre
  have e : s0.mem.readLE (0x2000 : BitVec 64).toNat 8 = 40 := by decide
  rw [e] at h2 h3
  exact ⟨f, s', h1, h2, h3⟩

end AuditWitness

#print axioms Proof.correctness
