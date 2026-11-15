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

theorem setup : CallSetup0 Extracted.entry [0x2000, 50] s0 := by
  refine ⟨rfl, rfl, by decide, ?_, rfl⟩
  intro i h; simp at h; rcases i with _ | _ | i <;> simp_all [s0, argReg, intArgRegs] <;> omega

/-- `s0.setRet ret` agrees with `s0` on the word at `p` (the return slot `[0x8000, 0x8008)` is elsewhere): the theorem's readLE terms are about the
state the run starts from, `s0.setRet ret`, and `readLE_setRet_of_disjoint` moves them back to `s0`. -/
theorem rd_setRet : (s0.setRet ret).mem.readLE (0x2000 : BitVec 64).toNat 8 = 40 := by
  rw [readLE_setRet_of_disjoint (by simp [s0])]; decide

theorem pre : StackWritable s0 0 8 ∧ Buffer s0 0x2000 8 true ∧ (0x2000 : BitVec 64).toNat % 8 = 0 ∧
    Disjoint 0x2000 8 (s0.regs regSP) 8 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_, ?_⟩ <;> decide) | (refine ⟨?_, ?_, ?_⟩ <;> decide)

example : ∃ fuel s', (Extracted.program.withExit ret).run fuel (s0.setRet ret) = .ok (.returned s') ∧
    s'.regs 0 = 40 ∧ s'.mem.readLE 0x2000 8 = 50 := by
  obtain ⟨f, s', h1, _, h2, h3⟩ := (Proof.correctness 0x2000 50) s0 setup pre ret hret
  rw [rd_setRet] at h2 h3
  exact ⟨f, s', h1, h2, h3⟩

end AuditWitness

#print axioms Proof.correctness
