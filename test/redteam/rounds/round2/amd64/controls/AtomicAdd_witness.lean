import Proof

/-! Positive control (round 2): the precondition of `AtomicAdd.correctness` is satisfiable, and
instantiating the theorem on a concrete call gives the hardware answer
(`*p = 40`, `d = 2` -> returns 42 and `*p = 42`). -/

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
  { regs := fun i => if i = 0 then 0x2000 else if i = 3 then 2 else if i = 4 then 0x8000 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [0x2000, 2] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, ?_⟩
  intro i h; simp at h; rcases i with _ | _ | i <;> simp_all [s0, argReg, intArgRegs] <;> omega

theorem pre : StackWritable s0 0 8 ∧ Buffer s0 0x2000 8 true ∧ Disjoint 0x2000 8 (s0.regs regSP) 8 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  simp [Disjoint, s0, regSP]

example : ∃ fuel s', (Extracted.program.withExit ret).run fuel s0 = .ok (.returned s') ∧
    s'.regs 0 = 42 ∧ s'.mem.readLE 0x2000 8 = 42 := by
  obtain ⟨f, s', h1, _, h2, h3⟩ := Proof.correctness 0x2000 2 ret hret s0 setup pre
  have e : s0.mem.readLE (0x2000 : BitVec 64).toNat 8 = 40 := by decide
  rw [e] at h2
  refine ⟨f, s', h1, by rw [h2]; decide, ?_⟩
  rw [show (0x2000 : BitVec 64).toNat = 0x2000 from rfl] at h3; rw [h3, h2]; decide


/-! ## Finding R2-A1 (split-lock): the precondition admits a word that straddles a 64-byte
cache line. `p = 0x203C` covers `0x203C..0x2043`, across the line boundary `0x2040`. The theorem
promises a normal return; on Linux with `split_lock_detect=fatal` the `LOCK XADDQ` raises `#AC`
and the process gets `SIGBUS` (see `host/splitlock.c`; in the default `warn` mode the kernel
logs a split-lock trap and the result is correct). -/
namespace Split
def mem : Memory :=
  ⟨fun a => if a = 0x203C then 40 else if a = 0x8000 then BitVec.ofNat 8 ret
      else if a = 0x8001 then BitVec.ofNat 8 (ret / 256) else 0,
   [⟨0x2000, 0x80, true⟩, ⟨0x8000, 8, true⟩]⟩
def s0 : State :=
  { regs := fun i => if i = 0 then 0x203C else if i = 3 then 2 else if i = 4 then 0x8000 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [0x203C, 2] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, ?_⟩
  intro i h; simp at h; rcases i with _ | _ | i <;> simp_all [s0, argReg, intArgRegs] <;> omega
theorem pre : StackWritable s0 0 8 ∧ Buffer s0 0x203C 8 true ∧ Disjoint 0x203C 8 (s0.regs regSP) 8 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  simp [Disjoint, s0, regSP]
/-- The word straddles the cache line at `0x2040`. -/
example : 0x203C / 64 ≠ (0x203C + 7) / 64 := by decide
example : ∃ fuel s', (Extracted.program.withExit ret).run fuel s0 = .ok (.returned s') ∧
    s'.regs 0 = 42 := by
  obtain ⟨f, s', h1, _, h2, _⟩ := Proof.correctness 0x203C 2 ret hret s0 setup pre
  have e : s0.mem.readLE (0x203C : BitVec 64).toNat 8 = 40 := by decide
  rw [e] at h2
  exact ⟨f, s', h1, by rw [h2]; decide⟩
end Split

end AuditWitness

#print axioms Proof.correctness
