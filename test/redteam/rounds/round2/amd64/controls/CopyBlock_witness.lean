import Proof

/-! Positive control (round 2): `CopyBlock.correctness` applies to a concrete call
(`src` byte `i` = `i + 1`, disjoint `dst`): the 128 bytes at `dst` become `src`'s. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI

namespace AuditWitness

def ret : Nat := 0x1000
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def mem : Memory :=
  ⟨fun a => if 0x3000 ≤ a ∧ a < 0x3080 then BitVec.ofNat 8 (a - 0x3000 + 1)
      else if a = 0x8000 then BitVec.ofNat 8 ret
      else if a = 0x8001 then BitVec.ofNat 8 (ret / 256) else 0,
   [⟨0x2000, 128, true⟩, ⟨0x3000, 128, false⟩, ⟨0x8000 - 40, 48, true⟩, ⟨0x5000, 0x40, false⟩]⟩

def rv : List (Nat × Nat) := [(0, 0x2000), (3, 0x3000), (4, 0x8000), (14, 0x5000)]

def s0 : State :=
  { regs := fun i => BitVec.ofNat 64 ((rv.lookup i).getD 0),
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [0x2000, 0x3000] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, ?_⟩
  intro i h; simp at h
  rcases i with _ | _ | i <;> first | rfl | omega

theorem pre : StackGuardOK s0 0 ∧ StackWritable s0 40 8 ∧ Buffer s0 0x2000 128 true ∧
    Buffer s0 0x3000 128 false ∧
    ((0x2000 : BitVec 64).toNat + 128 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat + 8 ≤ (0x2000 : BitVec 64).toNat) ∧
    ((0x3000 : BitVec 64).toNat + 128 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat ≤ (0x3000 : BitVec 64).toNat) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, by decide, by decide⟩

/-- The 128-byte value at `src` before the call (bytes 1..128). -/
def srcVal : Nat := Janus.Amd64.GoABI.listLE ((List.range 128).map (· + 1)) 128

set_option maxRecDepth 200000 in
example : ∃ fuel s', (Extracted.program.withExit ret).run fuel s0 = .ok (.returned s') ∧
    s'.mem.readLE 0x2000 128 = srcVal := by
  obtain ⟨f, s', h1, _, h2⟩ := Proof.correctness 0x2000 0x3000 ret hret s0 setup pre
  refine ⟨f, s', h1, ?_⟩
  have : s0.mem.readLE 0x3000 128 = srcVal := by decide
  simp only [valueAt] at h2
  exact h2.trans this

end AuditWitness

#print axioms Proof.correctness
