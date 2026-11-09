import Proof

/-! Positive control (round 2): `ClearWords.correctness` applies to a concrete call that takes
the `REP STOSQ` path of `memclrNoHeapPointers` (`len = 300` words = 2400 bytes ≥ 2048,
`HasERMS = 1`, `HasAVX2 = 0`), and the model run itself (`#eval`) agrees. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI

namespace AuditWitness

def ret : Nat := 0x1000
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def avx2 : Nat := 0x5768c4
def erms : Nat := 0x5768d5
open Janus.Amd64.Tactic in
theorem avx2_eq : Proof.hasAVX2 = avx2 := by
  simp only [Proof.hasAVX2, Proof.mc, reduceSegAddr, reduceRipTarget, Nat.reduceAdd]; rfl
open Janus.Amd64.Tactic in
theorem erms_eq : Proof.hasERMS = erms := by
  simp only [Proof.hasERMS, Proof.mc, reduceSegAddr, reduceRipTarget, Nat.reduceAdd]; rfl

def B : Nat := 0x10000
def SP : Nat := 0x600000

def mem : Memory :=
  ⟨fun a => if B ≤ a ∧ a < B + 2400 then 0xAB else if a = erms then 1
      else if a = SP then BitVec.ofNat 8 ret
      else if a = SP + 1 then BitVec.ofNat 8 (ret / 256) else 0,
   [⟨B, 2400, true⟩, ⟨SP - 32, 48, true⟩, ⟨0x5768c0, 0x40, false⟩, ⟨0x7000, 0x40, false⟩]⟩

def rv : List (Nat × Nat) := [(0, B), (3, 300), (1, 300), (4, SP), (14, 0x7000)]

def s0 : State :=
  { regs := fun i => BitVec.ofNat 64 ((rv.lookup i).getD 0),
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry
    [BitVec.ofNat 64 B, 300, 300] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, ?_⟩
  intro i h; simp at h
  rcases i with _ | _ | _ | i <;> first | rfl | omega

set_option maxRecDepth 100000 in
theorem pre :
    StackGuardOK s0 0 ∧ StackWritable s0 32 16 ∧ Buffer s0 (BitVec.ofNat 64 B) (8 * (300 : BitVec 64).toNat) true ∧
      ((BitVec.ofNat 64 B).toNat + 8 * (300 : BitVec 64).toNat ≤ (s0.regs regSP).toNat - 32 ∨
        (s0.regs regSP).toNat + 16 ≤ (BitVec.ofNat 64 B).toNat) ∧
      s0.mem.accessible Proof.hasAVX2 1 false = true ∧ s0.mem.readLE Proof.hasAVX2 1 ≠ 1 ∧
      s0.mem.accessible Proof.hasERMS 1 false = true ∧
      ((BitVec.ofNat 64 B).toNat + 8 * (300 : BitVec 64).toNat ≤ Proof.hasAVX2 ∨ Proof.hasERMS + 1 ≤ (BitVec.ofNat 64 B).toNat) ∧
      (Proof.hasERMS + 1 ≤ (s0.regs regSP).toNat - 32 ∨ (s0.regs regSP).toNat + 16 ≤ Proof.hasAVX2) := by
  rw [avx2_eq, erms_eq]
  exact ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

example : ∃ fuel s', (Extracted.program.withExit ret).run fuel s0 = .ok (.returned s') ∧
    s'.mem.readLE (B + 8 * 299) 8 = 0 ∧ s'.mem.bytes (B + 2400) = 0 := by
  obtain ⟨f, s', h1, _, h2, h3⟩ :=
    Proof.correctness (BitVec.ofNat 64 B) 300 300 ret hret s0 setup pre
  refine ⟨f, s', h1, h2 299 (by decide), ?_⟩
  rw [h3 (B + 2400) (by right; decide) (by left; decide)]; decide

/-- Independent check: evaluate the model (not the proof). -/
def runIt : String :=
  match (Extracted.program.withExit ret).run 2000 s0 with
  | .ok (.returned s') =>
    s!"returned; words zero: {(List.range 300).all (fun j => s'.mem.readLE (B + 8 * j) 8 = 0)}; RSP={(s'.regs 4).toNat == SP + 8}"
  | .ok (.stub n _ _) => s!"stub {n}"
  | .error e => s!"fault {repr e}"
#eval runIt

end AuditWitness

#print axioms Proof.correctness
