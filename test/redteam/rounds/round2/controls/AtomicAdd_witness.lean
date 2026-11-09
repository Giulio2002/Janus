import Extracted
import «Proof»
/-! Positive control: the AtomicAdd precondition is satisfiable (not vacuous). We build a
concrete call state, discharge CallSetup and the precondition by `decide`/`native`-free kernel
computation, and instantiate `Proof.correctness` to obtain a concrete `Returns`.
hasAtomics = 1636076 (computed). p = 0x3000 (8-aligned, writable), the LSE flag byte = 1. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Spec

namespace AtomicAddWitness

def ret : Nat := 0x1000
def p : BitVec 64 := 0x3000
def d : BitVec 64 := 7
def haAddr : Nat := 1636076

def s0 : State :=
  { regs := fun i => if i = 0 then p else if i = 1 then d
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := 0x10000, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun a => if a = haAddr then 1 else 0,
            [⟨haAddr, 1, false⟩, ⟨0x3000, 8, true⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [p, d] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases i with _ | _ | i <;> simp [s0] at h ⊢ <;> omega⟩

theorem pre : s0.mem.accessible (Proof.hasAtomics) 1 false = true ∧
    s0.mem.readLE Proof.hasAtomics 1 % 2 = 1 ∧ Ptr s0.mem p 8 true ∧ p.toNat % 8 = 0 := by
  have hha : Proof.hasAtomics = haAddr := by rfl
  rw [hha]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try rfl) <;> (unfold Ptr Memory.accessible <;> decide)

/-- The non-vacuous payload: `correctness` really fires on a satisfying state. -/
theorem fires : Returns (Extracted.program.withExit ret) s0
    (fun s' => ABIReturn s0 s' ∧
      (s'.regs 0).toNat = (s0.mem.readLE p.toNat 8 + d.toNat) % 2 ^ 64 ∧
      s'.mem = s0.mem.writeLE p.toNat 8 ((s0.mem.readLE p.toNat 8 + d.toNat) % 2 ^ 64)) :=
  Proof.correctness p d ret hret s0 setup pre

end AtomicAddWitness
