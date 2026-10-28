import Extracted

/-! Round 11 H1b (H1a with the model pinned by an equation premise instead of instantiated): the V1 vacuity for the hash contracts. `HashModel` is not a runtime parameter
type of the auditor's V1 rule; the closed model `H0` (every `memhash` is 2^64, which no 64-bit
register holds) makes `Memhash … H0` unsatisfiable (`unsat`), so the theorem claims anything:
here that memhash16 returns 42. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Hash Janus.Contracts.Mem

namespace Proof

def H0 : HashModel where
  mem := fun _ _ _ => 2 ^ 64
  mem32 := fun _ _ => 0
  mem64 := fun _ _ => 0
  TypeHash := fun _ _ _ _ _ => False
  Hashable := fun _ _ _ => False
  Env := fun _ _ => True
  priv := []

def G : Nat := 0x300000
def SP : Nat := 0x100000
def A : Nat := 0x200000
def mem0 : Memory where
  bytes := fun _ => 0
  regions := [⟨SP - 4096, 4096 + 32, true⟩, ⟨G, 24, false⟩, ⟨A, 8, false⟩]
def st (addr : Nat) : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 G else if i = 0 then BitVec.ofNat 64 A else if i = 2 then 8 else 0,
    sp := BitVec.ofNat 64 SP, pc := BitVec.ofNat 64 addr, flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem r28 (a : Nat) : (st a).regs 28 = BitVec.ofNat 64 G := by simp [st]
theorem r0 (a : Nat) : (st a).regs 0 = BitVec.ofNat 64 A := by simp [st]
theorem r2 (a : Nat) : (st a).regs 2 = 8 := by simp [st]
theorem r30 (a : Nat) : (st a).regs 30 = 0 := by simp [st]
theorem sp_ (a : Nat) : (st a).sp = BitVec.ofNat 64 SP := rfl
theorem mem_ (a : Nat) : (st a).mem = mem0 := rfl
theorem G_nat : (BitVec.ofNat 64 G).toNat = G := by decide
theorem A_nat : (BitVec.ofNat 64 A).toNat = A := by decide
theorem SP_nat : (BitVec.ofNat 64 SP).toNat = SP := by decide

theorem pre1 (addr : Nat) : HPre H0 4096 3 (st addr) ∧ Input (st addr) 4096 3 ((st addr).regs 0).toNat ((st addr).regs 2).toNat := by
  refine ⟨⟨trivial, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show StackGuardOK (st addr) 4096
    rw [← Spec.guardOK_iff]
    simp only [GuardOK, r28, sp_, mem_, G_nat, SP_nat]
    decide
  · simp only [CallOK, r30, sp_, mem_, SP_nat]
    decide
  · simp [H0, Outside]
  · simp only [calleeStack, r28, sp_, G_nat, SP_nat, Outside]
    decide
  · simp [H0, Outside]
  · simp only [Input, r0, r2, mem_, A_nat, calleeStack, sp_, SP_nat, Outside]
    decide

theorem unsat (p : Program) (addr : Nat) (d : Nat) : d = 4096 → ¬ Memhash p addr H0 d := by
  intro hd h
  subst hd
  obtain ⟨k, s', -, -, r, v, fl, fs, m, -, -, -, hr⟩ := h (st addr) (by simp [st]) (pre1 addr)
  have := (r 0).isLt
  simp [H0] at hr
  omega

theorem correctness (impl : List Segment) (a b : BitVec 64) (H : HashModel) (hH : H = H0)
    (hm : Memhash (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memhash") H 4096) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => True)
      (fun _ s' => s'.regs 0 = 42) := by
  subst hH
  exact absurd hm (unsat _ _ _ rfl)

end Proof
