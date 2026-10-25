import Janus
open Janus Janus.Arm64 Janus.Tactic Janus.Contracts

/-! Round 9 C1, kernel-checked: the allocation contract as it stood before round 9 (base
ff88563, `Janus/Contracts/Alloc.lean`, copied here verbatim as `OldNewobjectContract`) is false
for **every** program, address and runtime-owned list `rt`. A call state with a 2^47-byte type
(allowed: `≤ maxAlloc`) whose only regions are the stack window and the 16-byte descriptor
satisfies its precondition, and no code can return a writable 2^47-byte object there (memory
regions never change). So every theorem that assumed it held vacuously.
`NewobjectContract` itself (with the round-9 readiness hypothesis `H`) is satisfiable:
`audit/round9/controls/NewPair_witness.lean`. -/

namespace R9

/-- `NewobjectPre` / `NewobjectContract` before round 9 (no readiness hypothesis). -/
def OldNewobjectPre (stack : Nat) (s : State) : Prop :=
  CallOK s stack 1 ∧ TypeOK s.mem (s.regs 0).toNat ∧ typSize s.mem (s.regs 0).toNat ≤ maxAlloc
def OldNewobjectContract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat) : Prop :=
  Summary p addr (OldNewobjectPre stack)
    (fun s s' => AllocRet rt stack 1 (fun ptr => [ptr]) s s' fun m ptr =>
      0 < typSize s.mem (s.regs 0).toNat →
        Fresh rt m ptr (typSize s.mem (s.regs 0).toNat)
          (blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat)) true)

def T : Nat := 0x200000
def SP : Nat := 0x100000
def bigMem : Memory where
  bytes := fun a => if a = T + 5 then 0x80 else 0
  regions := [⟨SP - 4096, 4096 + 16, true⟩, ⟨T, 16, false⟩]
def bigState (addr : Nat) : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 T else 0, sp := BitVec.ofNat 64 SP,
    pc := BitVec.ofNat 64 addr, flags := ⟨false, false, false, false⟩, mem := bigMem }

theorem bigSize0 : typSize bigMem T = 2 ^ 47 := by decide
theorem blockBig : 2 ^ 47 ≤ blockSize (2 ^ 47) (typNoscan bigMem T) := by
  have := le_roundupsize (2 ^ 47) (typNoscan bigMem T)
  unfold blockSize; split <;> omega
theorem bigSize (addr : Nat) : typSize (bigState addr).mem ((bigState addr).regs 0).toNat = 2 ^ 47 :=
  bigSize0

theorem bigPre (addr : Nat) : OldNewobjectPre 4096 (bigState addr) := by
  simp only [OldNewobjectPre, CallOK, TypeOK, bigState]
  simp only [ite_true, show (30 = 0) = False by decide, ite_false,
    show (BitVec.ofNat 64 T).toNat = T by decide, bigSize0]
  decide

theorem newobject_unsat (p : Program) (addr : Nat) (rt : List (Nat × Nat)) :
    ¬ OldNewobjectContract p addr rt 4096 := by
  intro h
  unfold OldNewobjectContract Summary at h
  have h1 := h (bigState addr) rfl (bigPre addr)
  obtain ⟨k, s', -, -, ptr, junk, f, v, m, -, hfr, hq⟩ := h1
  have hq' := hq (by rw [bigSize]; decide)
  have hacc := hq'.2.2.1
  rw [hfr.accessible] at hacc
  have e1 : (bigState addr).mem = bigMem := rfl
  have e2 : ((bigState addr).regs 0).toNat = T := by simp [bigState]; decide
  rw [e1, e2, bigSize0] at hacc
  have hb := blockBig
  generalize blockSize (2 ^ 47) (typNoscan bigMem T) = b at hacc hb
  simp [Memory.accessible, bigMem, SP, T] at hacc
  omega

end R9
