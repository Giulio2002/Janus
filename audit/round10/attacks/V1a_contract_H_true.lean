import Extracted

/-! Round 10 V1a: the round-9 C1 vacuity, brought back by instantiating the readiness predicate.
The statement quantifies over `impl` and `rt` as NewPair does, but passes `H := fun _ _ _ _ =>
True` ("the runtime is always ready"). That contract is false for every implementation (the
round-9 `Unsat.lean` argument, a 2^47-byte request with no heap mapped), so the theorem can
claim anything: here that NewPair returns 42. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

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

theorem unsat (p : Program) (addr : Nat) (rt : List (Nat × Nat)) :
    ¬ NewobjectContract p addr rt 4096 (fun _ _ _ _ => True) := by
  intro h
  have hpre : NewobjectPre 4096 (bigState addr) ∧ Ready (fun _ _ _ _ => True) rt
      [((bigState addr).regs 0).toNat] (bigState addr) := by
    refine ⟨?_, trivial⟩
    simp only [NewobjectPre, CallOK, TypeOK, bigState]
    simp only [ite_true, show (30 = 0) = False by decide, ite_false,
      show (BitVec.ofNat 64 T).toNat = T by decide, bigSize0]
    decide
  obtain ⟨k, s', -, -, ptr, junk, f, v, m, -, hfr, hq⟩ := h (bigState addr) rfl hpre
  have e1 : (bigState addr).mem = bigMem := rfl
  have e2 : ((bigState addr).regs 0).toNat = T := by simp [bigState]; decide
  have hq' := hq (by rw [e1, e2, bigSize0]; decide)
  have hacc := hq'.2.2.1
  rw [hfr.accessible] at hacc
  rw [e1, e2, bigSize0] at hacc
  have hb := blockBig
  generalize blockSize (2 ^ 47) (typNoscan bigMem T) = b at hacc hb
  simp [Memory.accessible, bigMem, SP, T] at hacc
  omega

theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 (fun _ _ _ _ => True)) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt)
      (fun _ s' => s'.regs 0 = 42) :=
  absurd hnew (unsat _ _ _)

end Proof
