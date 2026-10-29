import Extracted

/-! Round 11 P1a: the V1 vacuity for the panic contracts. `PanicRuntime` is not a runtime
parameter type of the round-10 V1 rule, so a closed `Q0` (one fixed unrecovered panic of value type 1 in
every memory, `rp` the word at `[X29 + 8]`) is accepted. `GorecoverContract … Q0` holds of no program
(`unsat`: the contract makes `recover()` mark that panic recovered, but the chain is the same
constant list in every memory), and the theorem claims that RecoverSet returns 42. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic
  Janus.Contracts.PanicSat

namespace Proof

def r0 : PanicRec := { arg := ⟨1, 0⟩, goexit := false, start := 0, recovered := false }

def Q0 : PanicRuntime where
  err := fun _ => ⟨1, 0⟩
  priv := []
  depth := 64
  Env := fun _ => True
  panics := fun _ _ => [r0]
  defers := fun _ _ => []
  saved := fun _ _ => none
  rp := fun m _ => m.readLE (((sstate 0 zmem 0 0).regs 29).toNat + 8) 8
  room := fun _ _ => 1
  wrapper := fun _ => False

def st (addr : Nat) : State := sstate addr zmem 0 0

@[simp] theorem Q0_depth : Q0.depth = 64 := rfl

theorem pre0 (addr : Nat) : PanicPre Q0 0 (st addr) := by
  have hsp : (st addr).sp = BitVec.ofNat 64 swsp := rfl
  have hg28 : (st addr).regs 28 = BitVec.ofNat 64 swg := rfl
  have h30 : (st addr).regs 30 = BitVec.ofNat 64 sret := rfl
  have hm : (st addr).mem = zmem := rfl
  have hgn : (BitVec.ofNat 64 swg).toNat = swg := by decide
  have hspn : (BitVec.ofNat 64 swsp).toNat = swsp := by decide
  refine ⟨trivial, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, hg28, hgn]; decide
  · simp only [regG, stackguard0Offset, hg28, hm, hgn]; decide
  · simp only [stackguard0, regG, stackguard0Offset, hg28, hm, hsp, Q0_depth, hgn, hspn]; decide
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [hsp, hspn]; decide
  · simp only [hsp, hspn, Q0_depth]; decide
  · decide
  · simp only [hsp, hspn, Q0_depth]; decide
  · simp only [hsp, hspn, hm, Q0_depth]; decide
  · simp [Q0, Outside]

theorem unsat (p : Program) (addr : Nat) : ¬ GorecoverContract p addr Q0 := by
  intro h
  obtain ⟨k, s', -, -, -, hpost⟩ :=
    h (st addr) (by simp [st, sstate]) ⟨pre0 addr,
      by show zmem.accessible (BitVec.toNat (BitVec.ofNat 64 (swsp - 8)) + 8) 8 false = true; decide,
      by show BitVec.toNat (BitVec.ofNat 64 (swsp - 8)) + 16 ≤ 2 ^ 48; decide⟩
  have hrec := hpost.2.2.2.2.2
  have h1 := (hrec r0 [] rfl rfl rfl (fun h => h) rfl).2.2
  simp [Q0, r0] at h1


theorem correctness (impl : List Segment) (x e d : BitVec 64)
    (hrec : GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") Q0) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, e, d] (fun _ => True)
      (fun _ s' => s'.regs 0 = 42) :=
  absurd hrec (unsat _ _)

end Proof
