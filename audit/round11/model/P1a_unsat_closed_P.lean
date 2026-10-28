import Janus
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic
  Janus.Contracts.PanicSat

/-! Round 11 P1a (model row): `GorecoverContract` for a CLOSED `PanicRuntime` `Q0` whose goroutine
has, in every memory, exactly one active unrecovered panic (value type word 1, no wrappers) and whose
return point `rp` is whatever word `[X29 + 8]` holds holds of no program: the contract promises that
`recover()` returns the panic's value AND that the panic chain afterwards is `{ r with recovered := true } :: rs`,
but `Q0.panics` is the same constant list in every memory (the chain is not `Q0.priv`-backed), so the chain
cannot change. `PanicRuntime` is not a runtime-parameter type of the round-10 V1 rule, so a statement
could pin `Q0` and claim anything. (The model has no `Laws` instance: the row shows what a PINNED model
would make of the contract, which is why the auditor requires the model to be a free variable.) -/
namespace R11

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

end R11
