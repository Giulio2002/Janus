import Janus
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic
  Janus.Contracts.PanicSat

/-! Round 11 P1a (model row): `GorecoverContract` for a CLOSED `PanicRuntime` `Q0` in which no
panic is ever recorded as active (`Calm := True`) and every panic carries the type word 1
(`Panicking … v … := v.typ = 1`, no wrappers) holds of no program: `recover()` would have to
return `nil` (`Calm`) and the value of the panic (`Panicking`) at once. `PanicRuntime` is not a
runtime-parameter type of the round-10 V1 rule, so a statement could pin `Q0` and claim anything. -/
namespace R11

def Q0 : PanicRuntime where
  err := fun _ => ⟨1, 0⟩
  priv := []
  depth := 64
  Env := fun _ => True
  Panicking := fun _ _ v _ => v.typ = 1
  Calm := fun _ _ => True
  Recovered := fun _ _ => True
  wrapper := fun _ => False

def st (addr : Nat) : State := { wstate with pc := BitVec.ofNat 64 addr }

@[simp] theorem Q0_depth : Q0.depth = 64 := rfl

theorem pre0 (addr : Nat) : PanicPre Q0 0 (st addr) := by
  have hsp : (st addr).sp = BitVec.ofNat 64 wsp := rfl
  have hg28 : (st addr).regs 28 = BitVec.ofNat 64 wg := rfl
  have h30 : (st addr).regs 30 = BitVec.ofNat 64 wret := rfl
  have hm : (st addr).mem = wmem := rfl
  refine ⟨trivial, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, hg28]; decide
  · simp only [regG, stackguard0Offset, hg28, hm]; decide
  · simp only [stackguard0, regG, stackguard0Offset, hg28, hm, hsp, Q0_depth]; decide
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [hsp]; decide
  · simp only [hsp, Q0_depth]; decide
  · decide
  · simp only [hsp, Q0_depth]; rw [BitVec.toNat_ofNat]; simp only [wsp]; omega
  · simp only [hsp, hm, Q0_depth]
    refine Memory.accessible_mono _
      (show wmem.accessible (wsp - 64) (64 + 8 + 8 * 0) true = true by decide) ?_ ?_
    · rw [BitVec.toNat_ofNat]; simp [wsp]
    · rw [BitVec.toNat_ofNat]; simp only [wsp]; omega
  · simp [Q0, Outside]

theorem unsat (p : Program) (addr : Nat) : ¬ GorecoverContract p addr Q0 := by
  intro h
  obtain ⟨k, s', -, -, -, hcalm, hpan⟩ :=
    h (st addr) (by simp [st]) ⟨pre0 addr, by show wstate.mem.accessible ((wstate.regs 29).toNat + 8) 8 false = true; decide,
      by show (wstate.regs 29).toNat + 16 ≤ 2 ^ 48; decide⟩
  have h0 := (hcalm trivial).1
  have h1 := (hpan ⟨1, 0⟩ ((st addr).mem.readLE ((( st addr).regs 29).toNat + 8) 8) rfl (fun h => h) rfl).1
  rw [h0] at h1
  simp at h1

end R11
