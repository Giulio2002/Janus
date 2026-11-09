import Extracted

/-!
# `ErrorfAmd64.RetLow` smuggled into a consumer's statement (amd64)

Round n9. The auditor rejects a statement that states `[RSP] < 2^k` (k <= 46) of the caller. Each row spells that fact
differently. Statements are vacuous on purpose (`... ∧ False`): only the shape of the precondition is under test.
The guard is semantic: ANY top-level precondition that reads the word at the entry `RSP`, after unfolding definitions, is rejected
(a bound on the caller's return address weakens the guarantee without the reader seeing it). Every row must FAIL.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

def MyLow (s : State) : Prop := s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 46
abbrev MyLow2 (s : State) : Prop := Janus.Contracts.ErrorfAmd64.RetLow s

/-- b1: a proof-local alias of the hand-written bound. -/
theorem b1 : Ensures Extracted.program Extracted.entry [] (fun s => MyLow s ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

/-- b2: an alias of `RetLow` itself. -/
theorem b2 : Ensures Extracted.program Extracted.entry [] (fun s => MyLow2 s ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

/-- b3: the bound as a numeral (2^46). -/
theorem b3 : Ensures Extracted.program Extracted.entry [] (fun s => s.mem.readLE (s.regs 4).toNat 8 < 70368744177664 ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

/-- b4: a smaller bound (2^40, a Go binary's real bound) is the same restriction. -/
theorem b4 : Ensures Extracted.program Extracted.entry [] (fun s => s.mem.readLE (s.regs 4).toNat 8 ≤ 2 ^ 40 ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

/-- b5 (was a gap of the syntactic guard): `+ 1 ≤ 2^46`. -/
theorem b5 : Ensures Extracted.program Extracted.entry [] (fun s => s.mem.readLE (s.regs 4).toNat 8 + 1 ≤ 2 ^ 46 ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

/-- b6 (was a gap): through an existential. -/
theorem b6 : Ensures Extracted.program Extracted.entry [] (fun s => (∃ r, r < 2 ^ 46 ∧ s.mem.readLE (s.regs 4).toNat 8 = r) ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

/-- b7: division. -/
theorem b7 : Ensures Extracted.program Extracted.entry [] (fun s => s.mem.readLE (s.regs 4).toNat 8 / 2 ^ 46 = 0 ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

/-- b8 (CONTROL, must verify): the framework's standard ABI precondition `CallOK64` (which says `[RSP]` is the return address) used as-is. -/
theorem b8 : Ensures Extracted.program Extracted.entry [] (fun s => Janus.Contracts.CallOK64 s 4096 0 ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

def Wrap (s : State) : Prop := Janus.Contracts.CallOK64 s 4096 0 ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 46

/-- b9: a user definition wrapping `CallOK64` plus an extra bound on the return address. -/
theorem b9 : Ensures Extracted.program Extracted.entry [] (fun s => Wrap s ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

/-- b10: the read hidden behind a core-looking name (`Nat.sneak`, declared in this proof file, not in `Init`): opacity is by the
defining module, never by name. -/
def Nat.sneak (s : State) : Prop := s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 46

theorem b10 : Ensures Extracted.program Extracted.entry [] (fun s => Nat.sneak s ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

/-- b11: the read hidden behind an ABI-looking name in the framework's root namespace, declared in this proof file: only the
exact framework names are the ABI predicates. -/
def Janus.Sneak.CallSetup (s : State) : Prop := s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 46

theorem b11 : Ensures Extracted.program Extracted.entry [] (fun s => Janus.Sneak.CallSetup s ∧ False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.2.elim

end Proof
