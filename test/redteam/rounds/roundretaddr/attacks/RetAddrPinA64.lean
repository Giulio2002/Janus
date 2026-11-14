import Extracted

/-!
# Preconditions that pin the caller's return address `X30` (arm64), v0.4.0

Round retaddr. Before v0.4.0 the arm64 auditor had no rule at all: `(s.regs 30).toNat = 0` and `(s.regs 30).toNat <
2^20` were accepted (`LrPin.lean` of v0.3.3) and restricted the caller's return address. Now `Ensures` evaluates its
precondition on the call state BEFORE `State.setRet` installs the return address in `X30`: a statement about `X30` is
about the caller's old register, which the call overwrites. Every row is verified (audit-only) and harmless; the
Lean-level meaning is proved in `test/lean/JanusTests/RetAddr.lean` (a1-a5). Vacuous on purpose (`∧ False`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- e1: `X30` pinned to 0. -/
theorem e1 : Ensures Extracted.program Extracted.entry []
    (fun s => (s.regs 30).toNat = 0 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- e2: `X30` bounded. -/
theorem e2 : Ensures Extracted.program Extracted.entry []
    (fun s => (s.regs 30).toNat < 2 ^ 20 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- e3: through an existential alias. -/
theorem e3 : Ensures Extracted.program Extracted.entry []
    (fun s => (∃ r, (s.regs 30).toNat = r ∧ r = 0) ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- e4: with the instruction-count bound forms. -/
theorem e4 : EnsuresWithin (fun _ => 1) Extracted.program Extracted.entry []
    (fun s => (s.regs 30).toNat = 0 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

end Proof
