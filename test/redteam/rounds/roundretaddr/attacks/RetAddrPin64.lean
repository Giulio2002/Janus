import Extracted

/-!
# Preconditions that pin the caller's return address `[RSP]` (amd64), v0.4.0

Round retaddr. Before v0.4.0 `Ensures` evaluated its precondition on the call state with the return address already
written at `[RSP]`, so a precondition could restrict the caller's return address (to `0`: a jump to a nil code pointer
counted as a return) and the auditor tried to catch the spellings syntactically (the `[RSP]`-word rule; probes
`RspBypass64.lean` of v0.3.3 found seven accepted bypasses). Now the precondition is evaluated on the state BEFORE
`State.setRet` writes the return address, so a statement about `[RSP]` is a statement about the word the stack held
before the call, which the call overwrites: it restricts nothing. Every row is verified (audit-only) and harmless.
Statements are vacuous on purpose (`∧ False`): only the audit verdict is under test. The Lean-level meaning is proved in
`test/lean/JanusTests/RetAddr.lean` (m1-m10).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- c1: alias through an existential and an equation. -/
theorem c1 : Ensures Extracted.program Extracted.entry []
    (fun s => (∃ sp, (s.regs 4).toNat = sp ∧ s.mem.readLE sp 8 = 0) ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- c2: alias through two inequalities. -/
theorem c2 : Ensures Extracted.program Extracted.entry []
    (fun s => (∃ sp, (s.regs 4).toNat ≤ sp ∧ sp ≤ (s.regs 4).toNat ∧ s.mem.readLE sp 8 = 0) ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- c3: the address passed as a parameter to a proof-local definition. -/
def RdZero (m : Memory) (a : Nat) : Prop := m.readLE a 8 = 0

theorem c3 : Ensures Extracted.program Extracted.entry []
    (fun s => RdZero s.mem (s.regs 4).toNat ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- c4: a byte read (`Memory.bytes`). -/
theorem c4 : Ensures Extracted.program Extracted.entry []
    (fun s => (∀ i, i < 8 → s.mem.bytes ((s.regs 4).toNat + i) = 0) ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- c5: `RSP` pinned to a constant, the word read at that constant. -/
theorem c5 : Ensures Extracted.program Extracted.entry []
    (fun s => (s.regs 4).toNat = 0x100000 ∧ s.mem.readLE 0x100000 8 = 0 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.2.elim

/-- c6: a universally quantified alias. -/
theorem c6 : Ensures Extracted.program Extracted.entry []
    (fun s => (∀ sp, sp = (s.regs 4).toNat → s.mem.readLE sp 8 = 0) ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- c7: a let-bound alias. -/
theorem c7 : Ensures Extracted.program Extracted.entry []
    (fun s => (let a := (s.regs 4).toNat; s.mem.readLE a 8 = 0) ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- c8: the memory pinned whole by a closed memory value. -/
def zeroMem (m : Memory) : Memory := { m with bytes := fun _ => 0 }

theorem c8 : Ensures Extracted.program Extracted.entry []
    (fun s => s.mem = zeroMem s.mem ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- d0: the plain read (rejected on every version before v0.4.0). -/
theorem d0 : Ensures Extracted.program Extracted.entry []
    (fun s => s.mem.readLE (s.regs 4).toNat 8 = 0 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- d1: the return address bounded (`ErrorfAmd64.RetLow`'s fact), the n9 b3 spelling. -/
theorem d1 : Ensures Extracted.program Extracted.entry []
    (fun s => s.mem.readLE (s.regs 4).toNat 8 < 70368744177664 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- d2: the same through the same-run bound forms (`EnsuresWithin`, `RunsAtLeastOnCall`) of the statement. -/
theorem d2 : EnsuresWithin (fun _ => 1) Extracted.program Extracted.entry []
    (fun s => s.mem.readLE (s.regs 4).toNat 8 = 0 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

theorem d3 : RunsAtLeastOnCall (fun _ => 0) Extracted.program Extracted.entry []
    (fun s => s.mem.readLE (s.regs 4).toNat 8 = 0 ∧ False) := by
  intro s hs hp ret hret; exact hp.2.elim

/-! v0.4.0 phase 1b: the other main-theorem forms evaluate their precondition before the return address is written too. -/

/-- d4: ABI0 (`Ensures0`). -/
theorem d4 : Janus.Amd64.GoABI0.Ensures0 Extracted.program Extracted.entry [] 0
    (fun s => s.mem.readLE (s.regs 4).toNat 8 = 0 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- d5: the C ABI (`CEnsures`). -/
theorem d5 : Janus.Amd64.CABI.CEnsures Extracted.program Extracted.entry []
    (fun s => s.mem.readLE (s.regs 4).toNat 8 = 0 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- d6: the kernel semantics (`EnsuresK`). -/
theorem d6 (E : Janus.Kernel.KEnv) : Janus.Amd64.Kernel.EnsuresK Extracted.program E Extracted.entry []
    (fun s _ => s.mem.readLE (s.regs 4).toNat 8 = 0 ∧ False) (fun _ _ _ _ => True) := by
  intro s k hs hp ret hret; exact hp.2.elim

/-- d7: the cgo contract forms (`EnsuresC`, `CEnsuresC`). -/
theorem d7 (C : Janus.Amd64.FFI.Contract) : Janus.Amd64.FFI.EnsuresC Extracted.program C Extracted.entry []
    (fun s => s.mem.readLE (s.regs 4).toNat 8 = 0 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

theorem d8 (C : Janus.Amd64.FFI.Contract) : Janus.Amd64.FFI.CEnsuresC Extracted.program C Extracted.entry []
    (fun s => s.mem.readLE (s.regs 4).toNat 8 = 0 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret; exact hp.2.elim

/-- d9: stack growth (`EnsuresGrow64`): a `caller` that pins the return address (`[RSP] = 0`) verifies, and the pin is printed in
the statement's `caller` slot and disclosed by the report (`Assumes of the caller`). -/
theorem d9 (reloc : State → State → Prop) : Janus.Contracts.StackAmd64.EnsuresGrow64 Extracted.program reloc Extracted.entry []
    (fun _ => True) (fun s => s.mem.readLE (s.regs 4).toNat 8 = 0 ∧ False) (fun _ _ => True) := by
  intro s hs hp ret hret hc; exact hc.2.elim

end Proof
