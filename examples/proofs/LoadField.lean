import Extracted

/-!
# `LoadField(c *Cell) uint64` panics on a nil dereference (arm64)

**Guarantee (example 5 of docs/COVERAGE.md R6).** `LoadField` is `return c.V`, compiled to a bare
`LDR X0, [X0]; RET`. For a nil receiver (`c = 0`) with no memory mapped at address `0`, the load
**faults**: on real hardware a `SIGSEGV` whose fault address is below `0x1000`, which the Go
signal handler turns into a panic with the invalid-memory / nil-pointer error
(`runtime/signal_unix.go`, `sigpanic` → `panicmem`). So for every panic-runtime model `P`, every
admissible return address and every call state with `c = 0` and `[0, 8)` not accessible, the call
panics with a `runtime.Error` of kind `mem` (`P.err .mem`).

The outcome is the `.panicked` case of `EnsuresGo` with the signal-delivery classifier
(`Janus.Contracts.Panic.goClass`, `atFault`): a `outsideAllocation` fault at a small address is a
nil-pointer panic.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Panic

namespace Proof

theorem correctness (P : PanicRuntime) :
    EnsuresGo Extracted.program Extracted.entry [0#64]
      (fun s => s.mem.accessible 0 8 false = false)
      (fun _ => goClass P)
      (fun _ _ => False)
      (fun _ v _ => v = P.err ErrKind.mem) := by
  intro ret hret s hs hna
  have h0 : s.regs 0 = 0#64 := hs.args 0 (by decide)
  have hpc : s.pc = BitVec.ofNat 64 Extracted.entry := hs.pc
  have hpcn : s.pc.toNat = Extracted.entry := by
    rw [hpc, BitVec.toNat_ofNat]; rfl
  -- the load at the entry faults (nil dereference)
  have hfetch : (Extracted.program.withExit ret).fetch s.pc.toNat = some (segWord Extracted.program "example.com/basic.LoadField" 0) := by
    rw [hpcn]; rfl
  have hmi : memIndexed s 0 (BitVec.ofNat 64 (0 * 2 ^ 3)) false false
      (fun s a => memSingle s 3 1 0 a) = .error (.outsideAllocation 0 8) := by
    unfold memIndexed baseAddr memSingle load
    simp only [reduceIte, Nat.reduceEqDiff, Bool.false_eq_true, ite_false, h0]
    rw [show ((0#64 : BitVec 64) + BitVec.ofNat 64 (0 * 2 ^ 3)).toNat = 0 from by decide,
      show (2 : Nat) ^ 3 = 8 from rfl, hna]
    rfl
  have hstep : Arm64.step (segWord Extracted.program "example.com/basic.LoadField" 0) s = .error (.outsideAllocation 0 8) := by
    rw [step_of_decode (i := .ldstUImm 3 1 0 0 0) (by decide)]
    simp only [exec, hmi]
  refine GoReturns.fault (Program.Steps.refl s) ⟨?_, ?_, (segWord Extracted.program "example.com/basic.LoadField" 0), hfetch, hstep⟩
    (goClass_nil P s (by decide)) rfl
  · -- the entry pc is not the (external) return address
    rw [hpcn, Program.exitAddr_withExit]
    exact hret.ne_of_fetch (pc := Extracted.entry) (w := (segWord Extracted.program "example.com/basic.LoadField" 0)) (by rfl)
  · -- no stub at the entry
    rw [hpcn]; rfl


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000


def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then (0) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩
def PW : PanicRuntime := Janus.Contracts.PanicModel.P0 [] Janus.Contracts.PanicSat.RPa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (P : PanicRuntime), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s ∧ (s.mem.accessible 0 8 false = false) ∧
    GoReturns (Extracted.program.withExit ret) (goClass P) s fun o =>
    match o with
    | .returned s' => ABIReturn s s' ∧ (False)
    | .panicked v s' => v = P.err ErrKind.mem
    | .goexited _ => False := by
  refine ⟨ret, s0, PW, hret, setup, ?pre, correctness PW ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Disjoint, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
