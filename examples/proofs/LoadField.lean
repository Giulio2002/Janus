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
  have hfetch : (Extracted.program.withExit ret).fetch s.pc.toNat = some 0xf9400000 := by
    rw [hpcn]; rfl
  have hmi : memIndexed s 0 (BitVec.ofNat 64 (0 * 2 ^ 3)) false false
      (fun s a => memSingle s 3 1 0 a) = .error (.outsideAllocation 0 8) := by
    unfold memIndexed baseAddr memSingle load
    simp only [reduceIte, Nat.reduceEqDiff, Bool.false_eq_true, ite_false, h0]
    rw [show ((0#64 : BitVec 64) + BitVec.ofNat 64 (0 * 2 ^ 3)).toNat = 0 from by decide,
      show (2 : Nat) ^ 3 = 8 from rfl, hna]
    rfl
  have hstep : Arm64.step 0xf9400000 s = .error (.outsideAllocation 0 8) := by
    rw [step_of_decode (i := .ldstUImm 3 1 0 0 0) (by decide)]
    simp only [exec, hmi]
  refine GoReturns.fault (Program.Steps.refl s) ⟨?_, ?_, 0xf9400000, hfetch, hstep⟩
    (goClass_nil P s (by decide)) rfl
  · -- the entry pc is not the (external) return address
    rw [hpcn, Program.exitAddr_withExit]
    exact hret.ne_of_fetch (pc := Extracted.entry) (w := 0xf9400000) (by rfl)
  · -- no stub at the entry
    rw [hpcn]; rfl

end Proof
