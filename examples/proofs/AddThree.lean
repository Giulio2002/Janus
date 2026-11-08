import Extracted

/-!
# `AddThree(x, y, z uint64) uint64` returns `x + y + z`, by composing two calls to `Add`

**Guarantee.** For all 64-bit `x`, `y`, `z` and every Go call state `s` of
`example.com/basic.AddThree` (arguments in `X0`–`X2`) in which the stack-growth prologue falls
through (`GuardOK s 0`) and `SP` is aligned with `[SP-40, SP+32)` writable (`StackOK s 40 32`:
its 32-byte frame, the saved frame pointer, and the spill slot of `z` in the caller's frame),
the call returns (never faulting or panicking), obeys the ABI, and `X0 = (x + y + z) mod 2^64`.

**How.** The callee `Add` (extracted with `AddThree`) is proved once, from *any* state at its
entry, as a `Summary`: it returns to `X30` with `X0 := X0 + X1` and nothing else changed. The
proof of `AddThree` executes its own instructions and uses that summary at both `bl Add`s; the
callee's code is not re-executed.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- `Add` as a callee: from any state at its entry with a well-formed return address in `X30`
(4-aligned, below the top-byte range), it returns there with `X0 = X0 + X1`. -/
theorem add_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.Add")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56)
      (fun s s' => s' = { s with regs := setReg s.regs 0 (s.regs 0 + s.regs 1),
                                 pc := s.regs 30 }) := by
  intro s hpc ⟨h1, h2⟩
  janus_run

theorem correctness (x y z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y, z]
      (fun s => GuardOK s 0 ∧ StackOK s 40 32)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat + z.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hal, hb, ha, hw⟩
  janus_intro hs
  janus_run calls [add_summary]
  janus_arith


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (1) else if i = 1 then (2) else if i = 2 then (3) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(1 : BitVec 64), (2 : BitVec 64), (3 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y, z] s ∧ (GuardOK s 0 ∧ StackOK s 40 32) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = (x.toNat + y.toNat + z.toNat) % 2 ^ 64)) := by
  refine ⟨ret, s0, (1), (2), (3), hret, setup, ?pre, correctness (1) (2) (3) ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp] <;> decide

end Witness

end Proof
