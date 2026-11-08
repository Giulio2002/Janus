import Extracted

/-!
# `DeferAdd(x, y uint64) (r uint64)` returns `x + y` through an open-coded `defer`

**Guarantee.** For all `x`, `y` and every Go call state `s` of `example.com/basic.DeferAdd` in
which the stack-growth prologue falls through and `[SP-72, SP)` is writable with `SP` aligned,
the call returns, obeys the ABI, and `X0 = (x + y) mod 2^64`: the function sets `r = x`, and the
deferred closure (which captured `&r` and `y`) runs at the exit and adds `y` to `r` before it is
returned.

**How.** Go 1.26 open-codes this defer: the closure's funcval lives in the frame (with a
`deferBits` byte, which the panic path consults), and the exit clears the byte and calls the
closure with `BLR` (context `X26` = the funcval).
The closure is built by the code being proved, so the call target is read back from the stack
and no hypothesis is needed; `janus_run` executes the closure inline. The function also contains
`bl runtime.deferreturn`, reached only when a panic is recovered (out of scope, see
docs/SOUNDNESS.md): the extractor does not copy it (`omittedCalls` in `identity.json`), and the
theorem shows it is not reached.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun s => GuardOK s 0 ∧ StackOK s 72 0)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hal, hb, ha, hw⟩
  janus_intro hs
  janus_run


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (1) else if i = 1 then (2) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(1 : BitVec 64), (2 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (GuardOK s 0 ∧ StackOK s 72 0) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64)) := by
  refine ⟨ret, s0, (1), (2), hret, setup, ?pre, correctness (1) (2) ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp] <;> decide

end Witness

end Proof
