import Extracted

/-!
# `Max(x, y uint64) uint64` returns the larger argument

**Guarantee.** For all 64-bit `x`, `y` and every Go call state of `example.com/basic.Max` with
`x` in `X0` and `y` in `X1` (everything else arbitrary), the compiled code returns (never faulting or panicking), obeys the
ABI (`SP`, `X18`, `X28`, `X29` restored), and `X0` holds `x` if `x > y` (unsigned) and `y`
otherwise. Both sides of the compiled branch (`cmp x1, x0; b.cs`) are covered.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega


/-- SPEED: every call returns after executing at most 4 instructions (`CMP; B.cond; MOV; RET` on the longer path). The
unit is instructions of the model, not cycles (docs/SOUNDNESS.md, "Instruction-count bounds"). -/
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega

/-- SPEED (lower bound): every call executes at least 3 instructions before it returns (`CMP; B.cond; RET` on the shorter path). -/
theorem atLeast (x y : BitVec 64) :
    RunsAtLeastOnCall (fun _ => 3) Extracted.program Extracted.entry [x, y] (fun _ => True) := by
  intro ret hret s hs _
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
  { regs := fun i => if i = 0 then (3) else if i = 1 then (5) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(3 : BitVec 64), (5 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.regs 0 = if y.toNat < x.toNat then x else y)) := by
  refine ⟨ret, s0, (3), (5), hret, setup, ?pre, correctness (3) (5) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `within` is not vacuous: a concrete call (`Max(3, 5)`, the longer path) returns within 4 instructions with the guarantee. -/
theorem within : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) ∧
    (ReturnsWithin 4 (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.regs 0 = if y.toNat < x.toNat then x else y)) :=
  ⟨ret, s0, (3), (5), hret, setup, trivial, Proof.within (3) (5) ret hret s0 setup trivial⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `atLeast` is not vacuous: the same call is still running after 3 instructions and returns. -/
theorem atLeast : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) ∧
    RunsAtLeast 3 (Extracted.program.withExit ret) s ∧
    (Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s') :=
  ⟨ret, s0, (3), (5), hret, setup, trivial, Proof.atLeast (3) (5) ret hret s0 setup trivial,
    (Proof.correctness (3) (5) ret hret s0 setup trivial).mono fun _ h => h.1⟩

end Witness

end Proof
