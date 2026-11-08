import Extracted

/-!
# `Sum3(a, b, c uint64) uint64`: a variadic call

**Guarantee.** For all 64-bit `a`, `b`, `c` and every Go call state `s` of
`example.com/basic.Sum3` whose stack-growth prologue falls through (`GuardOK s 0`, the guard
word outside the stack window) and whose `SP` is aligned with `[SP-80, SP)` writable, the call
returns (never faulting or panicking), obeys the ABI, and `X0 = a + b + c mod 2^64`.

**What is exercised.** `sumv(a, b, c)` passes the variadic arguments as a slice: the compiler
stores `a`, `b`, `c` in a `[3]uint64` in `Sum3`'s frame (it does not escape, so no allocation)
and passes `(&arr, 3, 3)` in `X0`–`X2`. `sumv` is an ordinary `range` loop over that slice; with
the literal length 3 the executor runs it to the end.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (a b c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, c]
      (fun s => GuardOK s 0 ∧ StackOK s 80 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 80) 80)
      (fun _ s' => (s'.regs 0).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hgd
  janus_run
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
theorem nonvacuous : ∃ (ret : Nat) (s : State) (a : BitVec 64) (b : BitVec 64) (c : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b, c] s ∧ (GuardOK s 0 ∧ StackOK s 80 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 80) 80) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64)) := by
  refine ⟨ret, s0, (1), (2), (3), hret, setup, ?pre, correctness (1) (2) (3) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
