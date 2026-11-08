import Extracted

/-!
# `SumSquares(x, y uint64) uint64` returns `x² + y²` (mod `2^64`), calling `square` twice

**Guarantee.** For all 64-bit `x`, `y` and every Go call state `s` of
`example.com/basic.SumSquares` (`x` in `X0`, `y` in `X1`) in which the stack-growth prologue falls
through (`GuardOK s 0`) and `SP` is aligned with `[SP-40, SP+56)` writable (`StackOK s 40 56`:
its frame, the saved frame pointer, and the spill slot of `y` in the caller's frame), the call
returns (never faulting or panicking), obeys the ABI, and `X0 = (x·x + y·y) mod 2^64`.

**How.** `square` is proved once as a callee `Summary` (from any state at its entry it returns
to `X30` with `X0 := X0 · X0`), and the proof of `SumSquares` uses it at both call sites; the
spilled `y` and the first square are kept in the stack frame across the calls.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem square_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.square")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56)
      (fun s s' => s' = { s with regs := setReg s.regs 0 (s.regs 0 * s.regs 0),
                                 pc := s.regs 30 }) := by
  intro s hpc ⟨h1, h2⟩
  janus_run

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y]
      (fun s => GuardOK s 0 ∧ StackOK s 40 56)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat * x.toNat + y.toNat * y.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hal, hb, ha, hw⟩
  janus_intro hs
  janus_run calls [square_summary]
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
  { regs := fun i => if i = 0 then (2) else if i = 1 then (3) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(2 : BitVec 64), (3 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (GuardOK s 0 ∧ StackOK s 40 56) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = (x.toNat * x.toNat + y.toNat * y.toNat) % 2 ^ 64)) := by
  refine ⟨ret, s0, (2), (3), hret, setup, ?pre, correctness (2) (3) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
