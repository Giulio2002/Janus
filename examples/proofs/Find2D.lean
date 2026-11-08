import Extracted

/-!
# `Find2D(m *[3][3]uint64, x uint64) uint64`: nested loops left by a labeled `break`

**Guarantee.** For every pointer `m` to 72 readable bytes (`Ptr`; the `3×3` array, row-major)
and every 64-bit `x`, and every Go call state of `example.com/basic.Find2D`, the call returns
(never faulting or panicking), obeys the ABI, and `r = X0` is the row-major index `3i + j` of
the first element of `m` equal to `x`, or `9` if there is none: `r ≤ 9`, no element before
position `r` equals `x`, and if `r < 9` the element at position `r` does.

`break outer` jumps from the inner loop past the end of the outer one. Both loops have constant
trip counts, so the counters are literals in every iteration and `janus_run` executes them; the
search has one path per position at which it can stop (ten in all).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (m x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [m, x] (fun s => Ptr s.mem m 72 false)
      (fun s s' => (s'.regs 0).toNat ≤ 9 ∧
        (∀ j < (s'.regs 0).toNat, s.mem.readLE (m.toNat + 8 * j) 8 ≠ x.toNat) ∧
        ((s'.regs 0).toNat < 9 → s.mem.readLE (m.toNat + 8 * (s'.regs 0).toNat) 8 = x.toNat)) := by
  intro ret hret s hs ⟨hp, hp'⟩
  janus_intro hs
  janus_run
  all_goals try refine ⟨?_, fun h => h.elim⟩
  all_goals
    intro j hj
    janus_cases hj
    all_goals (try simp only [Nat.reduceMul, Nat.add_zero]) <;> omega


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (0) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (0 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (m : BitVec 64) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [m, x] s ∧ (Ptr s.mem m 72 false) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat ≤ 9 ∧
        (∀ j < (s'.regs 0).toNat, s.mem.readLE (m.toNat + 8 * j) 8 ≠ x.toNat) ∧
        ((s'.regs 0).toNat < 9 → s.mem.readLE (m.toNat + 8 * (s'.regs 0).toNat) 8 = x.toNat))) := by
  refine ⟨ret, s0, (0x300000), (0), hret, setup, ?pre, correctness (0x300000) (0) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
