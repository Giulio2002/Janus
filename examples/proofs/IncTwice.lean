import Extracted

/-!
# `IncTwice(c *Counter, d uint64) uint64`: static calls of a pointer-receiver method

**Guarantee.** For every pointer `c` to 8 writable bytes (`c.N`) outside the stack window and
every 64-bit `d`, and every Go call state `s` of `example.com/basic.IncTwice` whose stack-growth
prologue falls through (`GuardOK s 0`, the guard word outside the window) and whose `SP` is
aligned with `[SP-56, SP+24)` writable (the frame, and the spill slots of `c` and `d` in the
caller's frame), the call returns (never faulting or panicking), obeys the ABI, and with `N` the
value of `c.N` before the call: afterwards `c.N = N + 2d` and `X0 = (N + d) + (N + 2d)`, all
modulo `2^64`.

`c.Inc(d)` with `c` a pointer is a direct `bl` to `(*Counter).Inc` with the receiver in `X0`;
the second call sees the first one's store.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (c d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [c, d]
      (fun s => Ptr s.mem c 8 true ∧ GuardOK s 0 ∧ StackOK s 56 24 ∧
        Disjoint c.toNat 8 (s.sp.toNat - 56) 80 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 56) 80 ∧ Disjoint c.toNat 8 ((s.regs 28).toNat + 16) 8)
      (fun s s' => s'.mem.readLE c.toNat 8 = (s.mem.readLE c.toNat 8 + 2 * d.toNat) % 2 ^ 64 ∧
        (s'.regs 0).toNat = ((s.mem.readLE c.toNat 8 + d.toNat) + (s.mem.readLE c.toNat 8 + 2 * d.toNat)) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hc, hc'⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hgd, hcg⟩
  janus_intro hs
  simp only [Disjoint] at hd hgd hcg
  janus_run
  constructor <;> omega


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (1) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (1 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (c : BitVec 64) (d : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [c, d] s ∧ (Ptr s.mem c 8 true ∧ GuardOK s 0 ∧ StackOK s 56 24 ∧
        Disjoint c.toNat 8 (s.sp.toNat - 56) 80 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 56) 80 ∧ Disjoint c.toNat 8 ((s.regs 28).toNat + 16) 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.mem.readLE c.toNat 8 = (s.mem.readLE c.toNat 8 + 2 * d.toNat) % 2 ^ 64 ∧
        (s'.regs 0).toNat = ((s.mem.readLE c.toNat 8 + d.toNat) + (s.mem.readLE c.toNat 8 + 2 * d.toNat)) % 2 ^ 64)) := by
  refine ⟨ret, s0, (0x300000), (1), hret, setup, ?pre, correctness (0x300000) (1) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
