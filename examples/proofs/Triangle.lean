import Extracted

/-!
# `Triangle(n uint64) uint64`: an expression switch with `fallthrough`, compiled to a jump table

**Guarantee.** For every 64-bit `n` and every Go call state of `example.com/basic.Triangle` whose
memory holds the function's read-only jump table (`DataLoaded`), the call returns (never faulting
or panicking), obeys the ABI, and `X0` is the triangular number `n·(n+1)/2 = 0 + 1 + … + n` when
`n ≤ 8`, and `0` otherwise.

The nine dense cases become a bounds check (`cmp x0, #8; b.hi default`) and an indirect jump
through a table of code addresses in `.rodata` (`ldr x27, [x1, x0, lsl #3]; br x27`). The
`fallthrough` chain becomes straight-line code that each case enters at a different point. The
proof splits on the nine in-range values, for each of which the jump target is read from the
extracted table.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n]
      (fun s => Extracted.program.DataLoaded s.mem)
      (fun _ s' => (s'.regs 0).toNat = if n.toNat ≤ 8 then n.toNat * (n.toNat + 1) / 2 else 0) := by
  intro ret hret s hs hd
  janus_intro hs
  janus_data hd
  by_cases hn : n.toNat ≤ 8
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 9 ∧ n = BitVec.ofNat 64 k :=
      ⟨n.toNat, by omega, by simp⟩
    janus_cases hk
    all_goals janus_run
  · janus_run
    simp [hn]


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def wbytes (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (4) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(4 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [n] s ∧ (Extracted.program.DataLoaded s.mem) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = if n.toNat ≤ 8 then n.toNat * (n.toNat + 1) / 2 else 0)) := by
  refine ⟨ret, s0, (4), hret, setup, ?pre, correctness (4) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, dataByte, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
