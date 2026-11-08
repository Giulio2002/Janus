import Extracted

/-!
# `Add128(xh, xl, yh, yl uint64) (hi, lo uint64)` is 128-bit addition

**Guarantee.** For all 64-bit `xh, xl, yh, yl` and every Go call state of
`example.com/basic.Add128` with the arguments in `X0`–`X3`, the compiled code (an `adds`/`adcs`
carry chain) returns (never faulting or panicking), obeys the ABI, and the results `hi = X0`, `lo = X1` satisfy
`hi·2^64 + lo = (X + Y) mod 2^128` where `X = xh·2^64 + xl` and `Y = yh·2^64 + yl`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (xh xl yh yl : BitVec 64) :
    Ensures Extracted.program Extracted.entry [xh, xl, yh, yl] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat * 2 ^ 64 + (s'.regs 1).toNat =
        ((xh.toNat * 2 ^ 64 + xl.toNat) + (yh.toNat * 2 ^ 64 + yl.toNat)) % 2 ^ 128) := by
  intro ret hret s hs _
  janus_intro hs
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
  { regs := fun i => if i = 0 then (1) else if i = 1 then (2) else if i = 2 then (3) else if i = 3 then (4) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(1 : BitVec 64), (2 : BitVec 64), (3 : BitVec 64), (4 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (xh : BitVec 64) (xl : BitVec 64) (yh : BitVec 64) (yl : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [xh, xl, yh, yl] s ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat * 2 ^ 64 + (s'.regs 1).toNat =
        ((xh.toNat * 2 ^ 64 + xl.toNat) + (yh.toNat * 2 ^ 64 + yl.toNat)) % 2 ^ 128)) := by
  refine ⟨ret, s0, (1), (2), (3), (4), hret, setup, ?pre, correctness (1) (2) (3) (4) ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp] <;> decide

end Witness

end Proof
