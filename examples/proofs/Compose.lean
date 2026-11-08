import Extracted

/-!
# `Compose(a, b, x uint64) uint64`: a non-escaping closure

**Guarantee.** For all 64-bit `a`, `b`, `x` and every Go call state `s` of
`example.com/basic.Compose` whose stack-growth prologues (of `Compose` and of the callee `twice`)
fall through (`GuardOK s 64`, the guard word outside the stack window) and whose `SP` is aligned
with `[SP-112, SP)` writable (`StackOK`), the call returns (never faulting or panicking), obeys
the ABI, and `X0 = f(f(x)) = a·(a·x + b) + b mod 2^64` for the closure `f(v) = a·v + b`.

**What is exercised.** The closure captures `a` and `b`; escape analysis keeps it on the stack,
so `Compose` builds the funcval (the code address of `Compose.func1`, then `a`, `b`) in its own
frame, with no call to the allocator. `twice` calls it twice through `blr` with the context
register `X26` pointing at it, and `Compose.func1` reads the captured variables through `X26`.
Everything the indirect calls depend on is written by the code being proved, so the theorem
needs no hypothesis about the closure.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (a b x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, x]
      (fun s => GuardOK s 64 ∧ StackOK s 112 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 112) 112)
      (fun _ s' => (s'.regs 0).toNat = (a.toNat * (a.toNat * x.toNat + b.toNat) + b.toNat) % 2 ^ 64) := by
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
  { regs := fun i => if i = 0 then (2) else if i = 1 then (3) else if i = 2 then (4) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(2 : BitVec 64), (3 : BitVec 64), (4 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (a : BitVec 64) (b : BitVec 64) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b, x] s ∧ (GuardOK s 64 ∧ StackOK s 112 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 112) 112) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = (a.toNat * (a.toNat * x.toNat + b.toNat) + b.toNat) % 2 ^ 64)) := by
  refine ⟨ret, s0, (2), (3), (4), hret, setup, ?pre, correctness (2) (3) (4) ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp] <;> decide

end Witness

end Proof
