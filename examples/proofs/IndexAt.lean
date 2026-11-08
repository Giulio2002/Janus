import Extracted

/-!
# `IndexAt(xs []uint64, i int) uint64` panics out of range (arm64)

**Guarantee (example 4 of docs/COVERAGE.md R6).** For every slice header `(ptr, len, cap)` in
`X0`–`X2`, index `i` in `X3`, every panic-runtime model `P`, every admissible return address and
every Go call state of `example.com/basic.IndexAt` in which the stack-growth prologue falls
through and the frame is writable:

* if `len ≤ i` (unsigned, as the compiled `cmp; b.cs` checks), the call **panics** with a
  `runtime.Error` of kind `bounds` (`P.boundsError`), whatever the buffer — it reaches
  `runtime.panicBounds`, the Go bounds-check panic;
* if `i < len` and the `8·len` bytes at `ptr` are readable and disjoint from the stack window,
  the call **returns** `xs[i]` (never panics).

The two outcomes are the `.panicked`/`.returned` cases of `EnsuresGo` (`Janus.GoABI`): the
classification is `Janus.Contracts.Panic.goClass P`, which sends the `runtime.panicBounds` stub
to the model's bounds error (`panicStubErr`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Panic

namespace Proof

theorem correctness (P : PanicRuntime) (ptr len cap i : BitVec 64) :
    EnsuresGo Extracted.program Extracted.entry [ptr, len, cap, i]
      (fun s => GuardOK s 0 ∧ StackOK s 24 16 ∧
        (len.toNat ≤ i.toNat ∨
          (i.toNat < len.toNat ∧ Ptr s.mem ptr (8 * len.toNat) false ∧
            Disjoint ptr.toNat (8 * len.toNat) (s.sp.toNat - 24) 40)))
      (fun _ => goClass P)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE (ptr.toNat + 8 * i.toNat) 8)
      (fun _ v _ => v = P.boundsError) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hcase⟩
  janus_intro hs
  refine GoReturns.of_reaches ?_
  rcases hcase with hi | ⟨hi, ⟨hp, hp'⟩, hd⟩
  · -- out of range: reaches runtime.panicBounds
    simp only
    janus_run
    exact ⟨P.boundsError, goClass_panicStub P _ rfl (by decide), rfl⟩
  · -- in range: returns xs[i]
    simp only [Disjoint] at hd
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
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (4) else if i = 2 then (4) else if i = 3 then (1) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (4 : BitVec 64), (4 : BitVec 64), (1 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩
def PW : PanicRuntime := Janus.Contracts.PanicModel.P0 [] Janus.Contracts.PanicSat.RPa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (P : PanicRuntime) (ptr len cap i : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i] s ∧ (GuardOK s 0 ∧ StackOK s 24 16 ∧ (len.toNat ≤ i.toNat ∨ (i.toNat < len.toNat ∧ Ptr s.mem ptr (8 * len.toNat) false ∧ Disjoint ptr.toNat (8 * len.toNat) (s.sp.toNat - 24) 40))) ∧
    GoReturns (Extracted.program.withExit ret) (goClass P) s fun o =>
    match o with
    | .returned s' => ABIReturn s s' ∧ ((s'.regs 0).toNat = s.mem.readLE (ptr.toNat + 8 * i.toNat) 8)
    | .panicked v s' => v = P.boundsError
    | .goexited _ => False := by
  refine ⟨ret, s0, PW, (0x300000), (4), (4), (1), hret, setup, ?pre, correctness PW (0x300000) (4) (4) (1) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Disjoint, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
