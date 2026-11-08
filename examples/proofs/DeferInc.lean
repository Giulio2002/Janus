import Extracted

/-!
# `DeferInc(p *uint64, x uint64) uint64` runs an open-coded defer on return (arm64)

**Guarantee (example 2 of docs/COVERAGE.md R6).** `DeferInc` is `defer func(){ *p++ }(); return x`.
Go 1.26 open-codes the defer: the closure's funcval is built in the frame (with a `deferBits`
byte), and at the normal exit the function clears the byte and calls the closure with `BLR`
(context `X26` = the funcval, which captured `p`). For every `p`, `x`, every panic-runtime
model `P`, every admissible return address and every Go call state in which the stack-growth
prologue falls through, the 64-byte frame is writable, and `p` points at a writable word
disjoint from that frame, the call **returns** `x` and, as a side effect of the deferred closure
having run, the word at `p` is incremented by one. It never panics, so this is `EnsuresGo` with
the panic outcome ruled out — an `Ensures` lifted by `Ensures.toGo`.

The deferred closure is extracted (`DeferInc.func1`, inferred as a computed code address) and run
inline by `janus_run`; the `bl runtime.deferreturn` that `DeferInc` also contains is reached only
after a recovered panic (out of scope here) and is omitted from the extraction.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Panic

namespace Proof

theorem correctness (P : PanicRuntime) (p x : BitVec 64) :
    EnsuresGo Extracted.program Extracted.entry [p, x]
      (fun s => GuardOK s 0 ∧ StackOK s 72 0 ∧ Ptr s.mem p 8 true ∧
        Disjoint p.toNat 8 (s.sp.toNat - 72) 72)
      (fun _ => goClass P)
      (fun s s' => (s'.regs 0).toNat = x.toNat ∧
        s'.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64)
      (fun _ _ _ => False) := by
  apply Ensures.toGo
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hp, hp'⟩, hd⟩
  simp only [Disjoint] at hd
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
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (5) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (5 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩
def PW : PanicRuntime := Janus.Contracts.PanicModel.P0 [] Janus.Contracts.PanicSat.RPa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (P : PanicRuntime) (p x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [p, x] s ∧ (GuardOK s 0 ∧ StackOK s 72 0 ∧ Ptr s.mem p 8 true ∧ Disjoint p.toNat 8 (s.sp.toNat - 72) 72) ∧
    GoReturns (Extracted.program.withExit ret) (goClass P) s fun o =>
    match o with
    | .returned s' => ABIReturn s s' ∧ ((s'.regs 0).toNat = x.toNat ∧ s'.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64)
    | .panicked v s' => False
    | .goexited _ => False := by
  refine ⟨ret, s0, PW, (0x300000), (5), hret, setup, ?pre, correctness PW (0x300000) (5) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Disjoint, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
