import Extracted

/-!
# `PanicIf(x uint64, e any) uint64` returns or panics with `e` (arm64)

**Guarantee (example 1 of docs/COVERAGE.md R6).** `PanicIf` is `if x > 10 { panic(e) }; return x+1`.
The argument `e` is an empty interface (`any`), so `panic(e)` passes it straight to
`runtime.gopanic`. For every `x`, every interface value `e = (etyp, edata)` in `X1`/`X2`, every
panic-runtime model `P`, every admissible return address and every Go call state in which the
stack-growth prologue falls through and the frame is writable:

* if `x ≤ 10` (unsigned, as the compiled `cmp $10; b.hi` checks) the call **returns** `x + 1`;
* if `x > 10` the call **panics** with exactly the interface value `e` — it reaches
  `runtime.gopanic` with `e`'s type word in `X0` and data word in `X1`, which `goClass`
  classifies as `.panicked ⟨etyp, edata⟩`.

This is the literal `panic(v) → .panicked v`, the `.panicked`/`.returned` cases of `EnsuresGo`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Panic

namespace Proof

theorem correctness (P : PanicRuntime) (x etyp edata : BitVec 64) :
    EnsuresGo Extracted.program Extracted.entry [x, etyp, edata]
      (fun s => GuardOK s 0 ∧ StackOK s 40 32)
      (fun _ => goClass P)
      (fun _ s' => x.toNat ≤ 10 → s'.regs 0 = x + 1)
      (fun _ v _ => 10 < x.toNat → v = ⟨etyp.toNat, edata.toNat⟩) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩⟩
  janus_intro hs
  refine GoReturns.of_reaches ?_
  by_cases hx : x.toNat ≤ 10
  · -- x ≤ 10: returns x + 1
    janus_run
    exact fun _ => trivial
  · -- x > 10: panics with e
    have hx' : 10 < x.toNat := by omega
    janus_run
    refine ⟨⟨etyp.toNat, edata.toNat⟩, ?_, ?_⟩
    · show (⟨etyp.toNat, edata.toNat⟩ : Eface) = ⟨_, _⟩
      simp [setReg]
    · first | (intro _; rfl) | rfl | trivial

namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000


def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then (5) else if i = 1 then (7) else if i = 2 then (9) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(5 : BitVec 64), (7 : BitVec 64), (9 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩
def PW : PanicRuntime := Janus.Contracts.PanicModel.P0 [] Janus.Contracts.PanicSat.RPa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (P : PanicRuntime) (x etyp edata : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, etyp, edata] s ∧ (GuardOK s 0 ∧ StackOK s 40 32) ∧
    GoReturns (Extracted.program.withExit ret) (goClass P) s fun o =>
    match o with
    | .returned s' => ABIReturn s s' ∧ (x.toNat ≤ 10 → s'.regs 0 = x + 1)
    | .panicked v s' => 10 < x.toNat → v = ⟨etyp.toNat, edata.toNat⟩
    | .goexited _ => False := by
  refine ⟨ret, s0, PW, (5), (7), (9), hret, setup, ?pre, correctness PW (5) (7) (9) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Disjoint, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
