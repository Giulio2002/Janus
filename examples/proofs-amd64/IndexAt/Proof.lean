import Janus
import Extracted

/-! `example.com/basic.IndexAt(xs, i)` on amd64: out of range (`len ≤ i`, unsigned) panics with a
runtime bounds error (reaches `runtime.panicBounds`). Example 4 of docs/COVERAGE.md R6. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.PanicAmd64

theorem correctness (P : Spec.PanicRuntime) (ptr len cap i : BitVec 64) (hi : len.toNat ≤ i.toNat) :
    EnsuresGo Extracted.program Extracted.entry [ptr, len, cap, i]
      (fun s => StackWritable s 16 24)
      (fun _ => goClass P)
      (fun _ _ => True)
      (fun _ v _ => v = P.boundsError) := by
  intro ret hret s hs ⟨hle, hnw, hacc⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  refine GoReturns.of_reaches ?_
  janus64_run
  exact ⟨P.boundsError, goClass_panicStub P _ rfl (by decide), rfl⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The panic runtime: the model with an empty funcs table. -/
def PW : Spec.PanicRuntime := Janus.Contracts.PanicModel.P0 [] Janus.Contracts.PanicSatAmd64.RPa

def ptr : BitVec 64 := 0x30800#64
def len : BitVec 64 := 4#64
def cap : BitVec 64 := 4#64
def i : BitVec 64 := 4#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then ptr else if r_ = 3 then len else if r_ = 1 then cap else if r_ = 7 then i else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : (fun s : State => StackWritable s 16 24) s0 := by
  dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

theorem hyps : (len.toNat ≤ i.toNat) := by decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (P : Janus.Spec.PanicRuntime) (ptr : BitVec 64) (len : BitVec 64) (cap : BitVec 64) (i : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i] s ∧ (len.toNat ≤ i.toNat) ∧ (StackWritable s 16 24) ∧
    GoReturns (Extracted.program.withExit ret) (goClass P) s fun o =>
    match o with
    | .returned s' => ABIReturn s s' ∧ (True)
    | .panicked v s' => v = P.boundsError
    | .goexited _ => False :=
  ⟨ret, s0, PW, ptr, len, cap, i, hret, setup, hyps, hpre, correctness PW ptr len cap i hyps ret hret s0 setup hpre⟩

end Witness

end Proof
