import Janus
import Extracted

/-! `example.com/basic.DeferInc(p, x)` on amd64: returns `x` and an open-coded deferred closure
increments `*p` on the normal return path. Example 2 of docs/COVERAGE.md R6 (an `Ensures` lifted
by `Ensures.toGo`: it never panics). -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.PanicAmd64

theorem correctness (P : Spec.PanicRuntime) (p x : BitVec 64) :
    EnsuresGo Extracted.program Extracted.entry [p, x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 64 48 ∧ Buffer s p 8 true ∧
        Spec.Disjoint p.toNat 8 ((s.regs regSP).toNat - 64) 112)
      (fun _ => goClass P)
      (fun s s' => s'.regs 0 = x ∧
        s'.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64)
      (fun _ _ _ => False) := by
  apply Ensures.toGo
  intro ret hret s hs hpre
  obtain ⟨hg, ⟨hle, hnw, hacc⟩, ⟨hbw, hb⟩, hd⟩ := hpre
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint]
    at hacc hle hnw hgl hgb hnw2 hgr hd
  janus64_run

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The panic runtime: the model with an empty funcs table. -/
def PW : Spec.PanicRuntime := Janus.Contracts.PanicModel.P0 [] Janus.Contracts.PanicSatAmd64.RPa

def p : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def x : BitVec 64 := 3#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then p else if r_ = 3 then x else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [p, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : (fun s : State => StackGuardOK s 0 ∧ StackWritable s 64 48 ∧ Buffer s p 8 true ∧ Spec.Disjoint p.toNat 8 ((s.regs regSP).toNat - 64) 112) s0 := by
  dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

theorem hyps : True := by decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (P : Janus.Spec.PanicRuntime) (p : BitVec 64) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [p, x] s ∧ (StackGuardOK s 0 ∧ StackWritable s 64 48 ∧ Buffer s p 8 true ∧ Spec.Disjoint p.toNat 8 ((s.regs regSP).toNat - 64) 112) ∧
    GoReturns (Extracted.program.withExit ret) (goClass P) s fun o =>
    match o with
    | .returned s' => ABIReturn s s' ∧ (s'.regs 0 = x ∧ s'.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64)
    | .panicked v s' => False
    | .goexited _ => False :=
  ⟨ret, s0, PW, p, x, hret, setup, hpre, correctness PW p x ret hret s0 setup hpre⟩

end Witness

end Proof
