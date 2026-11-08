import Janus
import Extracted

/-! `example.com/basic.PanicIf(x, e any)` on amd64: returns `x+1` for `x ≤ 10`, panics with
exactly `e` (reaches `runtime.gopanic`) for `x > 10`. Example 1 of docs/COVERAGE.md R6. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts.PanicAmd64

theorem correctness (P : PanicRuntime) (x etyp edata : BitVec 64) :
    EnsuresGo Extracted.program Extracted.entry [x, etyp, edata]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 40 40)
      (fun _ => goClass P)
      (fun _ s' => x.toNat ≤ 10 → s'.regs 0 = x + 1)
      (fun _ v _ => 10 < x.toNat → v = ⟨etyp.toNat, edata.toNat⟩) := by
  intro ret hret s hs ⟨hg, hle, hnw, hacc⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  refine GoReturns.of_reaches ?_
  by_cases hx : x.toNat ≤ 10
  · janus64_run
    exact fun _ => trivial
  · have hx' : 10 < x.toNat := by omega
    janus64_run
    refine ⟨⟨etyp.toNat, edata.toNat⟩, ?_, ?_⟩
    · show (⟨etyp.toNat, edata.toNat⟩ : Eface) = ⟨_, _⟩
      simp [setRegF]
    · first | (intro _; rfl) | rfl | trivial

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The panic runtime: the model with an empty funcs table. -/
def PW : Spec.PanicRuntime := Janus.Contracts.PanicModel.P0 [] Janus.Contracts.PanicSatAmd64.RPa

def x : BitVec 64 := 3#64
def etyp : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def edata : BitVec 64 := 0x30900#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then x else if r_ = 3 then etyp else if r_ = 1 then edata else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, etyp, edata] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : (fun s : State => StackGuardOK s 0 ∧ StackWritable s 40 40) s0 := by
  dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

theorem hyps : True := by decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (P : Janus.Spec.PanicRuntime) (x : BitVec 64) (etyp : BitVec 64) (edata : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, etyp, edata] s ∧ (StackGuardOK s 0 ∧ StackWritable s 40 40) ∧
    GoReturns (Extracted.program.withExit ret) (goClass P) s fun o =>
    match o with
    | .returned s' => ABIReturn s s' ∧ (x.toNat ≤ 10 → s'.regs 0 = x + 1)
    | .panicked v s' => 10 < x.toNat → v = ⟨etyp.toNat, edata.toNat⟩
    | .goexited _ => False :=
  ⟨ret, s0, PW, x, etyp, edata, hret, setup, hpre, correctness PW x etyp edata ret hret s0 setup hpre⟩

end Witness

end Proof
