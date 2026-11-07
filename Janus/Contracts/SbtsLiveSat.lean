import Janus.Contracts.LiveSat

/-!
# `slicebytetostringLive` is satisfiable (arm64)

The audit accepts `RtLiveContract … (slicebytetostringSpec st) slicebytetostringLive` (U-SBTS-LIVE, `Janus.Tools.Audit`:
`frameworkSpecs`, `liveSpecOf`). This file is its non-vacuity witness for the empty string: for every `st`, an
implementation (`RET`: the result words are the argument words `buf = 0`, `ptr = 0`), a runtime, and a call state meeting
the precondition. The non-empty shapes (a copy into a fresh block) are `Janus.Contracts.LiveStub` stubs
(`SbtsLiveStub`).
-/

namespace Janus.Contracts.SbtsLiveSat

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat
open Janus.Contracts.AllocSat (toy A0 at0 link_at0)

theorem roundupsize_zero' (b : Bool) : roundupsize 0 b = 0 := by cases b <;> rfl

def okSb : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [0, 0, 0]

set_option maxRecDepth 20000 in
theorem sbts_impl (st : Nat) :
    RtLiveContract (toy.link (at0 [0xd65f03c0])) A0 4096 (toyR tys0 okSb) (slicebytetostringSpec st)
      slicebytetostringLive := by
  rw [link_at0]
  intro L b s hpc pre
  have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _⟩ := pre
  obtain ⟨-, -, -, -, -, hok, hinv, -⟩ := pre
  janus_run
  have ha : argWords s 3 = [0, 0, 0] := (hok.2 : argWords s 3 = [0, 0, 0])
  have ha' := ha
  simp [argWords, wordsFrom] at ha'
  have e0 : (s.regs 0).toNat = 0 := ha'.1
  have e1 : (s.regs 1).toNat = 0 := ha'.2.1
  refine rt_post_nochange ?_ ?_ ?_ ?_ hinv
  · simp [slicebytetostringSpec, slicebytetostringLive, ha, arg, roundupsize_zero']
  · simp [slicebytetostringSpec, slicebytetostringLive, ha, arg, e0, e1]
  · simp [slicebytetostringSpec, slicebytetostringLive, ha, arg, e0, e1, range0]
  · simp only [slicebytetostringSpec, ha, e0, e1, arg, List.getD_cons_succ, List.getD_cons_zero]
    simp [Janus.Spec.strBytes, StrOut, StrAt]

theorem slicebytetostringLive_satisfiable (st : Nat) : ∃ (impl : List Segment) (R : RtInv),
    RtLiveContract (toy.link impl) A0 4096 R (slicebytetostringSpec st) slicebytetostringLive ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      RtLivePre 4096 R (slicebytetostringSpec st) slicebytetostringLive A0 L b s := by
  have ha : argWords (wst [0, 0, 0]) 3 = [0, 0, 0] := by decide
  refine ⟨at0 [0xd65f03c0], toyR tys0 okSb, sbts_impl st, [], 0x400, wst [0, 0, 0], rfl,
    wst_wcallOK _ 3 (by omega), ?_, ?_, by trivial, wguard _ 3 (by omega),
    ⟨⟨rfl, ha⟩, wmem_inv 0, ?_, by simp, wwin _ 3 (by omega)⟩⟩
  · simp only [slicebytetostringSpec, ha, arg, List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨Or.inl rfl, by simp [StrIn], fun h => absurd rfl h⟩
  · intro x hx
    simp [slicebytetostringSpec, ha, arg] at hx
    subst hx
    simp [calleeStack, wsp_eq, wspn, wsp]
  · have hn : (slicebytetostringSpec st).nargs = 3 := rfl
    simp [slicebytetostringLive, hn, ha, arg, roundupsize_zero']

end Janus.Contracts.SbtsLiveSat

/-- `RtLiveContract linked a 4096 (toyR tys ok) (slicebytetostringSpec st) slicebytetostringLive` for the stub `RET` placed
at `a` (`[0xd65f03c0]`), when the request the runtime serves is the EMPTY string: `hok : ∀ args, ok a args → args = [0, 0, 0]`
(`buf = 0`, `ptr = 0`, `n = 0`; the result `(buf, ptr)` is then the empty string). U-SBTS-LIVE. -/
syntax "janus_live_sbts_empty " term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_sbts_empty $hok) => `(tactic| (
      intro L b s hpc pre
      have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _⟩ := pre
      obtain ⟨-, -, -, -, -, hokx, hinv, -⟩ := pre
      have ha : argWords s 3 = [0, 0, 0] := $hok _ hokx
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      have ha' := ha
      simp [argWords, wordsFrom] at ha'
      have e0 : (s.regs 0).toNat = 0 := ha'.1
      have e1 : (s.regs 1).toNat = 0 := ha'.2.1
      refine Janus.Contracts.LiveSat.rt_post_nochange ?_ ?_ ?_ ?_ hinv
      · simp [Janus.Contracts.slicebytetostringLive, ha, Janus.Contracts.arg, Janus.Contracts.SbtsLiveSat.roundupsize_zero']
      · simp [Janus.Contracts.slicebytetostringLive, ha, Janus.Contracts.arg, e0, e1]
      · simp [Janus.Contracts.slicebytetostringLive, ha, Janus.Contracts.arg, e0, e1, Janus.Contracts.range0]
      · simp only [Janus.Contracts.slicebytetostringSpec, ha, e0, e1, Janus.Contracts.arg, List.getD_cons_succ, List.getD_cons_zero]
        simp [Janus.Spec.strBytes, Janus.Contracts.StrOut, Janus.Contracts.StrAt]))
