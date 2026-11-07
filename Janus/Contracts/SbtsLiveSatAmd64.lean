import Janus.Contracts.LiveSatAmd64
import Janus.Contracts.SbtsLiveSat

/-!
# `slicebytetostringLive` is satisfiable (amd64)

The amd64 twin of `SbtsLiveSat.lean`: for every `st`, an implementation (`RET`: the result words are the argument words
`buf = 0` (`RAX`), `ptr = 0` (`RBX`)), a runtime, and a call state meeting the precondition of
`RtLiveContract64 … (slicebytetostringSpec st) slicebytetostringLive`.
-/

namespace Janus.Contracts.SbtsLiveSatAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy
  Janus.Contracts.LiveSatAmd64 Janus.Contracts.SbtsLiveSat
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0)

set_option maxRecDepth 20000 in
theorem sbts_impl64 (st : Nat) :
    RtLiveContract64 (toy.link (at0 [0xc3])) A0 4096 (toyR LiveSat.tys0 okSb) (slicebytetostringSpec st)
      slicebytetostringLive := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨hra, hal, h3, h4, h5⟩, _, _, _, _, hok, hinv, _⟩ := pre
  janus64_run
  have ha : argWords64 s 3 = [0, 0, 0] := (hok.2 : argWords64 s 3 = [0, 0, 0])
  have ha' := ha
  simp [argWords64, wordsFrom] at ha'
  have e0 : (s.regs 0).toNat = 0 := ha'.1
  have e1 : (s.regs 3).toNat = 0 := ha'.2.1
  refine rt_post_nochange64 ?_ ?_ ?_ ?_ hinv (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp) rfl rfl (by simp) rfl rfl rfl
  · simp [slicebytetostringLive, ha, arg, roundupsize_zero']
  · simp [slicebytetostringLive, ha, arg, e0, e1]
  · simp [slicebytetostringLive, ha, arg, e0, e1, range0]
  · simp only [slicebytetostringSpec, ha, e0, e1, arg, List.getD_cons_succ, List.getD_cons_zero]
    simp [Janus.Spec.strBytes, StrOut, StrAt]

theorem slicebytetostringLive64_satisfiable (st : Nat) : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    RtLiveContract64 (toy.link impl) A0 4096 R (slicebytetostringSpec st) slicebytetostringLive ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      RtLivePre64 4096 R (slicebytetostringSpec st) slicebytetostringLive A0 L b s := by
  have ha : argWords64 (wst [0, 0, 0]) 3 = [0, 0, 0] := by
    have a0 : argReg 0 = 0 := rfl
    have a1 : argReg 1 = 3 := rfl
    have a2 : argReg 2 = 1 := rfl
    simp [argWords64, wordsFrom, a0, a1, a2]
    refine ⟨?_, ?_, ?_⟩ <;> decide
  have hn : (slicebytetostringSpec st).nargs = 3 := rfl
  refine ⟨at0 [0xc3], toyR LiveSat.tys0 okSb, sbts_impl64 st, [], 0x400, wst [0, 0, 0], rfl,
    wcallOK64 _ 3 (by omega), ?_, ?_, by trivial, wguard64 _ 3 (by omega),
    ⟨⟨rfl, ha⟩, LiveSat.wmem_inv 0, ?_, by simp, wwin64 _ 3 (by omega)⟩⟩
  · simp only [slicebytetostringSpec, ha, arg, List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨Or.inl rfl, by simp [StrIn], fun h => absurd rfl h⟩
  · intro x hx
    simp [slicebytetostringSpec, ha, arg] at hx
    subst hx
    simp [calleeStack64, w4, LiveSat.wsp]
  · simp [slicebytetostringLive, hn, ha, arg, roundupsize_zero']

end Janus.Contracts.SbtsLiveSatAmd64

/-- The amd64 twin of `janus_live_sbts_empty`: the stub `RET` (`[0xc3]`) placed at the contract address; `hok : ∀ args, ok a args →
args = [0, 0, 0]` (`RAX = buf = 0`, `RBX = ptr = 0`, `RCX = n = 0`). -/
syntax "janus64_live_sbts_empty " term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_live_sbts_empty $hok) => `(tactic| (
      intro L b s hpc pre
      obtain ⟨⟨hra, hal, h3, h4, h5⟩, _, _, _, _, hokx, hinv, _⟩ := pre
      have ha : argWords64 s 3 = [0, 0, 0] := $hok _ hokx
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      have ha' := ha
      simp [argWords64, wordsFrom] at ha'
      have e0 : (s.regs 0).toNat = 0 := ha'.1
      have e1 : (s.regs 3).toNat = 0 := ha'.2.1
      refine Janus.Contracts.LiveSatAmd64.rt_post_nochange64 ?_ ?_ ?_ ?_ hinv (by simp [Janus.Amd64.Tactic.retAddrOf]) (by simp [Janus.Amd64.Tactic.setRegF])
        (by simp [Janus.Amd64.Tactic.setRegF]) (by simp [Janus.Amd64.Tactic.setRegF]) (by simp [Janus.Amd64.Tactic.setRegF]) (by simp [Janus.Amd64.Tactic.setRegF]) (by simp [Janus.Amd64.Tactic.setRegF]) (by simp)
        rfl rfl (by simp) rfl rfl rfl
      · simp [Janus.Contracts.slicebytetostringLive, ha, Janus.Contracts.arg, Janus.Contracts.SbtsLiveSat.roundupsize_zero']
      · simp [Janus.Contracts.slicebytetostringLive, ha, Janus.Contracts.arg, e0, e1]
      · simp [Janus.Contracts.slicebytetostringLive, ha, Janus.Contracts.arg, e0, e1, Janus.Contracts.range0]
      · simp only [Janus.Contracts.slicebytetostringSpec, ha, e0, e1, Janus.Contracts.arg, List.getD_cons_succ, List.getD_cons_zero]
        simp [Janus.Spec.strBytes, Janus.Contracts.StrOut, Janus.Contracts.StrAt]))
