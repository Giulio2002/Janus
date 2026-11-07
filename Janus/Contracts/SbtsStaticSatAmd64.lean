import Janus.Contracts.SbtsStaticSat

/-!
# `slicebytetostringSpecT` is satisfiable (amd64)

The amd64 twin of `SbtsStaticSat.lean`: the same table memory `tmem`, a `RET` implementation and a call state over `tmem`
meeting `RtLivePre64` for `slicebytetostringSpecT st` (U-SBTS-STATIC).
-/

namespace Janus.Contracts.SbtsStaticSatAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy
  Janus.Contracts.LiveSatAmd64 Janus.Contracts.SbtsLiveSat Janus.Contracts.SbtsStaticSat
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0)

/-- The amd64 witness call state over `tmem`. -/
def tst (l : List Nat) : State := { wst l with mem := tmem }

theorem tst_mem (l : List Nat) : (tst l).mem = tmem := rfl
theorem t4 (l : List Nat) : (tst l).regs 4 = BitVec.ofNat 64 LiveSat.wsp := w4 l
theorem t14 (l : List Nat) : (tst l).regs 14 = BitVec.ofNat 64 LiveSat.wg := w14 l

theorem tcallOK64 (l : List Nat) (n : Nat) (hn : n ≤ 5) : CallOK64 (tst l) 4096 n := by
  have hw : tmem.accessible (LiveSat.wsp - 4096) (4096 + 8 + 8 * 5) true = true := by decide
  simp only [CallOK64, t4, tst_mem, LiveSat.wspn]
  refine ⟨by decide, by decide, by decide, by simp [LiveSat.wsp]; omega, ?_⟩
  exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem tguard64 (l : List Nat) (n : Nat) (hn : n ≤ 5) : StackRoom64 (tst l) 4096 n := by
  simp only [StackRoom64, GuardOK64, t14, t4, tst_mem, LiveSat.wspn, LiveSat.wgn, calleeStack64]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true, LiveSat.wsp, LiveSat.wg]
  omega

theorem twin64 (l : List Nat) (n : Nat) (hn : n ≤ 5) :
    LiveSep (liveWin64 (tst l) 4096 n) (toyRt LiveSat.tys0) := by
  intro x hx
  simp only [liveWin64, calleeStack64, t4, LiveSat.wspn, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl) | rfl <;>
    simp only [toyRt, LiveSat.tys0, outside_cons, outside_nil, outside_append, List.map, and_true, LiveSat.wsp, HEAP, HEND,
      BUMP, WBUF, LiveSat.tyA, LiveSat.tyB, LiveSat.tyC] <;> omega

set_option maxRecDepth 20000 in
theorem sbtsT_impl64 (st : Nat) :
    RtLiveContract64 (toy.link (at0 [0xc3])) A0 4096 (toyR LiveSat.tys0 okSb) (slicebytetostringSpecT st)
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
  · simp only [slicebytetostringSpecT, slicebytetostringSpec, ha, e0, e1, arg, List.getD_cons_succ, List.getD_cons_zero]
    simp [Janus.Spec.strBytes, StrOut, StrAt]

theorem slicebytetostringSpecT64_satisfiable : ∃ (st : Nat) (impl : List Janus.Amd64.Segment) (R : RtInv),
    RtLiveContract64 (toy.link impl) A0 4096 R (slicebytetostringSpecT st) slicebytetostringLive ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      RtLivePre64 4096 R (slicebytetostringSpecT st) slicebytetostringLive A0 L b s := by
  have ha : argWords64 (tst [0, 0, 0]) 3 = [0, 0, 0] := by
    have a0 : argReg 0 = 0 := rfl
    have a1 : argReg 1 = 3 := rfl
    have a2 : argReg 2 = 1 := rfl
    simp [argWords64, wordsFrom, a0, a1, a2, tst, wst]
    try (refine ⟨?_, ?_, ?_⟩ <;> decide)
  have hn : (slicebytetostringSpecT ST).nargs = 3 := rfl
  refine ⟨ST, at0 [0xc3], toyR LiveSat.tys0 okSb, sbtsT_impl64 ST, [], 0x400, tst [0, 0, 0], rfl,
    tcallOK64 _ 3 (by omega), ?_, ?_, by trivial, tguard64 _ 3 (by omega),
    ⟨⟨rfl, ha⟩, tmem_inv 0, ?_, by simp, twin64 _ 3 (by omega)⟩⟩
  · simp only [slicebytetostringSpecT, slicebytetostringSpec, ha, arg, List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨⟨Or.inl rfl, by simp [StrIn], fun h => absurd rfl h⟩, tst_mem _ ▸ tmem_static⟩
  · intro x hx
    simp [slicebytetostringSpecT, slicebytetostringSpec, ha, arg] at hx
    subst hx
    simp [calleeStack64, t4, LiveSat.wsp]
  · simp [slicebytetostringLive, hn, ha, arg, roundupsize_zero']

end Janus.Contracts.SbtsStaticSatAmd64
