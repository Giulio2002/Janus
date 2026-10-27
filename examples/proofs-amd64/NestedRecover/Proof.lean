import Janus
import Extracted

/-!
# `NestedRecover(e1, e2 any) (r uint64)`: recovering a nested panic recovers both (amd64)

`NestedRecover` is
`defer func() { if recover() != nil { r = 7 } }(); defer func() { panic(e2) }(); panic(e1)`
(two open-coded defers). `panic(e1)` runs the second deferred call, which panics with `e2` while
`e1` is unwinding; `e2` becomes the active panic and the walk goes on to the remaining deferred
call, whose `recover()` returns `e2` (it is called directly by the deferred call the `e2` panic
runs): that recovers `e2`, and with it the aborted `e1`; the runtime drops both and resumes the
frame at its `deferreturn` call.

**Guarantee (example 9 of docs/COVERAGE.md R6).** For every panic-runtime model `P` satisfying its
laws, every implementation of `runtime.gopanic`, `runtime.gorecover` and `runtime.deferreturn`
meeting their contracts (`Janus.Contracts.PanicAmd64`, pinned to the Go 1.26 runtime's code), every
admissible return address and every call state with no active panic, the runtime usable with
stack for the frame and the nested panic's runtime window, both `any`s non-nil and room for two
`_panic` records: the call **returns `7`**. It never panics.
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64
open Janus.Contracts.MapAmd64 (keepABI_apply)
open Janus.Contracts.Panic (frameItems openItems frameKeep bitsWin recItems recItems_above Frame frameRecs_above)
open Janus.Spec (openBits)

/-! Code addresses are read off the extraction (`janus_eval%`), never copied: a relinked
binary needs no edit. -/
local macro "loc_NestedRecover_140" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedRecover" + 140))
local macro "loc_NestedRecover_146" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedRecover" + 146))
local macro "loc_NestedRecover_func1_27" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 27))

local macro "func1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedRecover.func1"))
local macro "func2A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedRecover.func2"))
local macro "resumeA" : term => `(janus_eval% (Extracted.entry + 0x8d))

set_option maxHeartbeats 0 in
/-- The deferred closure `NestedRecover.func2` up to its call of `runtime.gopanic`: `panic(e2)`. -/
theorem cl2 (impl : List Janus.Amd64.Segment) (e : State) (t d : BitVec 64) (a : Nat)
    (hpe : e.rip = BitVec.ofNat 64 func2A) (hrdx : e.regs 2 = BitVec.ofNat 64 a) (ha : a + 16 + 8 < 2 ^ 64)
    (hab : (e.regs 4).toNat ≤ a + 8)
    (hcapt : e.mem.readLE (a + 8) 8 = t.toNat) (hcapd : e.mem.readLE (a + 16) 8 = d.toNat)
    (hat : e.mem.accessible (a + 8) 8 false = true) (had : e.mem.accessible (a + 16) 8 false = true)
    (hgv : e.mem.readLE ((e.regs 14).toNat + 16) 8 < (e.regs 4).toNat)
    (hga : e.mem.accessible ((e.regs 14).toNat + 16) 8 false = true) (hgb : (e.regs 14).toNat + 16 + 8 ≤ 2 ^ 48)
    (hsp : 32 ≤ (e.regs 4).toNat)
    (hwin : e.mem.accessible ((e.regs 4).toNat - 32) 32 true = true) :
    ReachesRet (Extracted.program.link impl)
      (BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic")) e (fun S =>
      S.regs 4 = e.regs 4 - 32#64 ∧ S.regs 0 = t ∧ S.regs 3 = d ∧ S.regs 14 = e.regs 14 ∧
      S.regs 5 = e.regs 4 - 8#64 ∧ S.xmm 15 = e.xmm 15 ∧ S.df = e.df ∧
      MemFrame e.mem S.mem [((e.regs 4).toNat - 32, (e.regs 4).toNat)] ∧
      S.mem.readLE (S.regs 4).toNat 8 = func2A + 27) := by
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpe
  have hcr : cr = setRegF cr 2 (BitVec.ofNat 64 a) := by
    funext i; simp only [setRegF]; split
    · subst_vars; exact hrdx
    · rfl
  rw [hcr]
  janus64_run until [Extracted.program.contractAddr "runtime.gopanic"]
  refine ReachesRet.done rfl ?_
  have h32 : (cr 4 - 32#64).toNat = (cr 4).toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
  refine ⟨by simp [setRegF], by simp [setRegF], by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl, rfl,
    ?_, ?_⟩
  · have h4 : setRegF cr 2 (BitVec.ofNat 64 a) 4 = cr 4 := by simp [setRegF]
    rw [h4]; janus_frame
  · simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h32, Janus.Arm64.Memory.readLE_writeLE_self]

set_option maxHeartbeats 0 in
/-- The deferred closure `NestedRecover.func1` run by the runtime while the nested panic `e2` (on top
of the aborted `e1`) unwinds: its `recover()` returns the top panic's value `e2`, so it sets the
named result to `7`; the top panic is marked recovered. -/
theorem closure_run (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (hrec : GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") P)
    (hw : ¬ P.wrapper (segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 0x1b))
    (s : State) (hc : PanicCallerOK P s (P.depth + 128) 40) (e : State) (etyp edata st : Nat)
    (B : Spec.PanicRec)
    (hpe : e.rip = BitVec.ofNat 64 func1A) (hrdx : e.regs 2 = BitVec.ofNat 64 ((s.regs 4).toNat - 40))
    (h14 : e.regs 14 = s.regs 14) (hx : e.xmm 15 = 0) (hdf : e.df = false)
    (hal : (e.regs 4).toNat % 8 = 0) (hlo : (s.regs 4).toNat - 96 - P.depth ≤ (e.regs 4).toNat)
    (hhi : (e.regs 4).toNat + 16 ≤ (s.regs 4).toNat - 96)
    (hra : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 47) (henv : P.Env e.mem)
    (hW : MemFrame s.mem e.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat + 40)]))
    (hcap : e.mem.readLE ((s.regs 4).toNat - 32) 8 = (s.regs 4).toNat - 72)
    (hpan : P.panics e.mem (s.regs 14).toNat = [{ arg := ⟨etyp, edata⟩, start := st }, B])
    (hrp : P.rp e.mem (s.regs 14).toNat = e.mem.readLE (e.regs 4).toNat 8)
    (hne : etyp ≠ 0) :
    ReachesRet (Extracted.program.link impl) (retAddrOf e) e (fun c' =>
      c'.rip = retAddrOf e ∧ c'.regs 4 = e.regs 4 + 8 ∧ c'.regs 14 = e.regs 14 ∧ c'.regs 5 = e.regs 5 ∧
      c'.xmm 15 = 0 ∧ c'.df = false ∧ P.Env c'.mem ∧
      P.panics c'.mem (s.regs 14).toNat = [{ arg := ⟨etyp, edata⟩, start := st, recovered := true }, B] ∧
      P.defers c'.mem (s.regs 14).toNat = P.defers e.mem (s.regs 14).toNat ∧
      P.saved c'.mem (s.regs 14).toNat = P.saved e.mem (s.regs 14).toNat ∧
      P.room e.mem (s.regs 14).toNat ≤ P.room c'.mem (s.regs 14).toNat ∧
      MemFrame e.mem c'.mem (P.priv ++ [((e.regs 4).toNat - 24 - P.depth, (e.regs 4).toNat),
        ((s.regs 4).toNat - 72, (s.regs 4).toNat - 64)]) ∧
      c'.mem.readLE ((s.regs 4).toNat - 72) 8 = 7) := by
  have hc' := hc
  obtain ⟨henv0, hg, hal0, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd hb hal0
  have hgb' : (e.regs 14).toNat + 16 + 8 ≤ 2 ^ 48 := by rw [h14]; omega
  have hga : e.mem.accessible ((e.regs 14).toNat + 16) 8 false = true := by
    rw [hW.accessible, h14]; exact hgr
  have hwin' : e.mem.accessible ((s.regs 4).toNat - (P.depth + (P.depth + 128)))
      (P.depth + (P.depth + 128) + 40) true = true := by
    rw [hW.accessible]; exact hst
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpe hdf
  have hcr : cr = setRegF (setRegF cr 2 (BitVec.ofNat 64 ((s.regs 4).toNat - 40))) 14 (s.regs 14) := by
    funext i; simp only [setRegF]; split
    · subst_vars; exact h14
    · split
      · subst_vars; exact hrdx
      · rfl
  rw [hcr]
  janus64_run until [Extracted.program.contractAddr "runtime.gorecover"]
  refine ReachesRet.name fun G hG => ?_
  have hc24 : (cr 4 - 24#64).toNat = (cr 4).toNat - 24 := by rw [BitVec.toNat_sub]; simp; omega
  have hc8 : (cr 4 - 8#64).toNat = (cr 4).toNat - 8 := by rw [BitVec.toNat_sub]; simp; omega
  have hGsp : G.regs 4 = cr 4 - 24#64 := by rw [hG] <;> simp [setRegF]
  have hGspn : (G.regs 4).toNat = (cr 4).toNat - 24 := by rw [hGsp]; exact hc24
  have hG5 : G.regs 5 = cr 4 - 8#64 := by rw [hG] <;> simp [setRegF]
  have hG5n : (G.regs 5).toNat = (cr 4).toNat - 8 := by rw [hG5]; exact hc8
  have hG14 : G.regs 14 = s.regs 14 := by rw [hG] <;> simp [setRegF]
  have hGx : G.xmm 15 = 0 := by rw [hG]; exact hx
  have hGdf : G.df = false := by rw [hG]
  have hGpc : G.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gorecover") := by rw [hG] <;> rfl
  have hGf : MemFrame cm G.mem [((cr 4).toNat - 24, (cr 4).toNat)] := by rw [hG]; janus_frame
  have hGra : G.mem.readLE (G.regs 4).toNat 8 = loc_NestedRecover_func1_27 := by
    rw [hG]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, hc24, Janus.Arm64.Memory.readLE_writeLE_self]
  have hgG : gOf G = (s.regs 14).toNat := by simp only [gOf, hG14]
  have hGfW : MemFrame s.mem G.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat + 40)]) :=
    hW.trans hGf fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      omega⟩
  have hagG : Spec.Map.Agrees cm G.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (cr 4).toNat - 24) (hi := (cr 4).toNat) hGf
      (Outside.of_sub hout (by omega) (by omega))
  have hGacc : G.mem.accessible (cr 4).toNat 8 false = true := by
    rw [hGf.accessible, hW.accessible]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
  refine ReachesRet.call hrec hGpc ⟨PanicPre.of_within hc hGfW (hl.env_frame _ _ henv hagG) (by omega) (by omega)
      (by omega) hG14 hGx hGdf (by rw [hGra]; decide), ?_, ?_⟩ ?_
  · rw [hG5n, show (cr 4).toNat - 8 + 8 = (cr 4).toNat by omega]; exact hGacc
  · rw [hG5n]; omega
  intro G2 hpc2 hpost
  obtain ⟨⟨r2, x2, y2, f2, m2, hs2, hfr2, henv2⟩, hdf2, hsv2, hrp2, hrm2, hnil2, hpanI⟩ := hpost
  have hsegf : segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 0x1b = loc_NestedRecover_func1_27 := by decide
  have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have hpanG : P.panics G.mem (gOf G) = [{ arg := ⟨etyp, edata⟩, start := st }, B] := by
    rw [hgG, hl.panics_frame _ _ _ hagG]; exact hpan
  have hrpG : G.mem.readLE ((G.regs 5).toNat + 8) 8 = P.rp G.mem (gOf G) := by
    rw [hG5n, show (cr 4).toNat - 8 + 8 = (cr 4).toNat by omega, hgG, hl.rp_frame _ _ _ hagG, hrp]
    exact hGf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  obtain ⟨hr0, hr1, hrec2⟩ := hpanI _ [B] hpanG rfl rfl (by rw [hGra, ← hsegf]; exact hw) hrpG
  subst hs2
  have hdf2' : P.defers m2 (s.regs 14).toNat = P.defers cm (s.regs 14).toNat := by
    have h := hdf2; rw [hgG] at h; exact h.trans (hl.defers_frame _ _ _ hagG)
  have hsv2' : P.saved m2 (s.regs 14).toNat = P.saved cm (s.regs 14).toNat := by
    have h := hsv2; rw [hgG] at h; exact h.trans (hl.saved_frame _ _ _ hagG)
  have hrm2' : P.room cm (s.regs 14).toNat ≤ P.room m2 (s.regs 14).toNat := by
    have h := hrm2; rw [hgG] at h
    exact Nat.le_trans (Nat.le_of_eq (hl.room_frame _ _ _ hagG).symm) h
  have hpanM2 : P.panics m2 (s.regs 14).toNat =
      [{ arg := ⟨etyp, edata⟩, start := st, recovered := true }, B] := by
    have h := hrec2; rw [hgG] at h; exact h
  simp only [MapAmd64.calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, hGspn, keepABI_apply] at hfr2 hr0 hr1 henv2
  have hj0 : r2 0 ≠ 0 := fun h => hne (by rw [← hr0, h]; rfl)
  have hGra' : G.mem.readLE ((cr 4).toNat - 24) 8 = loc_NestedRecover_func1_27 := by rw [← hGspn]; exact hGra
  clear hpanI hnil2 hpanG hrpG hGacc hGra hGfW hGx hGdf hGpc hG14 hG5 hG5n hGsp hGspn hgG hdf2 hsv2 hrp2 hrm2 hpc2 hrec2
  subst hG
  have hcap' : cm.readLE ((s.regs 4).toNat - 40 + 8) 8 = (s.regs 4).toNat - 72 := by
    rw [show (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 by omega]; exact hcap
  have hacc7 : m2.accessible ((s.regs 4).toNat - 72) 8 true = true := by
    rw [hfr2.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_mono _ hwin' (by omega) (by omega)
  janus64_run [hcap']
  all_goals first
    | (exfalso; exact hj0 (BitVec.eq_of_toNat_eq (by simpa using ‹(r2 0).toNat = 0›)))
    | (have hag7 : Spec.Map.Agrees m2 (Janus.Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 72) 8 7) P.priv :=
         Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - 72) (hi := (s.regs 4).toNat - 64)
           (by janus_frame) (Outside.of_sub hout (by omega) (by omega))
       refine ⟨hx, hl.env_frame _ _ henv2 hag7, (hl.panics_frame _ _ _ hag7).trans hpanM2,
         (hl.defers_frame _ _ _ hag7).trans hdf2', (hl.saved_frame _ _ _ hag7).trans hsv2',
         Nat.le_trans hrm2' (Nat.le_of_eq (hl.room_frame _ _ _ hag7).symm), ?_⟩
       try simp only [List.cons_append, List.nil_append]
       janus_frame)

/-- The memory the run may change: the runtime's memory, the window below and around the frame, but
not the two slots holding the saved frame pointer and the return address. -/
abbrev W2 (P : Spec.PanicRuntime) (s : State) : List (Nat × Nat) :=
  P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat - 8),
    ((s.regs 4).toNat + 8, (s.regs 4).toNat + 40)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hpan : GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs)
    (hrec : GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U)
    (e1t e1d e2t e2d : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [e1t, e1d, e2t, e2d]
      (fun s => PanicCallerOK P s (P.depth + 128) 40 ∧ P.Calm s.mem (s.regs 14).toNat ∧
        e1t.toNat ≠ 0 ∧ e2t.toNat ≠ 0 ∧ 2 ≤ P.room s.mem (gOf s) ∧
        (∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp) ∧
        ¬ P.wrapper (segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 0x1b))
      (goClassU P U)
      (fun _ s' => (s'.regs 0).toNat = 7)
      (fun _ _ _ => False) := by
  intro ret hret s hs ⟨hc, hcalm, hne1, hne2, hroom, hds, hw⟩
  have hc' := hc
  obtain ⟨henv, hg, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd hb hal hds
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
    hret.fetch_none ?_
  janus64_run until [Extracted.program.contractAddr "runtime.gopanic"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun S hS => ?_
  have h104 : (s.regs 4 - 104#64).toNat = (s.regs 4).toNat - 104 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hSsp : S.regs 4 = s.regs 4 - 104#64 := by rw [hS] <;> simp [setRegF]
  have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 104 := by rw [hSsp]; exact h104
  have hSpc : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by rw [hS] <;> rfl
  have hS0 : S.regs 0 = e1t := by rw [hS] <;> simp [setRegF, h_a0]
  have hS3 : S.regs 3 = e1d := by rw [hS] <;> simp [setRegF, h_a1]
  have hS14 : S.regs 14 = s.regs 14 := by rw [hS] <;> simp [setRegF]
  have hSx : S.xmm 15 = 0 := by rw [hS]; exact h_x15
  have hSdf : S.df = false := by rw [hS]
  have hSf : MemFrame s.mem S.mem [((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat + 40)] := by
    rw [hS]; janus_frame
  have hSra : S.mem.readLE (S.regs 4).toNat 8 = loc_NestedRecover_140 := by
    rw [hS]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h104, Janus.Arm64.Memory.readLE_writeLE_self]
  have hbits : S.mem.readLE ((s.regs 4).toNat - 73) 1 = 3 := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  have hslot0 : S.mem.readLE ((s.regs 4).toNat - 24) 8 = (s.regs 4).toNat - 40 := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 4).isLt; omega)
  have hslot1 : S.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 64 := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 4).isLt; omega)
  have hfv1 : S.mem.readLE ((s.regs 4).toNat - 40) 8 = func1A := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    try decide
  have hfv2 : S.mem.readLE ((s.regs 4).toNat - 64) 8 = func2A := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    try decide
  have hcap1 : S.mem.readLE ((s.regs 4).toNat - 32) 8 = (s.regs 4).toNat - 72 := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 4).isLt; omega)
  have hcap2t : S.mem.readLE ((s.regs 4).toNat - 56) 8 = e2t.toNat := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := e2t.isLt; omega)
  have hcap2d : S.mem.readLE ((s.regs 4).toNat - 48) 8 = e2d.toNat := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := e2d.isLt; omega)
  have hSrbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                               have := (s.regs 5).isLt; omega)
  have hSret : S.mem.readLE (s.regs 4).toNat 8 = ret := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact h_ret
  clear hS
  obtain ⟨fi, hfi⟩ : ∃ fi : Spec.FuncInfo, fi = Spec.FuncInfo.named Extracted.funcs "example.com/basic.NestedRecover" :=
    ⟨_, rfl⟩
  have f_frame : fi.frame = 96 := by rw [hfi]; rfl
  have f_od : fi.openDefer = some (65, 16) := by rw [hfi]; rfl
  have f_res : fi.resume = Extracted.entry + 0x8d := by rw [hfi]; rfl
  have hagS : Spec.Map.Agrees s.mem S.mem P.priv :=
    Spec.Map.Agrees.of_window hSf (Outside.of_sub hout (by omega) (by omega))
  have hgS : gOf S = gOf s := by simp only [gOf, hS14]
  have hcalmS : P.panics S.mem (gOf S) = [] := by
    rw [hgS]; exact hl.calm_frame _ _ _ hcalm hagS
  have hdsS : P.defers S.mem (gOf S) = P.defers s.mem (gOf s) := by
    rw [hgS]; exact hl.defers_frame _ _ _ hagS
  have hfsp : fspOf S = (s.regs 4).toNat - 96 := by simp only [fspOf, hSspn]; omega
  have hdsS' : ∀ d ∈ P.defers S.mem (gOf S), (S.regs 4).toNat + 8 < d.sp := by
    intro d hd; rw [hdsS] at hd; have := hds d hd; omega
  have hri : recItems ((s.regs 4).toNat - 96) (P.defers S.mem (gOf S)) = [] :=
    recItems_above (by rw [← hfsp]; exact hdsS')
  have hF : frameOf fi (fspOf S) S.mem =
      ⟨(s.regs 4).toNat - 96, (s.regs 4).toNat, Extracted.entry + 0x8d,
        some ((s.regs 4).toNat - 73, (s.regs 4).toNat - 24)⟩ := by
    simp only [frameOf, Panic.frameOf, Spec.FuncInfo.bound, Spec.FuncInfo.bitsAt, Spec.FuncInfo.slotsAt,
      Spec.FuncInfo.varp, f_frame, f_od, hfsp, Option.map_some, Option.getD_some, f_res]
    have e1 : (s.regs 4).toNat - 96 + 96 - 8 - 65 = (s.regs 4).toNat - 73 := by omega
    have e2 : (s.regs 4).toNat - 96 + 96 - 8 - 16 = (s.regs 4).toNat - 24 := by omega
    have e3 : (s.regs 4).toNat - 96 + 96 = (s.regs 4).toNat := by omega
    rw [e1, e2, e3, hbits]; rfl
  have hob : openBits 3 = [1, 0] := by decide
  have hI : frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S)) =
      [{ fn := (s.regs 4).toNat - 64, bits := some 1, chain := P.defers S.mem (gOf S) },
       { fn := (s.regs 4).toNat - 40, bits := some 0, chain := P.defers S.mem (gOf S) }] := by
    have e1 : (s.regs 4).toNat - 24 + 8 * 1 = (s.regs 4).toNat - 16 := by omega
    have e2 : (s.regs 4).toNat - 24 + 8 * 0 = (s.regs 4).toNat - 24 := by omega
    rw [hF]
    simp only [frameItems, openItems, hbits, hob, List.map_cons, List.map_nil, hri, List.append_nil, e1, e2,
      hslot0, hslot1, Nat.reducePow, Nat.reduceMod]
  have hSfW : MemFrame s.mem S.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat + 40)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  refine GopanicContract.apply (fi := fi) hpan hSpc (by rw [hSra, hfi]; rfl) ?_ ?_
  · refine ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
        (by rw [hSspn]; omega) hS14 hSx hSdf (by rw [hSra]; decide),
      by rw [hS0]; exact hne1, ?_, ?_, ?_⟩
    · rw [hgS, hl.room_frame _ _ _ hagS]; omega
    · intro _
      have e : fi.bitsAt (fspOf S) = (s.regs 4).toNat - 73 := by
        simp only [Spec.FuncInfo.bitsAt, Spec.FuncInfo.varp, f_frame, f_od, hfsp, Option.map_some,
          Option.getD_some]; omega
      rw [e]
      refine ⟨?_, Outside.of_sub hout (by omega) (by omega)⟩
      rw [hSf.accessible]
      exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
    · rw [hI, hF]
      refine ⟨⟨⟨by omega, by rw [hSf.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega),
        Outside.of_sub hout (by omega) (by omega), by dsimp only; omega, ?_, ?_⟩, ?_⟩, ?_⟩
      · rw [hbits, hob]
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;>
          refine ⟨by omega, ?_, by omega, by dsimp only; omega, Outside.of_sub hout (by omega) (by omega)⟩ <;>
          rw [hSf.accessible] <;>
          exact Janus.Contracts.IfaceModel.acc_read_of_write
            (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
      · intro it hit
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl <;> dsimp only <;> omega
      · intro it hit
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl <;> dsimp only <;> refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first
          | (exact Outside.of_sub hout (by omega) (by omega))
          | omega
          | (rw [hSf.accessible]; exact Janus.Contracts.IfaceModel.acc_read_of_write
              (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)))
          | (simp only [hfv1, hfv2]; try decide)
      · intro it hit
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl <;> dsimp only <;> simp only [hfv1, hfv2] <;> decide
  intro hE
  have hK : frameKeep S.mem (frameOf fi (fspOf S) S.mem)
      (frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S))) =
      [((s.regs 4).toNat - 73, (s.regs 4).toNat - 73 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8),
       ((s.regs 4).toNat - 24, (s.regs 4).toNat - 24 + 8), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 64 + 8),
       ((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 8)] := by
    have e1 : (s.regs 4).toNat - 24 + 8 * 1 = (s.regs 4).toNat - 16 := by omega
    have e2 : (s.regs 4).toNat - 24 + 8 * 0 = (s.regs 4).toNat - 24 := by omega
    rw [hI, hF]
    simp only [frameKeep, hbits, hob, List.map_cons, List.map_nil, List.cons_append, List.nil_append, e1, e2]
  rw [hK, hI, hF] at hE
  rw [Engine_cons] at hE
  obtain ⟨k1, e, hst1, ⟨hpc1, h2_1, h14_1, hx1, hdf1, hal1, hlo1, hhi1, hra1, henv1⟩,
    hfr1, hb1, hd1, hpn1, hrm1, hrs1, hcont1, hnest1⟩ := hE
  dsimp only at hpc1 h2_1 hlo1 hhi1 hra1 hfr1 hcont1 hrs1 hnest1
  have hfr1' : MemFrame S.mem e.mem
      (P.priv ++ [((s.regs 4).toNat - 96 - P.depth, (s.regs 4).toNat - 104), ((s.regs 4).toNat - 73, (s.regs 4).toNat - 73 + 1)]) := by
    refine hfr1.mono fun a n h => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true, rtWin, bitsWin] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, by omega⟩, by omega⟩
  have hW_e : MemFrame s.mem e.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat + 40)]) :=
    hSfW.trans hfr1' fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hwd' : ∀ a n, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - 96 - P.depth ∨ (s.regs 4).toNat - 104 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 73 ∨ (s.regs 4).toNat - 64 ≤ a) → e.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    rw [hfr1'.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h1, by omega, by omega⟩)]
  have hwd : ∀ a, Outside a 8 P.priv → (a + 8 ≤ (s.regs 4).toNat - 96 - P.depth ∨ (s.regs 4).toNat - 104 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 73 ∨ (s.regs 4).toNat - 64 ≤ a) → e.mem.readLE a 8 = S.mem.readLE a 8 :=
    fun a => hwd' a 8
  have hm_fv2 : e.mem.readLE ((s.regs 4).toNat - 64) 8 = func2A := by
    rw [hwd _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hfv2
  have hm_c2t : e.mem.readLE ((s.regs 4).toNat - 64 + 8) 8 = e2t.toNat := by
    rw [show (s.regs 4).toNat - 64 + 8 = (s.regs 4).toNat - 56 by omega]
    rw [hwd _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hcap2t
  have hm_c2d : e.mem.readLE ((s.regs 4).toNat - 64 + 16) 8 = e2d.toNat := by
    rw [show (s.regs 4).toNat - 64 + 16 = (s.regs 4).toNat - 48 by omega]
    rw [hwd _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hcap2d
  have hgv : e.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hW_e.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hgo, by omega⟩)]
  have hga : e.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by
    rw [hW_e.accessible]; exact hgr
  have hwin : e.mem.accessible ((s.regs 4).toNat - (P.depth + (P.depth + 128)))
      (P.depth + (P.depth + 128) + 40) true = true := by
    rw [hW_e.accessible]; exact hst
  have hpn_e : P.panics e.mem (gOf s) =
      { arg := ⟨e1t.toNat, e1d.toNat⟩, start := (s.regs 4).toNat - 96 } :: P.panics s.mem (gOf s) := by
    have := hpn1
    rw [hS0, hS3, hfsp, hgS, hl.panics_frame _ _ _ hagS, hS14] at this
    exact this
  rw [hm_fv2] at hpc1
  have hS14' : e.regs 14 = s.regs 14 := by rw [h14_1, hS14]
  refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
  obtain ⟨j2, S2, hj2, hS2pc, hS2sp, hS20, hS23, hS214, hS25, hS2x, hS2df, hS2f, hS2ra⟩ :=
    cl2 impl e e2t e2d ((s.regs 4).toNat - 64) hpc1 (by rw [h2_1]) (by omega) (by omega) hm_c2t hm_c2d
      (by rw [hW_e.accessible]; exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)))
      (by rw [hW_e.accessible]; exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)))
      (by rw [hS14', hgv]; omega) (by rw [hS14']; exact hga) (by rw [hS14']; omega) (by omega)
      (by rw [hW_e.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
  refine GoReturns.of_steps (hj2.withExit hret.fetch_none) ?_
  have h32 : (e.regs 4 - 32#64).toNat = (e.regs 4).toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
  have hS2spn : (S2.regs 4).toNat = (e.regs 4).toNat - 32 := by rw [hS2sp]; exact h32
  have hS214' : S2.regs 14 = s.regs 14 := by rw [hS214, hS14']
  have hS2x' : S2.xmm 15 = 0 := by rw [hS2x]; exact hx1
  have hS2df' : S2.df = false := by rw [hS2df]; exact hdf1
  have hgS2 : gOf S2 = gOf s := by simp only [gOf, hS214']
  have hS2fW : MemFrame s.mem S2.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat + 40)]) :=
    hW_e.trans hS2f fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      omega⟩
  have hagE : Spec.Map.Agrees e.mem S2.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (e.regs 4).toNat - 32) (hi := (e.regs 4).toNat) hS2f
      (Outside.of_sub hout (by omega) (by omega))
  obtain ⟨fi2, hfi2⟩ : ∃ fi : Spec.FuncInfo, fi = Spec.FuncInfo.named Extracted.funcs
      "example.com/basic.NestedRecover.func2" := ⟨_, rfl⟩
  have f2_frame : fi2.frame = 24 := by rw [hfi2]; rfl
  have f2_od : fi2.openDefer = none := by rw [hfi2]; rfl
  have f2_res : fi2.resume = func2A := by rw [hfi2]; rfl
  have hdE : P.defers e.mem (gOf s) = P.defers s.mem (gOf s) := by
    have := hd1; rw [hS14] at this; simp only [gOf] at this ⊢; exact this.trans hdsS
  have hdS2 : P.defers S2.mem (gOf S2) = P.defers s.mem (gOf s) := by
    rw [hgS2, hl.defers_frame _ _ _ hagE, hdE]
  have hds2 : ∀ d ∈ P.defers S2.mem (gOf S2), (S2.regs 4).toNat + 8 < d.sp := by
    intro d hd; rw [hdS2] at hd; have := hds d hd; omega
  have hfsp2 : fspOf S2 = (e.regs 4).toNat - 24 := by simp only [fspOf, hS2spn]; omega
  have hF2 : frameOf fi2 (fspOf S2) S2.mem = ⟨(e.regs 4).toNat - 24, (e.regs 4).toNat, func2A, none⟩ := by
    simp only [frameOf, Panic.frameOf, Spec.FuncInfo.bound, f2_frame, f2_od, hfsp2, f2_res]
    have e3 : (e.regs 4).toNat - 24 + 24 = (e.regs 4).toNat := by omega
    rw [e3]
  have hri2 : recItems ((e.regs 4).toNat - 24) (P.defers S2.mem (gOf S2)) = [] :=
    recItems_above (by rw [← hfsp2]; exact hds2)
  have hI2 : frameItems S2.mem (frameOf fi2 (fspOf S2) S2.mem) (P.defers S2.mem (gOf S2)) = [] := by
    rw [hF2]; simp only [frameItems, List.nil_append, hri2]
  have hrmS : P.room S.mem (gOf S) = P.room s.mem (gOf s) := by rw [hgS, hl.room_frame _ _ _ hagS]
  have hrmE : P.room s.mem (gOf s) ≤ P.room e.mem (gOf s) + 1 := by
    have := hrm1; rw [hS14] at this; simp only [gOf] at this ⊢; rw [hrmS] at this; simp only [gOf] at this; omega
  have hroomS2 : P.room S2.mem (gOf S2) = P.room e.mem (gOf s) := by
    rw [hgS2, hl.room_frame _ _ _ hagE]
  refine GopanicContract.apply (fi := fi2) hpan hS2pc (by rw [hS2ra, hfi2]; rfl) ?_ ?_
  · refine ⟨PanicPre.of_within hc hS2fW (hl.env_frame _ _ henv1 hagE) (by omega) (by omega)
        (by omega) hS214' hS2x' hS2df' (by rw [hS2ra]; decide),
      by rw [hS20]; exact hne2, ?_, ?_, ?_⟩
    · rw [hroomS2]; omega
    · intro h; rw [f2_od] at h; cases h
    · rw [hI2, hF2]; exact ⟨⟨trivial, fun it h => absurd h (by simp)⟩, fun it h => absurd h (by simp)⟩
  intro hE2
  rw [hI2, hF2] at hE2
  rw [Engine_nil] at hE2
  obtain ⟨k2, d, hst2, hU, hpd, hdd, hdfr, hdenv, hdrm, hdsv⟩ := hE2
  refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
  have hS14g : (S.regs 14).toNat = gOf s := by simp [gOf, hS14]
  have hS2g : (S2.regs 14).toNat = gOf s := by simp [gOf, hS214']
  have hS2f' : MemFrame e.mem S2.mem (P.priv ++ [((e.regs 4).toNat - 24 - P.depth, (e.regs 4).toNat)]) :=
    hS2f.mono fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      omega
  have hWd : MemFrame e.mem d.mem (P.priv ++ [((e.regs 4).toNat - 24 - P.depth, (e.regs 4).toNat)]) :=
    hS2f'.trans hdfr fun a n h => ⟨h, by
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega⟩⟩
  have hU' : U d (S.regs 14).toNat (e.regs 4).toNat := by
    rw [hS14g, ← hS2g]; exact hU
  have hAg : Spec.Map.Agrees e.mem d.mem
      [((e.regs 4).toNat, (s.regs 4).toNat - 96), ((s.regs 4).toNat - 73, (s.regs 4).toNat - 73 + 1),
        ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8), ((s.regs 4).toNat - 24, (s.regs 4).toNat - 24 + 8),
        ((s.regs 4).toNat - 64, (s.regs 4).toNat - 64 + 8), ((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 8)] := by
    refine Spec.Map.Agrees.of_memFrame hWd fun a ⟨r, hr, h1, h2⟩ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [outside_append, outside_cons, outside_nil, and_true]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at h1 h2 <;>
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩
  have hdef' : P.defers d.mem (S.regs 14).toNat = P.defers e.mem (S.regs 14).toNat := by
    rw [hS14g, ← hS2g, hdd, (frameRecs_above (sp := (e.regs 4).toNat - 24) (by rw [← hfsp2]; exact hds2)).2, hdS2]
    rw [hS2g, hdE]
  have hsv' : P.saved d.mem (S.regs 14).toNat = P.saved e.mem (S.regs 14).toNat := by
    rw [hS14g, ← hS2g, hdsv, hS2g, ← hgS2, hl.saved_frame _ _ _ hagE]
  have hpnS : P.panics S.mem (gOf S) = P.panics s.mem (gOf s) := by rw [hgS, hl.panics_frame _ _ _ hagS]
  have hpnS2 : P.panics S2.mem (gOf S2) =
      { arg := ⟨e1t.toNat, e1d.toNat⟩, start := (s.regs 4).toNat - 96 } :: P.panics s.mem (gOf s) := by
    rw [hgS2, hl.panics_frame _ _ _ hagE]; exact hpn_e
  have hpn' : P.panics d.mem (S.regs 14).toNat =
      { arg := ⟨e2t.toNat, e2d.toNat⟩, start := (e.regs 4).toNat - 24 } ::
      { arg := ⟨(S.regs 0).toNat, (S.regs 3).toNat⟩, start := fspOf S } :: P.panics S.mem (gOf S) := by
    rw [hS14g, ← hS2g, hpd, hpnS2, hpnS, hS0, hS3, hfsp, hS20, hS23, hfsp2]
  have hrm' : P.room S.mem (gOf S) - 1 ≤ P.room d.mem (S.regs 14).toNat + 1 := by
    have a1 : P.room S.mem (gOf S) - 1 ≤ P.room e.mem (gOf s) := by have := hrm1; rwa [hS14g] at this
    have a2 : P.room S2.mem (gOf S2) - 1 ≤ P.room d.mem (gOf s) := by have := hdrm; rwa [hS2g] at this
    rw [hS14g]; omega
  have hE' := hnest1 rfl d { arg := ⟨e2t.toNat, e2d.toNat⟩, start := (e.regs 4).toNat - 24 } hU' hAg hdenv hdef' hsv'
    hpn' rfl rfl (show (e.regs 4).toNat - 24 ≤ (e.regs 4).toNat by omega) hrm'
  rw [Engine_cons] at hE'
  obtain ⟨k3, e3, hst3, ⟨hpc3, h2_3, h14_3, hx3, hdf3, hal3, hlo3, hhi3, hra3, henvE3⟩,
    hfrE3, -, hdE3, hpn3, -, hrsE3, hcont3, -⟩ := hE'
  dsimp only at hpc3 h2_3 hlo3 hhi3 hra3 hfrE3 hcont3 hrsE3
  refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
  rw [ite_eq_right (by decide)] at hrsE3
  have hM_e : MemFrame S.mem e.mem (W2 P s) := hfr1'.mono fun a n h => by
    simp only [W2, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, by omega, by omega⟩
  have hM_d : MemFrame S.mem d.mem (W2 P s) := hM_e.trans hWd fun a n h => ⟨h, by
    simp only [W2, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, by omega⟩⟩
  have hM_e3 : MemFrame S.mem e3.mem (W2 P s) := hM_d.trans hfrE3 fun a n h => ⟨h, by
    simp only [W2, rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, by omega⟩, by omega⟩⟩
  have hW_e3 : MemFrame s.mem e3.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat + 40)]) :=
    hSfW.trans hM_e3 fun a n h => ⟨h, by
      simp only [W2, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hread : ∀ a n, Outside a n P.priv → (s.regs 4).toNat - 40 ≤ a → a + n ≤ (s.regs 4).toNat - 24 →
      e3.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    rw [hfrE3.readLE _ _ (by
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨h1, by omega⟩, by omega⟩),
      hWd.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h1, by omega⟩),
      hwd' a n h1 (by omega) (by omega)]
  have hm_fv : e3.mem.readLE ((s.regs 4).toNat - 40) 8 = func1A := by
    rw [hread _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hfv1
  have hm_cap : e3.mem.readLE ((s.regs 4).toNat - 32) 8 = (s.regs 4).toNat - 72 := by
    rw [hread _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hcap1
  have hpn1' : P.panics e3.mem (gOf s) = [{ arg := ⟨e2t.toNat, e2d.toNat⟩, start := (e.regs 4).toNat - 24 },
      { arg := ⟨e1t.toNat, e1d.toNat⟩, start := (s.regs 4).toNat - 96 }] := by
    have := hpn3
    rw [hS14, hS0, hS3, hfsp, hcalmS] at this
    simpa [gOf] using this
  have hgv3 : e3.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hW_e3.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hgo, by omega⟩)]
  rw [hm_fv] at hpc3
  have hcl := closure_run impl P hl hrec hw s hc e3 e2t.toNat e2d.toNat ((e.regs 4).toNat - 24) _ hpc3
    (by rw [h2_3]) (by rw [h14_3, hS14]) hx3 hdf3 hal3 hlo3 hhi3 hra3 henvE3 hW_e3 hm_cap hpn1' (by
      have h := hrsE3.1; rwa [hS14] at h) hne2
  obtain ⟨k2, c', hst2, -, hcrip, hcsp, hc14, hc5, hcx, hcdf, hcenv, hcpan, hcdef, hcsv, hcrm, hcfr, hc7⟩ := hcl
  refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
  have hagc : Spec.Map.Agrees e3.mem c'.mem (((e3.regs 4).toNat + 8, (s.regs 4).toNat - 96) ::
      [((s.regs 4).toNat - 73, (s.regs 4).toNat - 73 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8),
       ((s.regs 4).toNat - 24, (s.regs 4).toNat - 24 + 8), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 64 + 8),
       ((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 8)]) := by
    refine Spec.Map.Agrees.of_memFrame hcfr fun a ⟨r, hr, h1, h2⟩ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [outside_append, outside_cons, outside_nil, and_true]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at h1 h2 <;>
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩
  have hra64 : e3.mem.readLE (e3.regs 4).toNat 8 < 2 ^ 64 := by omega
  have hdr1 : DeferReturned P (S.regs 14) ((s.regs 4).toNat - 96)
      [((s.regs 4).toNat - 73, (s.regs 4).toNat - 73 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8),
       ((s.regs 4).toNat - 24, (s.regs 4).toNat - 24 + 8), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 64 + 8),
       ((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 8)] e3 c' := by
    refine ⟨?_, hcsp, by rw [hc14, h14_3], by rw [hc5], hcx, hcdf, hagc, hcenv, ?_, ?_, ?_⟩
    · rw [hcrip, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hra64
    · rw [hS14]; exact hcdef
    · rw [hS14]; exact hcsv
    · rw [hS14]; exact hcrm
  have hpanc : P.panics c'.mem (S.regs 14).toNat =
      { arg := ⟨e2t.toNat, e2d.toNat⟩, start := (e.regs 4).toNat - 24, recovered := true } ::
      ({ arg := ⟨(S.regs 0).toNat, (S.regs 3).toNat⟩, start := fspOf S } :: P.panics S.mem (gOf S)) := by
    rw [hS14, hS0, hS3, hfsp, hcalmS]; exact hcpan
  have hr2s : (e.regs 4).toNat - 24 ≤ (s.regs 4).toNat - 96 := by omega
  have hrecov := (hcont3 c' hdr1).2 rfl _ _ rfl hpanc (by
    intro q hq
    rw [hpanc] at hq
    simp only [hcalmS, List.takeWhile, hr2s, hfsp] at hq
    simp at hq
    rcases hq with rfl | rfl <;> rfl)
  obtain ⟨k3, d5, hst3', hdpc, hdsp, hd5, hd14, hdx, hddf, hdfr, hdenv, hdpan, hddef, hdsv, hdroom⟩ := hrecov
  refine GoReturns.of_steps (hst3'.withExit hret.fetch_none) ?_
  have hM_c : MemFrame S.mem c'.mem (W2 P s) := hM_e3.trans hcfr fun a n h => ⟨h, by
    simp only [W2, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, by omega, by omega⟩⟩
  have hM_dm : MemFrame S.mem d5.mem (W2 P s) := hM_c.trans hdfr fun a n h => ⟨h, by
    simp only [W2, rtWin, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, by omega⟩⟩
  obtain ⟨dr, drip, dfl, dxm, dm, dyh, dfs, ddf, dmx⟩ := d5
  dsimp only at hdpc hdsp hd5 hd14 hdx hddf hdfr hdenv hdpan hddef hdsv hdroom hM_dm
  rw [show Extracted.entry + 141 = resumeA from rfl] at hdpc
  subst hdpc hddf
  have hd4v : dr 4 = s.regs 4 - 96#64 := by
    rw [hdsp]; apply BitVec.eq_of_toNat_eq
    have := (s.regs 4).isLt
    rw [BitVec.toNat_ofNat, BitVec.toNat_sub]; simp; omega
  have hd5v : dr 5 = s.regs 4 - 8#64 := by
    rw [hd5]; apply BitVec.eq_of_toNat_eq
    have := (s.regs 4).isLt
    rw [BitVec.toNat_ofNat, BitVec.toNat_sub]; simp; omega
  have hd14v : dr 14 = s.regs 14 := by rw [hd14, hS14]
  have hdr' : dr = setRegF (setRegF (setRegF dr 4 (s.regs 4 - 96#64)) 5 (s.regs 4 - 8#64)) 14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact hd14v
    · rw [if_neg h14]
      by_cases h5 : i = 5
      · rw [if_pos h5, h5]; exact hd5v
      · rw [if_neg h5]
        by_cases h4 : i = 4
        · rw [if_pos h4, h4]; exact hd4v
        · rw [if_neg h4]
  rw [hdr']
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn"))
    hret.fetch_none ?_
  janus64_run until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun D hD => ?_
  have h104' : (s.regs 4 - 104#64).toNat = (s.regs 4).toNat - 104 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hDm : D.mem = Janus.Arm64.Memory.writeLE dm ((s.regs 4).toNat - 104) 8 loc_NestedRecover_146 := by rw [hD]
  have hDsp : D.regs 4 = s.regs 4 - 104#64 := by rw [hD] <;> simp [setRegF]
  have hDspn : (D.regs 4).toNat = (s.regs 4).toNat - 104 := by rw [hDsp]; exact h104'
  have hD14 : D.regs 14 = s.regs 14 := by rw [hD] <;> simp [setRegF]
  have hD5 : D.regs 5 = s.regs 4 - 8#64 := by rw [hD] <;> simp [setRegF]
  have hDx : D.xmm 15 = 0 := by rw [hD]; exact hdx
  have hDdf : D.df = false := by rw [hD]
  have hDpc : D.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by rw [hD] <;> rfl
  have hgD : gOf D = gOf s := by simp only [gOf, hD14]
  have hDra : D.mem.readLE (D.regs 4).toNat 8 = loc_NestedRecover_146 := by
    rw [hDm, hDspn, Janus.Arm64.Memory.readLE_writeLE_self]
  have hagD : Spec.Map.Agrees dm D.mem P.priv := by
    rw [hDm]
    exact Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - 104) (hi := (s.regs 4).toNat - 96)
      (by janus_frame) (Outside.of_sub hout (by omega) (by omega))
  simp only [rtWin] at hdfr
  have hWC : MemFrame s.mem c'.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat + 40)]) :=
    hW_e3.trans hcfr fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hWD : MemFrame s.mem dm
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat + 40)]) :=
    hWC.trans hdfr fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega⟩⟩
  have hWD' : MemFrame s.mem D.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat + 40)]) := by
    rw [hDm]
    exact hWD.writeLE (a := (s.regs 4).toNat - 104) (k := 8) loc_NestedRecover_146
      (r := ((s.regs 4).toNat - (P.depth + (P.depth + 128)), (s.regs 4).toNat + 40))
      (List.mem_append_right _ (List.mem_singleton.2 rfl)) (by omega) (by omega)
  have hsvD : P.saved D.mem (gOf D) = none := by
    rw [hgD, hl.saved_frame _ _ _ hagD]
    have := hdsv
    rw [if_pos (by decide), hS14] at this
    exact this
  have hdefD : P.defers D.mem (gOf D) = P.defers s.mem (gOf s) := by
    rw [hgD, hl.defers_frame _ _ _ hagD]
    have h1 := hddef
    have h2 := hcdef
    have h3 := hdE3
    simp only [gOf, hS14] at h1 h2 h3 hdsS ⊢
    rw [h1, h2, h3]; exact hdsS
  have hfspD : fspOf D = (s.regs 4).toNat - 96 := by simp only [fspOf, hDspn]; omega
  have hF2 : retFrame P D = ⟨(s.regs 4).toNat - 96, (s.regs 4).toNat - 96, 0, none⟩ := by
    simp only [retFrame, hsvD, hfspD]
  have hds'' : ∀ d ∈ P.defers s.mem (gOf s), (s.regs 4).toNat - 96 < d.sp := fun d hd => by
    have := hds d hd; omega
  have hdI : frameItems D.mem (retFrame P D) (P.defers D.mem (gOf D)) = [] := by
    rw [hF2, hdefD]; simp only [frameItems, List.nil_append, recItems_above hds'']
  have hpre : PanicPre P 0 D := PanicPre.of_within hc hWD' (hl.env_frame _ _ hdenv hagD) (by omega) (by omega)
    (by omega) hD14 hDx hDdf (by rw [hDra]; decide)
  refine DeferreturnContract.apply (S := D) hdr hDpc ⟨hpre, ?_⟩ ?_
  · rw [hdI, hF2]; exact ⟨⟨trivial, fun it h => absurd h (by simp)⟩, fun it h => absurd h (by simp)⟩
  intro hE
  rw [hdI, Engine_nil] at hE
  obtain ⟨k4, d2, hst4, hfin⟩ := hE
  obtain ⟨hfpc, hfsp', hf14, hf5, hfx, hfdf, hfmf, hfenv, -⟩ := hfin
  refine GoReturns.of_steps (hst4.withExit hret.fetch_none) ?_
  obtain ⟨er, erip, efl, exm, em, eyh, efs, edf, emx⟩ := d2
  dsimp only at hfpc hfsp' hf14 hf5 hfx hfdf hfmf hfenv
  rw [hDra] at hfpc
  have hepc : erip = BitVec.ofNat 64 loc_NestedRecover_146 := by
    apply BitVec.eq_of_toNat_eq; rw [hfpc, BitVec.toNat_ofNat]
  subst hepc hfdf
  have he4v : er 4 = s.regs 4 - 96#64 := by
    rw [hfsp', hDsp]; apply BitVec.eq_of_toNat_eq
    have := (s.regs 4).isLt
    rw [BitVec.toNat_add, BitVec.toNat_sub]; simp; omega
  have he5v : er 5 = s.regs 4 - 8#64 := by rw [hf5, hD5]
  have he14v : er 14 = s.regs 14 := by rw [hf14, hD14]
  have her : er = setRegF (setRegF (setRegF er 4 (s.regs 4 - 96#64)) 5 (s.regs 4 - 8#64)) 14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact he14v
    · rw [if_neg h14]
      by_cases h5 : i = 5
      · rw [if_pos h5, h5]; exact he5v
      · rw [if_neg h5]
        by_cases h4 : i = 4
        · rw [if_pos h4, h4]; exact he4v
        · rw [if_neg h4]
  rw [her]
  simp only [rtWin, bitsWin, hF2, List.append_nil] at hfmf
  have hxfer : ∀ a n v, Outside a n P.priv → (s.regs 4).toNat - 8 ≤ a → a + n ≤ (s.regs 4).toNat + 8 →
      S.mem.readLE a n = v → em.readLE a n = v := by
    intro a n v hpr h1 h2 hv
    rw [hfmf.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpr, by omega⟩), hDm,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [← hv]
    exact (hM_dm.readLE _ _ (by
      simp only [W2, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpr, by omega, by omega⟩)).symm.symm
  have hfpE : em.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    refine hxfer _ _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) ?_
    exact hSrbp
  have hlrE : em.readLE (s.regs 4).toNat 8 = ret := by
    refine hxfer _ _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) hSret
  have h7E : em.readLE ((s.regs 4).toNat - 72) 8 = 7 := by
    rw [hfmf.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩), hDm,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hdfr.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩)]
    exact hc7
  have hacE : em.accessible ((s.regs 4).toNat - 96) 104 true = true := by
    rw [hfmf.accessible, hWD'.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
  refine GoReturns.of_reaches ?_
  janus64_run [hlrE]
  exact hfx

namespace Witness

open Janus.Contracts.PanicSat (tabWords witMem witRet witArg)
open Janus.Contracts.PanicSatAmd64
open Janus.Contracts.PanicModel

abbrev T0 : List Spec.FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : Spec.PanicRuntime := P0 T0 RPa

def gA : Nat := Extracted.program.contractAddr "runtime.gopanic"
def rA : Nat := Extracted.program.contractAddr "runtime.gorecover"
def dA : Nat := Extracted.program.contractAddr "runtime.deferreturn"

/-- The code linked next to `NestedRecover`: the model engine and a `jmp` to it at each contract
address. -/
def implW : List Janus.Amd64.Segment :=
  panicImpl Extracted.program [("runtime.gopanic", eGopanic), ("runtime.gorecover", eGorecover),
    ("runtime.deferreturn", eDeferreturn)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

set_option maxRecDepth 100000 in
theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubG : StubAt (Extracted.program.link implW) gA eGopanic :=
  StubAt.of_jmp (bs := stubCode gA eGopanic) (rel := (eGopanic + 2 ^ 64 - (gA + 5)) % 2 ^ 64) (len := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubR : StubAt (Extracted.program.link implW) rA eGorecover :=
  StubAt.of_jmp (bs := stubCode rA eGorecover) (rel := (eGorecover + 2 ^ 64 - (rA + 5)) % 2 ^ 64) (len := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubD : StubAt (Extracted.program.link implW) dA eDeferreturn :=
  StubAt.of_jmp (bs := stubCode dA eDeferreturn) (rel := (eDeferreturn + 2 ^ 64 - (dA + 5)) % 2 ^ 64) (len := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem hpan : GopanicContract (Extracted.program.link implW) gA PW U1 T0 :=
  gopanic_at stubG (gopanic_run engineAt T0 tok)

theorem hrec : GorecoverContract (Extracted.program.link implW) rA PW :=
  gorecover_at stubR (gorecover_run engineAt T0)

theorem hdr : DeferreturnContract (Extracted.program.link implW) dA PW U1 :=
  deferreturn_at stubD (deferreturn_run (T := T0) engineAt)

abbrev ret : Nat := witRet

/-- Memory: the model's table and runtime range writable, a stack (a region of the witness memory) holding the
return address `ret` at `[wsp]`, the goroutine readable. -/
def wmW : Janus.Arm64.Memory := witMem (tabWords T0 ++ [(wsp, ret)])

theorem env_w : Env0 T0 wmW := by
  unfold Env0
  have hnd : ndef wmW = 0 := by decide
  refine ⟨by decide, by decide, by decide, fun i hi => ?_, ?_⟩
  · omega
  · unfold TableOK
    exact ⟨by decide, by decide, by decide⟩

theorem hret : RetAddr (Extracted.program.link implW) ret := RetAddr.of_check (by decide)

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg
      else if i = 0 then 1#64 else if i = 1 then 2#64 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmW }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [1#64, 0#64, 2#64, 0#64] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, fun i h => ?_, rfl⟩
  simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem pre : PanicCallerOK PW s0 (PW.depth + 128) 40 ∧ PW.Calm s0.mem (s0.regs 14).toNat ∧
    (1#64 : BitVec 64).toNat ≠ 0 ∧ (2#64 : BitVec 64).toNat ≠ 0 ∧ 2 ≤ PW.room s0.mem (gOf s0) ∧
    (∀ d ∈ PW.defers s0.mem (gOf s0), (s0.regs regSP).toNat ≤ d.sp) ∧
    ¬ PW.wrapper (segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 0x1b) := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩,
    ?_, by decide, by decide, ?_, ?_, id⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · show panics0 wmW = []
    rw [panics0_eq]; decide
  · show 2 ≤ room0 wmW
    rw [room0_eq]; decide
  · intro d hd
    have hnd : ndef wmW = 0 := by decide
    have : defers0 wmW = [] := by rw [defers0_eq, hnd]; rfl
    exact absurd hd (by rw [show PW.defers s0.mem (gOf s0) = defers0 wmW from rfl, this]; simp)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime)
    (U : Janus.Amd64.State → Nat → Nat → Prop) (ret : Nat) (s : Janus.Amd64.State), P.Laws ∧
    GopanicContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gopanic") P U
      Extracted.funcs ∧
    GorecoverContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gorecover") P ∧
    DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P U ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [1#64, 0#64, 2#64, 0#64] s ∧
    (PanicCallerOK P s (P.depth + 128) 40 ∧ P.Calm s.mem (s.regs 14).toNat ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧
      (2#64 : BitVec 64).toNat ≠ 0 ∧ 2 ≤ P.room s.mem (gOf s) ∧
      (∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp) ∧
      ¬ P.wrapper (segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 0x1b)) :=
  ⟨implW, PW, U1, ret, s0, P0_laws T0 RPa, hpan, hrec, hdr, hret, setup, pre⟩

/-- So the guarantee is reached: `NestedRecover` panics, the nested panic is recovered by the
remaining deferred call, and the call returns `7`. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClassU PW U1 s0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ (s'.regs 0).toNat = 7
    | .panicked _ _ => False
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U1 hpan hrec hdr 1#64 0#64 2#64 0#64 ret hret s0 setup pre

end Witness

end Proof
