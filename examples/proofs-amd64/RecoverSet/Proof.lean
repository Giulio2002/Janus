import Janus
import Extracted

/-! `example.com/basic.RecoverSet(x, e any) (r uint64)` on amd64: for `x ≤ 10` it returns `x`
(the deferred closure's `recover()` returns `nil`); for `x > 10`, `panic(e)` enters
`runtime.gopanic`, which runs the open-coded deferred closure; its `recover()` returns `e`, so it
sets `r = 7`; the runtime resumes the frame at its `deferreturn` call, which returns, and the call
returns `7`. Example 3 of docs/COVERAGE.md R6; contracts `Janus.Contracts.PanicAmd64` (pinned),
instantiated with the funcdata (`deferBits` at `RSP + 23`, slot at `RSP + 48`, `deferreturn` at
`entry + 0x86`, the body `RSP` being `RSP + 8` at `gopanic`'s entry). -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64
open Janus.Contracts.MapAmd64 (keepABI_apply)
open Janus.Contracts.Panic (frameItems openItems frameKeep bitsWin recItems recItems_above)
open Janus.Spec (openBits)

/-! Code addresses are evaluated from the extraction (`janus_eval%`), so a relinked binary needs
no edit: the deferred closure's entry, its return point after `CALL runtime.gorecover`, and the
`deferreturn` call the runtime resumes at. -/
local macro "func1A" : term =>
  `(janus_eval% (segAddr Extracted.program "example.com/basic.RecoverSet.func1"))
local macro "recoverRet" : term =>
  `(janus_eval% (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x1b))
local macro "resumeA" : term => `(janus_eval% (Extracted.entry + 0x86))

set_option maxHeartbeats 0 in
/-- The deferred closure `RecoverSet.func1` run by the runtime during a panic: it calls `recover()`,
which returns the panic's value, so it sets the named result to `7` and returns. -/
theorem closure_run (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (hrec : GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") P)
    (hw : ¬ P.wrapper (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x1b))
    (s : State) (hc : PanicCallerOK P s (P.depth + 96) 32) (e : State) (etyp edata : Nat)
    (hpe : e.rip = BitVec.ofNat 64 func1A) (hrdx : e.regs 2 = BitVec.ofNat 64 ((s.regs 4).toNat - 32))
    (h14 : e.regs 14 = s.regs 14) (hx : e.xmm 15 = 0) (hdf : e.df = false)
    (hal : (e.regs 4).toNat % 8 = 0) (hlo : (s.regs 4).toNat - 64 - P.depth ≤ (e.regs 4).toNat)
    (hhi : (e.regs 4).toNat + 16 ≤ (s.regs 4).toNat - 64)
    (hra : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 47) (henv : P.Env e.mem)
    (hW : MemFrame s.mem e.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 96)), (s.regs 4).toNat + 32)]))
    (hcap : e.mem.readLE ((s.regs 4).toNat - 24) 8 = (s.regs 4).toNat - 40)
    (hpan : P.panics e.mem (s.regs 14).toNat = [{ arg := ⟨etyp, edata⟩, start := (s.regs 4).toNat - 64 }])
    (hrp : P.rp e.mem (s.regs 14).toNat = e.mem.readLE (e.regs 4).toNat 8)
    (hne : etyp ≠ 0) :
    ReachesRet (Extracted.program.link impl) (retAddrOf e) e (fun c' =>
      c'.rip = retAddrOf e ∧ c'.regs 4 = e.regs 4 + 8 ∧ c'.regs 14 = e.regs 14 ∧ c'.regs 5 = e.regs 5 ∧
      c'.xmm 15 = 0 ∧ c'.df = false ∧ P.Env c'.mem ∧
      P.panics c'.mem (s.regs 14).toNat =
        [{ arg := ⟨etyp, edata⟩, start := (s.regs 4).toNat - 64, recovered := true }] ∧
      P.defers c'.mem (s.regs 14).toNat = P.defers e.mem (s.regs 14).toNat ∧
      P.saved c'.mem (s.regs 14).toNat = P.saved e.mem (s.regs 14).toNat ∧
      P.room e.mem (s.regs 14).toNat ≤ P.room c'.mem (s.regs 14).toNat ∧
      MemFrame e.mem c'.mem (P.priv ++ [((e.regs 4).toNat - 24 - P.depth, (e.regs 4).toNat),
        ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)]) ∧
      c'.mem.readLE ((s.regs 4).toNat - 40) 8 = 7) := by
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
  have hwin' : e.mem.accessible ((s.regs 4).toNat - (P.depth + (P.depth + 96)))
      (P.depth + (P.depth + 96) + 32) true = true := by
    rw [hW.accessible]; exact hst
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpe hdf
  have hcr : cr = setRegF (setRegF cr 2 (BitVec.ofNat 64 ((s.regs 4).toNat - 32))) 14 (s.regs 14) := by
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
  have hGra : G.mem.readLE (G.regs 4).toNat 8 = 4742395 := by
    rw [hG]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, hc24, Janus.Arm64.Memory.readLE_writeLE_self]
  have hgG : gOf G = (s.regs 14).toNat := by simp only [gOf, hG14]
  have hGfW : MemFrame s.mem G.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 96)), (s.regs 4).toNat + 32)]) :=
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
  have hsegf : segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x1b = 4742395 := by decide
  have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have hpanG : P.panics G.mem (gOf G) = [{ arg := ⟨etyp, edata⟩, start := (s.regs 4).toNat - 64 }] := by
    rw [hgG, hl.panics_frame _ _ _ hagG]; exact hpan
  have hrpG : G.mem.readLE ((G.regs 5).toNat + 8) 8 = P.rp G.mem (gOf G) := by
    rw [hG5n, show (cr 4).toNat - 8 + 8 = (cr 4).toNat by omega, hgG, hl.rp_frame _ _ _ hagG, hrp]
    exact hGf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  obtain ⟨hr0, hr1, hrec2⟩ := hpanI _ [] hpanG rfl rfl (by rw [hGra, ← hsegf]; exact hw) hrpG
  subst hs2
  have hdf2' : P.defers m2 (s.regs 14).toNat = P.defers cm (s.regs 14).toNat := by
    have h := hdf2; rw [hgG] at h; exact h.trans (hl.defers_frame _ _ _ hagG)
  have hsv2' : P.saved m2 (s.regs 14).toNat = P.saved cm (s.regs 14).toNat := by
    have h := hsv2; rw [hgG] at h; exact h.trans (hl.saved_frame _ _ _ hagG)
  have hrm2' : P.room cm (s.regs 14).toNat ≤ P.room m2 (s.regs 14).toNat := by
    have h := hrm2; rw [hgG] at h
    exact Nat.le_trans (Nat.le_of_eq (hl.room_frame _ _ _ hagG).symm) h
  have hpanM2 : P.panics m2 (s.regs 14).toNat =
      [{ arg := ⟨etyp, edata⟩, start := (s.regs 4).toNat - 64, recovered := true }] := by
    have h := hrec2; rw [hgG] at h; exact h
  simp only [MapAmd64.calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, hGspn, keepABI_apply] at hfr2 hr0 hr1 henv2
  have hj0 : r2 0 ≠ 0 := fun h => hne (by rw [← hr0, h]; rfl)
  have hGra' : G.mem.readLE ((cr 4).toNat - 24) 8 = 4742395 := by rw [← hGspn]; exact hGra
  clear hpanI hnil2 hpanG hrpG hGacc hGra hGfW hGx hGdf hGpc hG14 hG5 hG5n hGsp hGspn hgG hdf2 hsv2 hrp2 hrm2 hpc2 hrec2
  subst hG
  have hcap' : cm.readLE ((s.regs 4).toNat - 32 + 8) 8 = (s.regs 4).toNat - 40 := by
    rw [show (s.regs 4).toNat - 32 + 8 = (s.regs 4).toNat - 24 by omega]; exact hcap
  have hacc7 : m2.accessible ((s.regs 4).toNat - 40) 8 true = true := by
    rw [hfr2.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_mono _ hwin' (by omega) (by omega)
  janus64_run [hcap']
  all_goals first
    | (exfalso; exact hj0 (BitVec.eq_of_toNat_eq (by simpa using ‹(r2 0).toNat = 0›)))
    | (have hag7 : Spec.Map.Agrees m2 (Janus.Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 40) 8 7) P.priv :=
         Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - 40) (hi := (s.regs 4).toNat - 32)
           (by janus_frame) (Outside.of_sub hout (by omega) (by omega))
       refine ⟨hx, hl.env_frame _ _ henv2 hag7, (hl.panics_frame _ _ _ hag7).trans hpanM2,
         (hl.defers_frame _ _ _ hag7).trans hdf2', (hl.saved_frame _ _ _ hag7).trans hsv2',
         Nat.le_trans hrm2' (Nat.le_of_eq (hl.room_frame _ _ _ hag7).symm), ?_⟩
       try simp only [List.cons_append, List.nil_append]
       janus_frame)

set_option maxHeartbeats 0 in
theorem correctness (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hpan : GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs)
    (hrec : GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U)
    (hw : ¬ P.wrapper (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x1b))
    (x etyp edata : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [x, etyp, edata]
      (fun s => PanicCallerOK P s (P.depth + 96) 32 ∧ P.Calm s.mem (s.regs 14).toNat ∧
        etyp.toNat ≠ 0 ∧ 0 < P.room s.mem (gOf s) ∧
        ∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp)
      (fun _ => goClass P)
      (fun _ s' => (s'.regs 0).toNat = if x.toNat ≤ 10 then x.toNat else 7)
      (fun _ _ _ => False) := by
  intro ret hret s hs ⟨hc, hcalm, hne, hroom, hds⟩
  have hc' := hc
  obtain ⟨henv, hg, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd hb hal hds
  by_cases hx : x.toNat ≤ 10
  · refine GoReturns.of_reaches ?_
    janus64_run until [Extracted.program.contractAddr "runtime.gorecover"]
    have h96 : (18446744073709551520 + (s.regs 4).toNat) % 18446744073709551616 = (s.regs 4).toNat - 96 := by
      omega
    have h80 : (18446744073709551536 + (s.regs 4).toNat) % 18446744073709551616 = (s.regs 4).toNat - 80 := by
      omega
    refine Reaches.call (Summary.withExit hrec hret) rfl
      ⟨PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_⟩ ?_
    rotate_left 11
    · intro s1 hpc1 hpost
      obtain ⟨⟨r1, x1, y1, f1, m1, hs1, hfr1, henv1⟩, -, -, -, -, hnil1, -⟩ := hpost
      obtain ⟨h0, h3, -⟩ := hnil1 (Or.inl (hl.calm_frame _ _ _ (by simpa [setRegF, gOf] using hcalm)
        (Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + (P.depth + 96)))
          (hi := (s.regs 4).toNat + 32) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))))
      subst hs1
      have h96' : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
        rw [BitVec.toNat_sub]; simp; omega
      simp only [keepABI_apply, reduceIte, Nat.reduceEqDiff] at h0 h3
      simp only [MapAmd64.calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, h96'] at hfr1
      janus64_run
      all_goals first | (simp [hx]; done) | (exfalso; simp_all)
    · simp only [List.cons_append, List.nil_append]; janus_frame
    · apply hl.env_frame _ _ henv
      apply Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + (P.depth + 96)))
        (hi := (s.regs 4).toNat + 32)
      · janus_frame
      · exact Outside.of_sub hout (by omega) (by omega)
    all_goals try (simp [setRegF, h96, h80]; try omega)
    all_goals try (simp only [h96, h80, Janus.Arm64.Memory.readLE_writeLE_self]; decide)
    · exact Janus.Contracts.IfaceModel.acc_read_of_write
        (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
  · have hx' : 10 < x.toNat := by omega
    refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
      hret.fetch_none ?_
    janus64_run until [Extracted.program.contractAddr "runtime.gopanic"]
    refine ReachesRet.done rfl ?_
    refine GoReturns.name fun S hS => ?_
    have h72 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
      rw [BitVec.toNat_sub]; simp; omega
    have hSsp : S.regs 4 = s.regs 4 - 72#64 := by rw [hS] <;> simp [setRegF]
    have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 72 := by rw [hSsp]; exact h72
    have hSpc : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by rw [hS] <;> rfl
    have hS0 : S.regs 0 = etyp := by rw [hS] <;> simp [setRegF]
    have hS3 : S.regs 3 = edata := by rw [hS] <;> simp [setRegF]
    have hS14 : S.regs 14 = s.regs 14 := by rw [hS] <;> simp [setRegF]
    have hSx : S.xmm 15 = 0 := by rw [hS]; exact h_x15
    have hSdf : S.df = false := by rw [hS]
    have hSf : MemFrame s.mem S.mem [((s.regs 4).toNat - (P.depth + (P.depth + 96)), (s.regs 4).toNat + 32)] := by
      rw [hS]; janus_frame
    have hSra : S.mem.readLE (S.regs 4).toNat 8 = 4742309 := by
      rw [hS]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h72, Janus.Arm64.Memory.readLE_writeLE_self]
    have hbits : S.mem.readLE ((s.regs 4).toNat - 41) 1 = 1 := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
    have hslot : S.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 32 := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 have := (s.regs 4).isLt; omega)
    have hfv : S.mem.readLE ((s.regs 4).toNat - 32) 8 = func1A := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      try decide
    have hcap : S.mem.readLE ((s.regs 4).toNat - 24) 8 = (s.regs 4).toNat - 40 := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 have := (s.regs 4).isLt; omega)
    obtain ⟨fi, hfi⟩ : ∃ fi : Spec.FuncInfo, fi = Spec.FuncInfo.named Extracted.funcs "example.com/basic.RecoverSet" :=
      ⟨_, rfl⟩
    have f_frame : fi.frame = 64 := by rw [hfi]; rfl
    have f_od : fi.openDefer = some (33, 8) := by rw [hfi]; rfl
    have f_res : fi.resume = Extracted.entry + 0x86 := by rw [hfi]; rfl
    have hagS : Spec.Map.Agrees s.mem S.mem P.priv :=
      Spec.Map.Agrees.of_window hSf (Outside.of_sub hout (by omega) (by omega))
    have hgS : gOf S = gOf s := by simp only [gOf, hS14]
    have hdsS : P.defers S.mem (gOf S) = P.defers s.mem (gOf s) := by rw [hgS]; exact hl.defers_frame _ _ _ hagS
    have hdsS' : ∀ d ∈ P.defers S.mem (gOf S), (S.regs 4).toNat + 8 < d.sp := by
      intro d hd; rw [hdsS] at hd; have := hds d hd; omega
    have hfsp : fspOf S = (s.regs 4).toNat - 64 := by simp only [fspOf, hSspn]; omega
    have hri : recItems ((s.regs 4).toNat - 64) (P.defers S.mem (gOf S)) = [] :=
      recItems_above (by rw [← hfsp]; exact hdsS')
    have hF : frameOf fi (fspOf S) S.mem =
        ⟨(s.regs 4).toNat - 64, (s.regs 4).toNat, Extracted.entry + 0x86,
          some ((s.regs 4).toNat - 41, (s.regs 4).toNat - 16)⟩ := by
      simp only [frameOf, Panic.frameOf, Spec.FuncInfo.bound, Spec.FuncInfo.bitsAt, Spec.FuncInfo.slotsAt,
        Spec.FuncInfo.varp, f_frame, f_od, hfsp, Option.map_some, Option.getD_some, f_res]
      have e1 : (s.regs 4).toNat - 64 + 64 - 8 - 33 = (s.regs 4).toNat - 41 := by omega
      have e2 : (s.regs 4).toNat - 64 + 64 - 8 - 8 = (s.regs 4).toNat - 16 := by omega
      have e3 : (s.regs 4).toNat - 64 + 64 = (s.regs 4).toNat := by omega
      rw [e1, e2, e3, hbits]; rfl
    have hob : openBits 1 = [0] := by decide
    have hI : frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S)) =
        [{ fn := (s.regs 4).toNat - 32, bits := some 0, chain := P.defers S.mem (gOf S) }] := by
      rw [hF]
      simp only [frameItems, openItems, hbits, hob, List.map_cons, List.map_nil, hri, List.append_nil]
      have e3 : (s.regs 4).toNat - 16 + 8 * 0 = (s.regs 4).toNat - 16 := by omega
      rw [e3, hslot]
    have hSfW : MemFrame s.mem S.mem
        (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 96)), (s.regs 4).toNat + 32)]) :=
      hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
    refine GopanicContract.apply (fi := fi) hpan hSpc (by rw [hSra, hfi]; rfl) ?_ ?_
    · refine ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
          (by rw [hSspn]; omega) hS14 hSx hSdf (by rw [hSra]; decide),
        by rw [hS0]; exact hne, ?_, ?_, ?_⟩
      · rw [hgS, hl.room_frame _ _ _ hagS]; exact hroom
      · intro _
        have e : fi.bitsAt (fspOf S) = (s.regs 4).toNat - 41 := by
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
          rcases hi with rfl
          refine ⟨by omega, ?_, by omega, by dsimp only; omega, Outside.of_sub hout (by omega) (by omega)⟩
          rw [hSf.accessible]
          exact Janus.Contracts.IfaceModel.acc_read_of_write
            (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
        · intro it hit
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
          rcases hit with rfl
          dsimp only
          omega
        · intro it hit
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
          rcases hit with rfl
          dsimp only
          refine ⟨by omega, ?_, ?_, ?_, Outside.of_sub hout (by omega) (by omega), by omega⟩
          · rw [hSf.accessible]; exact Janus.Contracts.IfaceModel.acc_read_of_write
              (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
          · rw [hfv]; try decide
          · rw [hfv]; try decide
        · intro it hit
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
          rcases hit with rfl
          dsimp only
          rw [hfv]; decide
    intro hE
    have hcalmS : P.panics S.mem (gOf S) = [] := by
      rw [hgS]; exact hl.calm_frame _ _ _ hcalm hagS
    have hK : frameKeep S.mem (frameOf fi (fspOf S) S.mem)
        (frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S))) =
        [((s.regs 4).toNat - 41, (s.regs 4).toNat - 41 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8),
         ((s.regs 4).toNat - 32, (s.regs 4).toNat - 32 + 8)] := by
      rw [hI, hF]
      simp only [frameKeep, hbits, hob, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      have e3 : (s.regs 4).toNat - 16 + 8 * 0 = (s.regs 4).toNat - 16 := by omega
      rw [e3]
    rw [hK, hI, hF] at hE
    rw [Engine_cons] at hE
    obtain ⟨k1, e, hst1, ⟨hpc1, h2e, h14e, hxe, hdfe, hal1, hlo1, hhi1, hra1, henv1⟩,
      hfr1, hb1, hd1, hpn1, hrm1, hrs1, hcont1, -⟩ := hE
    dsimp only at hpc1 h2e hlo1 hhi1 hfr1 hb1 hcont1 hrs1
    rw [if_neg (by decide)] at hrs1
    have hfr1' : MemFrame S.mem e.mem
        (P.priv ++ [((s.regs 4).toNat - 64 - P.depth, (s.regs 4).toNat - 72),
          ((s.regs 4).toNat - 41, (s.regs 4).toNat - 40)]) := by
      refine hfr1.mono fun a n h => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true, rtWin, bitsWin] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨⟨h1, by omega⟩, by omega⟩
    have hW_e : MemFrame s.mem e.mem
        (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 96)), (s.regs 4).toNat + 32)]) :=
      hSfW.trans hfr1' fun a n h => ⟨h, by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
        obtain ⟨h1, h2⟩ := h
        exact ⟨h1, by omega, by omega⟩⟩
    have hm_fv : e.mem.readLE ((s.regs 4).toNat - 32) 8 = func1A := by
      rw [hfr1'.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
      exact hfv
    have hm_cap : e.mem.readLE ((s.regs 4).toNat - 24) 8 = (s.regs 4).toNat - 40 := by
      rw [hfr1'.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
      exact hcap
    rw [hm_fv] at hpc1
    have hpn1' : P.panics e.mem (s.regs 14).toNat =
        [{ arg := ⟨etyp.toNat, edata.toNat⟩, start := (s.regs 4).toNat - 64 }] := by
      have := hpn1
      rw [hS14, hS0, hS3, hcalmS] at this
      simpa [hfsp] using this
    have hcl := closure_run impl P hl hrec hw s hc e etyp.toNat edata.toNat hpc1
      (by rw [h2e]) (by rw [h14e, hS14]) hxe hdfe hal1 hlo1 hhi1 hra1 henv1 hW_e hm_cap hpn1' (by rw [← hS14]; exact hrs1.1) hne
    refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
    obtain ⟨k2, c', hst2, -, hcrip, hcsp, hc14, hc5, hcx, hcdf, hcenv, hcpan, hcdef, hcsv, hcrm, hcfr, hc7⟩ := hcl
    refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
    have hagc : Spec.Map.Agrees e.mem c'.mem (((e.regs 4).toNat + 8, (s.regs 4).toNat - 64) ::
        [((s.regs 4).toNat - 41, (s.regs 4).toNat - 41 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8),
         ((s.regs 4).toNat - 32, (s.regs 4).toNat - 32 + 8)]) := by
      refine Spec.Map.Agrees.of_memFrame hcfr fun a ⟨r, hr, h1, h2⟩ => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [outside_append, outside_cons, outside_nil, and_true]
      rcases hr with rfl | rfl | rfl | rfl <;> simp only at h1 h2 <;>
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩
    have hra64 : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 64 := by omega
    have hdr1 : DeferReturned P (S.regs 14) ((s.regs 4).toNat - 64)
        [((s.regs 4).toNat - 41, (s.regs 4).toNat - 41 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8),
         ((s.regs 4).toNat - 32, (s.regs 4).toNat - 32 + 8)] e c' := by
      refine ⟨?_, hcsp, by rw [hc14, h14e], by rw [hc5], hcx, hcdf, hagc, hcenv, ?_, ?_, ?_⟩
      · rw [hcrip, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hra64
      · rw [hS14]; exact hcdef
      · rw [hS14]; exact hcsv
      · rw [hS14]; exact hcrm
    have hpanc : P.panics c'.mem (S.regs 14).toNat =
        { arg := ⟨(S.regs 0).toNat, (S.regs 3).toNat⟩, start := fspOf S, recovered := true } ::
          P.panics S.mem (gOf S) := by
      rw [hS14, hS0, hS3, hfsp, hcalmS]; exact hcpan
    have hrecov := (hcont1 c' hdr1).2 rfl _ _ rfl hpanc (by
      intro q hq
      rw [hpanc] at hq
      simp only [hcalmS, List.takeWhile] at hq
      split at hq
      · simp at hq; subst hq; rfl
      · simp at hq)
    obtain ⟨k3, d, hst3, hdpc, hdsp, hd5, hd14, hdx, hddf, hdfr, hdenv, hdpan, hddef, hdsv, hdroom⟩ := hrecov
    refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
    obtain ⟨dr, drip, dfl, dxm, dm, dyh, dfs, ddf, dmx⟩ := d
    dsimp only at hdpc hdsp hd5 hd14 hdx hddf hdfr hdenv hdpan hddef hdsv hdroom
    rw [show Extracted.entry + 134 = resumeA from rfl] at hdpc
    subst hdpc hddf
    have hd4v : dr 4 = s.regs 4 - 64#64 := by
      rw [hdsp]; apply BitVec.eq_of_toNat_eq
      have := (s.regs 4).isLt
      rw [BitVec.toNat_ofNat, BitVec.toNat_sub]; simp; omega
    have hd5v : dr 5 = s.regs 4 - 8#64 := by
      rw [hd5]; apply BitVec.eq_of_toNat_eq
      have := (s.regs 4).isLt
      rw [BitVec.toNat_ofNat, BitVec.toNat_sub]; simp; omega
    have hd14v : dr 14 = s.regs 14 := by rw [hd14, hS14]
    have hdr' : dr = setRegF (setRegF (setRegF dr 4 (s.regs 4 - 64#64)) 5 (s.regs 4 - 8#64)) 14 (s.regs 14) := by
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
    have h72 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
      rw [BitVec.toNat_sub]; simp; omega
    have hDm : D.mem = Janus.Arm64.Memory.writeLE dm ((s.regs 4).toNat - 72) 8 4742315 := by rw [hD]
    have hDsp : D.regs 4 = s.regs 4 - 72#64 := by rw [hD] <;> simp [setRegF]
    have hDspn : (D.regs 4).toNat = (s.regs 4).toNat - 72 := by rw [hDsp]; exact h72
    have hD14 : D.regs 14 = s.regs 14 := by rw [hD] <;> simp [setRegF]
    have hD5 : D.regs 5 = s.regs 4 - 8#64 := by rw [hD] <;> simp [setRegF]
    have hDx : D.xmm 15 = 0 := by rw [hD]; exact hdx
    have hDdf : D.df = false := by rw [hD]
    have hDpc : D.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by rw [hD] <;> rfl
    have hgD : gOf D = gOf s := by simp only [gOf, hD14]
    have hDra : D.mem.readLE (D.regs 4).toNat 8 = 4742315 := by
      rw [hDm, hDspn, Janus.Arm64.Memory.readLE_writeLE_self]
    have hagD : Spec.Map.Agrees dm D.mem P.priv := by
      rw [hDm]
      exact Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - 72) (hi := (s.regs 4).toNat - 64)
        (by janus_frame) (Outside.of_sub hout (by omega) (by omega))
    simp only [rtWin] at hdfr
    have hWC : MemFrame s.mem c'.mem
        (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 96)), (s.regs 4).toNat + 32)]) :=
      hW_e.trans hcfr fun a n h => ⟨h, by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
        obtain ⟨h1, h2⟩ := h
        exact ⟨h1, by omega, by omega⟩⟩
    have hWD : MemFrame s.mem dm
        (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 96)), (s.regs 4).toNat + 32)]) :=
      hWC.trans hdfr fun a n h => ⟨h, by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
        obtain ⟨h1, h2⟩ := h
        exact ⟨h1, by omega⟩⟩
    have hWD' : MemFrame s.mem D.mem
        (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 96)), (s.regs 4).toNat + 32)]) := by
      rw [hDm]
      exact hWD.writeLE (a := (s.regs 4).toNat - 72) (k := 8) 4742315
        (r := ((s.regs 4).toNat - (P.depth + (P.depth + 96)), (s.regs 4).toNat + 32))
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
      have h3 := hd1
      simp only [gOf, hS14] at h1 h2 h3 hdsS ⊢
      rw [h1, h2, h3]; exact hdsS
    have hfspD : fspOf D = (s.regs 4).toNat - 64 := by simp only [fspOf, hDspn]; omega
    have hF2 : retFrame P D = ⟨(s.regs 4).toNat - 64, (s.regs 4).toNat - 64, 0, none⟩ := by
      simp only [retFrame, hsvD, hfspD]
    have hds'' : ∀ d ∈ P.defers s.mem (gOf s), (s.regs 4).toNat - 64 < d.sp := fun d hd => by
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
    obtain ⟨hfpc, hfsp, hf14, hf5, hfx, hfdf, hfmf, hfenv, -⟩ := hfin
    refine GoReturns.of_steps (hst4.withExit hret.fetch_none) ?_
    obtain ⟨er, erip, efl, exm, em, eyh, efs, edf, emx⟩ := d2
    dsimp only at hfpc hfsp hf14 hf5 hfx hfdf hfmf hfenv
    rw [hDra] at hfpc
    have hepc : erip = BitVec.ofNat 64 4742315 := by
      apply BitVec.eq_of_toNat_eq; rw [hfpc, BitVec.toNat_ofNat]
    subst hepc hfdf
    have he4v : er 4 = s.regs 4 - 64#64 := by
      rw [hfsp, hDsp]; apply BitVec.eq_of_toNat_eq
      have := (s.regs 4).isLt
      rw [BitVec.toNat_add, BitVec.toNat_sub]; simp; omega
    have he5v : er 5 = s.regs 4 - 8#64 := by rw [hf5, hD5]
    have he14v : er 14 = s.regs 14 := by rw [hf14, hD14]
    have her : er = setRegF (setRegF (setRegF er 4 (s.regs 4 - 64#64)) 5 (s.regs 4 - 8#64)) 14 (s.regs 14) := by
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
    -- the facts the epilogue reads, carried from the entry state through every frame
    have hxfer : ∀ a n v, Outside a n P.priv → (s.regs 4).toNat - 8 ≤ a → a + n ≤ (s.regs 4).toNat + 8 →
        S.mem.readLE a n = v → em.readLE a n = v := by
      intro a n v hpr h1 h2 hv
      rw [hfmf.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpr, by omega⟩), hDm,
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        hdfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpr, by omega⟩),
        hcfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpr, by omega, by omega⟩)]
      rw [← hv]
      exact hfr1'.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpr, by omega, by omega⟩)
    have hfpE : em.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
      refine hxfer _ _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) ?_
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 have := (s.regs 5).isLt; omega)
    have hlrE : em.readLE (s.regs 4).toNat 8 = ret := by
      refine hxfer _ _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) ?_
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      exact h_ret
    have h7E : em.readLE ((s.regs 4).toNat - 40) 8 = 7 := by
      rw [hfmf.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩), hDm,
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        hdfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩)]
      exact hc7
    have hacE : em.accessible ((s.regs 4).toNat - 64) 72 true = true := by
      rw [hfmf.accessible, hWD'.accessible]
      exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
    refine GoReturns.of_reaches ?_
    janus64_run [hlrE]
    have hSrbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 have := (s.regs 5).isLt; omega)
    refine ⟨⟨?_, hfx⟩, ?_⟩
    · rw [hSrbp]; exact BitVec.ofNat_toNat _ _
    · rw [if_neg hx]

/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSatAmd64` (code that
`PanicSatAmd64Run`/`PanicSatAmd64Entry` prove meets the `gopanic`, `gorecover` and `deferreturn`
contracts in every program that contains it) linked into `RecoverSet`'s program with a `jmp` to it at
each of the three contract addresses, and a call state satisfying the precondition: so `correctness`
applies (`nonvacuous`), and with `x = 42` `RecoverSet` panics, recovers and returns `7`
(`returns`). -/

namespace Witness

open Janus.Contracts.PanicSat (tabWords witMem)
open Janus.Contracts.PanicSatAmd64
open Janus.Contracts.PanicModel

abbrev T0 : List Spec.FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : Spec.PanicRuntime := P0 T0 RPa

def gA : Nat := Extracted.program.contractAddr "runtime.gopanic"
def rA : Nat := Extracted.program.contractAddr "runtime.gorecover"
def dA : Nat := Extracted.program.contractAddr "runtime.deferreturn"

/-- The code linked next to `RecoverSet`: the model engine and a `jmp` to it at each contract
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

def ret : Nat := 0x200000

/-- Memory: the model's table and runtime range writable, a stack `[0x40000, 0x50000)` holding the
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
      else if i = 0 then 42#64 else if i = 3 then 1#64 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmW }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [42#64, 1#64, 0#64] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, fun i h => ?_, rfl⟩
  simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

theorem pre : PanicCallerOK PW s0 (PW.depth + 96) 32 ∧ PW.Calm s0.mem (s0.regs 14).toNat ∧
    (1#64 : BitVec 64).toNat ≠ 0 ∧ 0 < PW.room s0.mem (gOf s0) ∧
    ∀ d ∈ PW.defers s0.mem (gOf s0), (s0.regs regSP).toNat ≤ d.sp := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩,
    ?_, by decide, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · show panics0 wmW = []
    rw [panics0_eq]; decide
  · show 0 < room0 wmW
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
    ¬ P.wrapper (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x1b) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [42#64, 1#64, 0#64] s ∧
    (PanicCallerOK P s (P.depth + 96) 32 ∧ P.Calm s.mem (s.regs 14).toNat ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧
      0 < P.room s.mem (gOf s) ∧ ∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp) :=
  ⟨implW, PW, U1, ret, s0, P0_laws T0 RPa, hpan, hrec, hdr, id, hret, setup, pre⟩

/-- So the guarantee is reached: with `x = 42` `RecoverSet` panics, recovers, and returns `7`. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClass PW) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧
        (s'.regs 0).toNat = if (42#64 : BitVec 64).toNat ≤ 10 then (42#64 : BitVec 64).toNat else 7
    | .panicked _ _ => False
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U1 hpan hrec hdr id 42#64 1#64 0#64 ret hret s0 setup pre

end Witness

end Proof
