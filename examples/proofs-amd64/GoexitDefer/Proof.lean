import Janus
import Extracted

/-!
# `GoexitDefer(p *uint64)`: `runtime.Goexit` runs the deferred call and terminates the goroutine (amd64)

`GoexitDefer` is
`defer func() { if recover() != nil { *p = 99 } else { *p = *p + 1 } }(); runtime.Goexit(); *p = 5`
with an open-coded defer.

**Guarantee (example 4 of docs/COVERAGE.md R6).** For every panic-runtime model `P` satisfying its
laws and every implementation of `runtime.Goexit` and `runtime.gorecover` meeting their contracts
(`Janus.Contracts.PanicAmd64`, pinned to the Go 1.26 runtime's code), every admissible return address
and every call state in which the runtime is usable with room for a record, `p` points to a
writable word outside the runtime's memory and the stack window: the call **never returns and never
panics**; it terminates the goroutine (`GoOutcome.goexited`) with `*p = *p + 1`. `Goexit` pushes a
`_panic` with `goexit` set, so the deferred call's `recover()` returns `nil` (a `Goexit` cannot be
recovered) and it takes the `else` branch; the store `*p = 5` after `Goexit` never happens.
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64
open Janus.Contracts.MapAmd64 (keepABI_apply)
open Janus.Contracts.Panic (frameItems openItems frameKeep bitsWin recItems recItems_above)
open Janus.Spec (openBits)

/-! Code addresses are read off the extraction (`janus_eval%`), never copied: a relinked
binary needs no edit. -/
local macro "loc_GoexitDefer_69" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.GoexitDefer" + 69))
local macro "loc_GoexitDefer_func1_27" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.GoexitDefer.func1" + 27))



local macro "func1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.GoexitDefer.func1"))
local macro "recoverRet" : term =>
  `(janus_eval% (segAddr Extracted.program "example.com/basic.GoexitDefer.func1" + 0x1b))

set_option maxHeartbeats 0 in
/-- The deferred closure `GoexitDefer.func1` run by the runtime during a `Goexit`: its `recover()`
returns `nil` (a `Goexit` is not a panic), so it adds `1` to `*p`. -/
theorem closure_run (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (hrec : GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") P)
    (s : State) (hc : PanicCallerOK P s (P.depth + 64) 16) (e : State) (p : BitVec 64)
    (hpe : e.rip = BitVec.ofNat 64 func1A) (hrdx : e.regs 2 = BitVec.ofNat 64 ((s.regs 4).toNat - 32))
    (h14 : e.regs 14 = s.regs 14) (hx : e.xmm 15 = 0) (hdf : e.df = false)
    (hal : (e.regs 4).toNat % 8 = 0) (hlo : (s.regs 4).toNat - 40 - P.depth ≤ (e.regs 4).toNat)
    (hhi : (e.regs 4).toNat + 16 ≤ (s.regs 4).toNat - 40)
    (hra : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 47) (henv : P.Env e.mem)
    (hW : MemFrame s.mem e.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 64)), (s.regs 4).toNat + 16)]))
    (hcap : e.mem.readLE ((s.regs 4).toNat - 24) 8 = p.toNat)
    (hpv : e.mem.readLE p.toNat 8 = s.mem.readLE p.toNat 8) (hps : s.mem.accessible p.toNat 8 true = true)
    (hpo : Outside p.toNat 8 P.priv)
    (hdj : p.toNat + 8 ≤ (s.regs 4).toNat - (P.depth + (P.depth + 64)) ∨
      (s.regs 4).toNat - (P.depth + (P.depth + 64)) + (P.depth + (P.depth + 64) + 16) ≤ p.toNat)
    (hpan : ∃ r rs, P.panics e.mem (s.regs 14).toNat = r :: rs ∧ r.goexit = true) :
    ReachesRet (Extracted.program.link impl) (retAddrOf e) e (fun c' =>
      c'.rip = retAddrOf e ∧ c'.regs 4 = e.regs 4 + 8 ∧ c'.regs 14 = e.regs 14 ∧ c'.regs 5 = e.regs 5 ∧
      c'.xmm 15 = 0 ∧ c'.df = false ∧ P.Env c'.mem ∧
      P.panics c'.mem (s.regs 14).toNat = P.panics e.mem (s.regs 14).toNat ∧
      P.defers c'.mem (s.regs 14).toNat = P.defers e.mem (s.regs 14).toNat ∧
      P.saved c'.mem (s.regs 14).toNat = P.saved e.mem (s.regs 14).toNat ∧
      P.room e.mem (s.regs 14).toNat ≤ P.room c'.mem (s.regs 14).toNat ∧
      MemFrame e.mem c'.mem (P.priv ++ [((e.regs 4).toNat - 24 - P.depth, (e.regs 4).toNat),
        (p.toNat, p.toNat + 8)]) ∧
      c'.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64) := by
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
  have hwin' : e.mem.accessible ((s.regs 4).toNat - (P.depth + (P.depth + 64)))
      (P.depth + (P.depth + 64) + 16) true = true := by
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
  have hGra : G.mem.readLE (G.regs 4).toNat 8 = loc_GoexitDefer_func1_27 := by
    rw [hG]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, hc24, Janus.Arm64.Memory.readLE_writeLE_self]
  have hgG : gOf G = (s.regs 14).toNat := by simp only [gOf, hG14]
  have hGfW : MemFrame s.mem G.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 64)), (s.regs 4).toNat + 16)]) :=
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
  obtain ⟨⟨r2, x2, y2, f2, m2, zhm2, krm2, hs2, hfr2, henv2⟩, hdf2, hsv2, hrp2, hrm2, hnil2, hpanI⟩ := hpost
  have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  obtain ⟨r, rs, hr, hgx⟩ := hpan
  have hpanG : P.panics G.mem (gOf G) = r :: rs := by
    rw [hgG, hl.panics_frame _ _ _ hagG]; exact hr
  obtain ⟨h0, h3, hpanI'⟩ := hnil2 (Or.inr ⟨r, rs, hpanG, Or.inl hgx⟩)
  subst hs2
  have hdf2' : P.defers m2 (s.regs 14).toNat = P.defers cm (s.regs 14).toNat := by
    have h := hdf2; rw [hgG] at h; exact h.trans (hl.defers_frame _ _ _ hagG)
  have hsv2' : P.saved m2 (s.regs 14).toNat = P.saved cm (s.regs 14).toNat := by
    have h := hsv2; rw [hgG] at h; exact h.trans (hl.saved_frame _ _ _ hagG)
  have hrm2' : P.room cm (s.regs 14).toNat ≤ P.room m2 (s.regs 14).toNat := by
    have h := hrm2; rw [hgG] at h
    exact Nat.le_trans (Nat.le_of_eq (hl.room_frame _ _ _ hagG).symm) h
  have hpanM2 : P.panics m2 (s.regs 14).toNat = P.panics cm (s.regs 14).toNat := by
    have h := hpanI'; rw [hgG] at h
    exact h.trans (hl.panics_frame _ _ _ hagG)
  simp only [MapAmd64.calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, hGspn, keepABI_apply] at hfr2 h0 h3 henv2
  have h0' : r2 0 = 0 := by simpa [keepABI_apply] using h0
  have hGra' : G.mem.readLE ((cr 4).toNat - 24) 8 = loc_GoexitDefer_func1_27 := by rw [← hGspn]; exact hGra
  have hcap' : cm.readLE ((s.regs 4).toNat - 32 + 8) 8 = p.toNat := by
    rw [show (s.regs 4).toNat - 32 + 8 = (s.regs 4).toNat - 24 by omega]; exact hcap
  have hpv2 : m2.readLE p.toNat 8 = s.mem.readLE p.toNat 8 := by
    rw [hfr2.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpo, by omega, by omega⟩), hG]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hpv
  have hpa : cm.accessible p.toNat 8 true = true := by rw [hW.accessible]; exact hps
  have hacc7 : m2.accessible p.toNat 8 true = true := by
    rw [hfr2.accessible, hG]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hpa
  have hacc7r : m2.accessible p.toNat 8 false = true := Janus.Arm64.Memory.accessible_weaken _ hacc7
  clear hpanI hnil2 hpanG hGacc hGra hGfW hGx hGdf hGpc hG14 hG5 hG5n hGsp hGspn hgG hdf2 hsv2 hrp2 hrm2 hpc2 hpanI'
  subst hG
  have hsl : m2.readLE ((cr 4).toNat - 16) 8 = p.toNat := by
    rw [hfr2.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    rw [hcap', h64]; exact Nat.mod_eq_of_lt p.isLt
  have hpn : p.toNat % 2 ^ 64 = p.toNat := Nat.mod_eq_of_lt p.isLt
  janus64_run [hcap', hsl, hpv2, hpn]
  all_goals first
    | (exfalso; apply ‹¬(r2 0).toNat = 0›; simp [h0'])
    | (have hag7 : Spec.Map.Agrees m2 (Janus.Arm64.Memory.writeLE m2 p.toNat 8 (s.mem.readLE p.toNat 8 + 1)) P.priv :=
         Spec.Map.agrees_writeLE m2 _ hpo
       refine ⟨hx, hl.env_frame _ _ henv2 hag7, (hl.panics_frame _ _ _ hag7).trans hpanM2,
         (hl.defers_frame _ _ _ hag7).trans hdf2', (hl.saved_frame _ _ _ hag7).trans hsv2',
         Nat.le_trans hrm2' (Nat.le_of_eq (hl.room_frame _ _ _ hag7).symm), ?_⟩
       try simp only [List.cons_append, List.nil_append]
       janus_frame)

set_option maxHeartbeats 0 in
theorem correctness (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hge : GoexitContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.Goexit") P U Extracted.funcs)
    (hrec : GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") P)
    (p : BitVec 64) :
    EnsuresGoX (Extracted.program.link impl) Extracted.entry [p]
      (fun s => PanicCallerOK P s (P.depth + 64) 16 ∧ Buffer s p 8 true ∧
        Spec.Disjoint p.toNat 8 ((s.regs regSP).toNat - (P.depth + (P.depth + 64))) (P.depth + (P.depth + 64) + 16) ∧
        Outside p.toNat 8 P.priv ∧ 0 < P.room s.mem (gOf s) ∧
        ∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp)
      (goClassU P U)
      (fun _ _ => False)
      (fun _ _ _ => False)
      (fun s s' => s'.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64) := by
  intro ret hret s hs ⟨hc, ⟨hpb, hps⟩, hdj, hpo, hroom, hds⟩
  have hc' := hc
  obtain ⟨henv, hg, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd hb hal hds hdj
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.Goexit"))
    hret.fetch_none ?_
  janus64_run until [Extracted.program.contractAddr "runtime.Goexit"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun S hS => ?_
  have h48 : (s.regs 4 - 48#64).toNat = (s.regs 4).toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hSsp : S.regs 4 = s.regs 4 - 48#64 := by rw [hS] <;> simp [setRegF]
  have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 48 := by rw [hSsp]; exact h48
  have hSpc : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.Goexit") := by rw [hS] <;> rfl
  have hS14 : S.regs 14 = s.regs 14 := by rw [hS] <;> simp [setRegF]
  have hSx : S.xmm 15 = 0 := by rw [hS]; exact h_x15
  have hSdf : S.df = false := by rw [hS]
  have hSf : MemFrame s.mem S.mem [((s.regs 4).toNat - (P.depth + (P.depth + 64)), (s.regs 4).toNat + 16)] := by
    rw [hS]; janus_frame
  have hSra : S.mem.readLE (S.regs 4).toNat 8 = loc_GoexitDefer_69 := by
    rw [hS]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h48, Janus.Arm64.Memory.readLE_writeLE_self]
  have hbits : S.mem.readLE ((s.regs 4).toNat - 33) 1 = 1 := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have hslot : S.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 32 := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 4).isLt; omega)
  have hfv : S.mem.readLE ((s.regs 4).toNat - 32) 8 = func1A := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    try decide
  have hcap : S.mem.readLE ((s.regs 4).toNat - 24) 8 = p.toNat := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := p.isLt; omega)
  obtain ⟨fi, hfi⟩ : ∃ fi : Spec.FuncInfo, fi = Spec.FuncInfo.named Extracted.funcs "example.com/basic.GoexitDefer" :=
    ⟨_, rfl⟩
  have f_frame : fi.frame = 40 := by rw [hfi]; rfl
  have f_od : fi.openDefer = some (25, 8) := by rw [hfi]; rfl
  have f_res : fi.resume = Extracted.entry + 0x68 := by rw [hfi]; rfl
  have hagS : Spec.Map.Agrees s.mem S.mem P.priv :=
    Spec.Map.Agrees.of_window hSf (Outside.of_sub hout (by omega) (by omega))
  have hgS : gOf S = gOf s := by simp only [gOf, hS14]
  have hdsS : P.defers S.mem (gOf S) = P.defers s.mem (gOf s) := by rw [hgS]; exact hl.defers_frame _ _ _ hagS
  have hdsS' : ∀ d ∈ P.defers S.mem (gOf S), (S.regs 4).toNat + 8 < d.sp := by
    intro d hd; rw [hdsS] at hd; have := hds d hd; omega
  have hfsp : fspOf S = (s.regs 4).toNat - 40 := by simp only [fspOf, hSspn]; omega
  have hri : recItems ((s.regs 4).toNat - 40) (P.defers S.mem (gOf S)) = [] :=
    recItems_above (by rw [← hfsp]; exact hdsS')
  have hF : frameOf fi (fspOf S) S.mem =
      ⟨(s.regs 4).toNat - 40, (s.regs 4).toNat, Extracted.entry + 0x68,
        some ((s.regs 4).toNat - 33, (s.regs 4).toNat - 16)⟩ := by
    simp only [frameOf, Panic.frameOf, Spec.FuncInfo.bound, Spec.FuncInfo.bitsAt, Spec.FuncInfo.slotsAt,
      Spec.FuncInfo.varp, f_frame, f_od, hfsp, Option.map_some, Option.getD_some, f_res]
    have e1 : (s.regs 4).toNat - 40 + 40 - 8 - 25 = (s.regs 4).toNat - 33 := by omega
    have e2 : (s.regs 4).toNat - 40 + 40 - 8 - 8 = (s.regs 4).toNat - 16 := by omega
    have e3 : (s.regs 4).toNat - 40 + 40 = (s.regs 4).toNat := by omega
    rw [e1, e2, e3, hbits]; rfl
  have hob : openBits 1 = [0] := by decide
  have hI : frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S)) =
      [{ fn := (s.regs 4).toNat - 32, bits := some 0, chain := P.defers S.mem (gOf S) }] := by
    rw [hF]
    simp only [frameItems, openItems, hbits, hob, List.map_cons, List.map_nil, hri, List.append_nil]
    have e3 : (s.regs 4).toNat - 16 + 8 * 0 = (s.regs 4).toNat - 16 := by omega
    rw [e3, hslot]
  have hSfW : MemFrame s.mem S.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 64)), (s.regs 4).toNat + 16)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  refine GoexitContract.apply (fi := fi) hge hSpc (by rw [hSra, hfi]; rfl) ?_ ?_
  · refine ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
        (by rw [hSspn]; omega) hS14 hSx hSdf (by rw [hSra]; decide), ?_, ?_, ?_⟩
    · rw [hgS, hl.room_frame _ _ _ hagS]; exact hroom
    · intro _
      have e : fi.bitsAt (fspOf S) = (s.regs 4).toNat - 33 := by
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
  have hK : frameKeep S.mem (frameOf fi (fspOf S) S.mem)
      (frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S))) =
      [((s.regs 4).toNat - 33, (s.regs 4).toNat - 33 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8),
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
  have hfr1' : MemFrame S.mem e.mem
      (P.priv ++ [((s.regs 4).toNat - 40 - P.depth, (s.regs 4).toNat - 48),
        ((s.regs 4).toNat - 33, (s.regs 4).toNat - 32)]) := by
    refine hfr1.mono fun a n h => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true, rtWin, bitsWin] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, by omega⟩, by omega⟩
  have hW_e : MemFrame s.mem e.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 64)), (s.regs 4).toNat + 16)]) :=
    hSfW.trans hfr1' fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hm_fv : e.mem.readLE ((s.regs 4).toNat - 32) 8 = func1A := by
    rw [hfr1'.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    exact hfv
  have hm_cap : e.mem.readLE ((s.regs 4).toNat - 24) 8 = p.toNat := by
    rw [hfr1'.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    exact hcap
  rw [hm_fv] at hpc1
  have hpv : e.mem.readLE p.toNat 8 = s.mem.readLE p.toNat 8 := by
    rw [hW_e.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpo, by omega⟩)]
  have hpn1' : ∃ r rs, P.panics e.mem (s.regs 14).toNat = r :: rs ∧ r.goexit = true := by
    refine ⟨{ arg := ⟨0, 0⟩, goexit := true, start := fspOf S }, P.panics S.mem (gOf S), ?_, rfl⟩
    have := hpn1
    rw [hS14] at this
    exact this
  have hcl := closure_run impl P hl hrec s hc e p hpc1 (by rw [h2e]) (by rw [h14e, hS14]) hxe hdfe hal1 hlo1 hhi1
    hra1 henv1 hW_e hm_cap hpv hps hpo hdj hpn1'
  refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
  obtain ⟨k2, c', hst2, -, hcrip, hcsp, hc14, hc5, hcx, hcdf, hcenv, hcpan, hcdef, hcsv, hcrm, hcfr, hcp⟩ := hcl
  refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
  have hagc : Spec.Map.Agrees e.mem c'.mem (((e.regs 4).toNat + 8, (s.regs 4).toNat - 40) ::
      [((s.regs 4).toNat - 33, (s.regs 4).toNat - 33 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8),
       ((s.regs 4).toNat - 32, (s.regs 4).toNat - 32 + 8)]) := by
    refine Spec.Map.Agrees.of_memFrame hcfr fun a ⟨r, hr, h1, h2⟩ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [outside_append, outside_cons, outside_nil, and_true]
    rcases hr with rfl | rfl | rfl | rfl <;> simp only at h1 h2 <;>
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩
  have hra64 : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 64 := by omega
  have hdr1 : DeferReturned P (S.regs 14) ((s.regs 4).toNat - 40)
      [((s.regs 4).toNat - 33, (s.regs 4).toNat - 33 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8),
       ((s.regs 4).toNat - 32, (s.regs 4).toNat - 32 + 8)] e c' := by
    refine ⟨?_, hcsp, by rw [hc14, h14e], by rw [hc5], hcx, hcdf, hagc, hcenv, ?_, ?_, ?_⟩
    · rw [hcrip, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hra64
    · rw [hS14]; exact hcdef
    · rw [hS14]; exact hcsv
    · rw [hS14]; exact hcrm
  have hpanc : P.panics c'.mem (S.regs 14).toNat =
      { arg := ⟨0, 0⟩, goexit := true, start := fspOf S } :: P.panics S.mem (gOf S) := by
    rw [hS14, hcpan]; have := hpn1; rw [hS14] at this; exact this
  have hE1 := (hcont1 c' hdr1).1 hpanc
  rw [Engine_nil] at hE1
  obtain ⟨k3, d, hst3, hU, hpd, -, hfrd, -, -, -⟩ := hE1
  refine GoReturns.goexit (hst3.withExit hret.fetch_none) ?_ ?_
  · refine ⟨?_, { arg := ⟨0, 0⟩, goexit := true, start := fspOf S }, P.panics S.mem (gOf S), ?_, rfl⟩
    · have hg' : gOf s = (S.regs 14).toNat := by simp only [gOf, hS14]
      rw [hg']; exact hU
    · have hg' : gOf s = (S.regs 14).toNat := by simp only [gOf, hS14]
      rw [hg']; exact hpd
  · show d.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64
    rw [hfrd.readLE _ _ (by
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hpo, by omega⟩, by omega⟩)]
    exact hcp

/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSatAmd64` (code that
`PanicSatAmd64Run` proves meets the `Goexit` and `gorecover` contracts in every program that
contains it) linked into `GoexitDefer`'s program with a `jmp` to it at each contract address, and a
call state satisfying the precondition: so `correctness` applies (`nonvacuous`), and `GoexitDefer`
terminates the goroutine from that state (`returns`). -/

namespace Witness

open Janus.Contracts.PanicSat (tabWords witMem witRet witArg)
open Janus.Contracts.PanicSatAmd64
open Janus.Contracts.PanicModel

abbrev T0 : List Spec.FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : Spec.PanicRuntime := P0 T0 RPa

def geA : Nat := Extracted.program.contractAddr "runtime.Goexit"
def rcA : Nat := Extracted.program.contractAddr "runtime.gorecover"

/-- The code linked next to `GoexitDefer`: the model engine and a `jmp` to it at each contract
address. -/
def implW : List Janus.Amd64.Segment :=
  panicImpl Extracted.program [("runtime.Goexit", eGoexit), ("runtime.gorecover", eGorecover)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

set_option maxRecDepth 100000 in
theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubGe : StubAt (Extracted.program.link implW) geA eGoexit :=
  StubAt.of_jmp (bs := stubCode geA eGoexit) (rel := (eGoexit + 2 ^ 64 - (geA + 5)) % 2 ^ 64) (len := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubRc : StubAt (Extracted.program.link implW) rcA eGorecover :=
  StubAt.of_jmp (bs := stubCode rcA eGorecover) (rel := (eGorecover + 2 ^ 64 - (rcA + 5)) % 2 ^ 64) (len := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem hge : GoexitContract (Extracted.program.link implW) geA PW U1 T0 :=
  goexit_at stubGe (goexit_run engineAt T0 tok)

theorem hrec : GorecoverContract (Extracted.program.link implW) rcA PW :=
  gorecover_at stubRc (gorecover_run engineAt T0)

abbrev pA : Nat := witArg
abbrev ret : Nat := witRet

/-- Memory: the model's table and runtime range writable, a stack (a region of the witness memory) holding the
return address `ret` at `[wsp]` (and `*pA`), the goroutine readable. -/
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
      else if i = 0 then BitVec.ofNat 64 pA else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmW }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [BitVec.ofNat 64 pA] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, fun i h => ?_, rfl⟩
  simp at h; subst h; rfl

theorem pre : PanicCallerOK PW s0 (PW.depth + 64) 16 ∧ Buffer s0 (BitVec.ofNat 64 pA) 8 true ∧
    Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 ((s0.regs regSP).toNat - (PW.depth + (PW.depth + 64)))
      (PW.depth + (PW.depth + 64) + 16) ∧
    Outside (BitVec.ofNat 64 pA).toNat 8 PW.priv ∧ 0 < PW.room s0.mem (gOf s0) ∧
    ∀ d ∈ PW.defers s0.mem (gOf s0), (s0.regs regSP).toNat ≤ d.sp := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩,
    ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · show 0 < room0 wmW
    rw [room0_eq]; decide
  · intro d hd
    have hnd : ndef wmW = 0 := by decide
    have : defers0 wmW = [] := by rw [defers0_eq, hnd]; rfl
    exact absurd hd (by rw [show PW.defers s0.mem (gOf s0) = defers0 wmW from rfl, this]; simp)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime)
    (U : Janus.Amd64.State → Nat → Nat → Prop) (ret : Nat) (s : Janus.Amd64.State), P.Laws ∧
    GoexitContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.Goexit") P U
      Extracted.funcs ∧
    GorecoverContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gorecover") P ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 pA] s ∧
    (PanicCallerOK P s (P.depth + 64) 16 ∧ Buffer s (BitVec.ofNat 64 pA) 8 true ∧
      Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 ((s.regs regSP).toNat - (P.depth + (P.depth + 64)))
        (P.depth + (P.depth + 64) + 16) ∧
      Outside (BitVec.ofNat 64 pA).toNat 8 P.priv ∧ 0 < P.room s.mem (gOf s) ∧
      ∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp) :=
  ⟨implW, PW, U1, ret, s0, P0_laws T0 RPa, hge, hrec, hret, setup, pre⟩

/-- So the guarantee is reached: `GoexitDefer` runs its deferred call (which adds 1 to `*p`) and
terminates the goroutine. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClassU PW U1 s0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ False
    | .panicked _ _ => False
    | .goexited s' => s'.mem.readLE (BitVec.ofNat 64 pA).toNat 8 =
        (s0.mem.readLE (BitVec.ofNat 64 pA).toNat 8 + 1) % 2 ^ 64 :=
  correctness implW PW (P0_laws T0 RPa) U1 hge hrec (BitVec.ofNat 64 pA) ret hret s0 setup pre

end Witness

end Proof
