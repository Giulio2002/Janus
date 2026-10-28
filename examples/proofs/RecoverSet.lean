import Extracted

/-!
# `RecoverSet(x uint64, e any) (r uint64)`: `recover` turns a panic into a return (arm64)

**Guarantee (example 3 of docs/COVERAGE.md R6).** `RecoverSet` is
`defer func() { if recover() != nil { r = 7 } }(); if x > 10 { panic(e) }; return x`, with an
open-coded defer. For every panic-runtime model `P` satisfying its laws, every implementation of
`runtime.gopanic`, `runtime.gorecover` and `runtime.deferreturn` meeting their contracts
(`Janus.Contracts.Panic`, pinned to the Go 1.26 runtime's code), and every Go call state in which
no panic is active, the runtime is usable with enough stack (`PanicCallerOK`), and `e` is not nil:

* if `x ≤ 10` the call returns `x` — the deferred closure runs at the exit, its `recover()` returns
  `nil` (no panic), and it leaves `r` alone;
* if `x > 10` the call **returns `7`**: `panic(e)` enters `runtime.gopanic`, which runs the deferred
  closure; its `recover()` returns `e`, so it sets the named result `r = 7`; the runtime resumes
  the frame at its `deferreturn` call, which returns, and the function returns `r`.

It never panics. The `gopanic` contract is instantiated with `RecoverSet`'s funcdata: the
`deferBits` byte at `SP + 39`, the closure slot at `SP + 64`, the `deferreturn` call at
`entry + 0x84`; the deferred closure `RecoverSet.func1` is not a wrapper.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Proof


/-! Code addresses are read off the extraction (`janus_eval%`), never copied: a relinked
binary needs no edit. -/
local macro "loc_RecoverSet_128" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RecoverSet" + 128))
local macro "loc_RecoverSet_136" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RecoverSet" + 136))
local macro "loc_RecoverSet_func1_36" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 36))

/-! Code addresses are evaluated from the extraction (`janus_eval%`), so a relinked binary needs
no edit: the deferred closure's entry, its return point after `BL runtime.gorecover`, and the
`deferreturn` call the runtime resumes at. -/
local macro "func1A" : term =>
  `(janus_eval% (segAddr Extracted.program "example.com/basic.RecoverSet.func1"))
local macro "recoverRet" : term =>
  `(janus_eval% (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 36))
local macro "resumeA" : term => `(janus_eval% (Extracted.entry + 0x84))

set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hpan : GopanicContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gopanic") P U
      Extracted.funcs)
    (hrec : GorecoverContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gorecover") P)
    (hdr : DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P U)
    (x etyp edata : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [x, etyp, edata]
      (fun s => PanicCallerOK P s (P.depth + 112) 32 ∧ P.Calm s.mem (s.regs 28).toNat ∧
        etyp.toNat ≠ 0 ∧ 0 < P.room s.mem (gOf s) ∧ (∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp) ∧
        ¬ P.wrapper (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x24))
      (fun _ => goClass P)
      (fun _ s' => (s'.regs 0).toNat = if x.toNat ≤ 10 then x.toNat else 7)
      (fun _ _ _ => False) := by
  intro ret hret s hs ⟨hc, hcalm, hne, hroom, hds, hw⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd
  by_cases hx : x.toNat ≤ 10
  · -- normal path: the exit calls the closure, whose recover() returns nil
    refine GoReturns.of_reaches ?_
    janus_run until [Extracted.program.contractAddr "runtime.gorecover"]
    refine Reaches.call (Summary.withExit hrec hret) rfl ⟨?_, ?_, ?_⟩ ?_
    rotate_left 3
    · rintro s1 hpc1 ⟨⟨j1, f1, v1, m1, ex1, ep1, hs1, hfr1, henv1⟩, -, -, -, -, hnil1, -⟩
      obtain ⟨h0, h1, -⟩ := hnil1 (Or.inl (hl.calm_frame _ _ _ hcalm
        (Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + (P.depth + 112))) (hi := s.sp.toNat + 32)
          (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))))
      subst hs1
      simp only [calleeStack] at hfr1
      simp only [retStateX, callRegs_apply, List.getD_nil] at h0 h1
      janus_run
      all_goals first | (simp [hx]; done) | (exfalso; simp_all)
    · refine PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_
      · simp only [List.cons_append, List.nil_append]; janus_frame
      · apply hl.env_frame _ _ henv
        apply Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + (P.depth + 112)))
          (hi := s.sp.toNat + 32)
        · janus_frame
        · exact Outside.of_sub hout (by omega) (by omega)
      all_goals (simp [setReg]; try omega)
    · have h120 : (18446744073709551496 + s.sp.toNat) % 18446744073709551616 = s.sp.toNat - 120 := by
        omega
      simp [setReg, h120]
      exact Janus.Contracts.IfaceModel.acc_read_of_write
        (Memory.accessible_mono _ hst (by omega) (by omega))
    · simp [setReg]; omega
  · -- panic path: gopanic runs the closure, whose recover() returns e; it sets r = 7
    have hx' : 10 < x.toNat := by omega
    refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
      hret.fetch_none ?_
    janus_run until [Extracted.program.contractAddr "runtime.gopanic"]
    refine ReachesRet.done rfl ?_
    refine GoReturns.name fun S hS => ?_
    have hSpc : S.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by rw [hS]; rfl
    have hS30 : S.regs 30 = (BitVec.ofNat 64 loc_RecoverSet_128) := by rw [hS] <;> rfl
    have hS0 : S.regs 0 = etyp := by rw [hS] <;> simp [setReg]
    have hS1 : S.regs 1 = edata := by rw [hS] <;> simp [setReg]
    have hS28 : S.regs 28 = s.regs 28 := by rw [hS] <;> simp [setReg]
    have hS18 : S.regs 18 = s.regs 18 := by rw [hS] <;> simp [setReg]
    have hSsp : S.sp.toNat = s.sp.toNat - 80 := by
      rw [hS]; simp only; rw [BitVec.toNat_sub]; simp; omega
    have hSf : MemFrame s.mem S.mem [(s.sp.toNat - (P.depth + (P.depth + 112)), s.sp.toNat + 32)] := by
      rw [hS]; janus_frame
    have hbits : S.mem.readLE (s.sp.toNat - 41) 1 = 1 := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    have hslot : S.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 32 := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 have := s.sp.isLt; omega)
    have hfv : S.mem.readLE (s.sp.toNat - 32) 8 = func1A := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      try decide
    have hcap : S.mem.readLE (s.sp.toNat - 24) 8 = s.sp.toNat - 40 := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 have := s.sp.isLt; omega)
    obtain ⟨fi, hfi⟩ : ∃ fi : FuncInfo, fi = FuncInfo.named Extracted.funcs "example.com/basic.RecoverSet" := ⟨_, rfl⟩
    have f_frame : fi.frame = 80 := by rw [hfi]; rfl
    have f_od : fi.openDefer = some (33, 8) := by rw [hfi]; rfl
    have f_res : fi.resume = Extracted.entry + 0x84 := by rw [hfi]; rfl
    have hagS : Map.Agrees s.mem S.mem P.priv :=
      Map.Agrees.of_window hSf (Outside.of_sub hout (by omega) (by omega))
    have hgS : gOf S = gOf s := by simp only [gOf, hS28]
    have hdsS : P.defers S.mem (gOf S) = P.defers s.mem (gOf s) := by rw [hgS]; exact hl.defers_frame _ _ _ hagS
    have hdsS' : ∀ d ∈ P.defers S.mem (gOf S), S.sp.toNat < d.sp := by
      intro d hd; rw [hdsS] at hd; have := hds d hd; omega
    have hri : recItems (s.sp.toNat - 80) (P.defers S.mem (gOf S)) = [] :=
      recItems_above (by rw [← hSsp]; exact hdsS')
    have hF : frameOf fi S.sp.toNat S.mem =
        ⟨s.sp.toNat - 80, s.sp.toNat, Extracted.entry + 0x84, some (s.sp.toNat - 41, s.sp.toNat - 16)⟩ := by
      simp only [frameOf, FuncInfo.bound, FuncInfo.bitsAt, FuncInfo.slotsAt, FuncInfo.varp, f_frame, f_od, hSsp,
        Option.map_some, Option.getD_some, f_res]
      have e1 : s.sp.toNat - 80 + 80 - 8 - 33 = s.sp.toNat - 41 := by omega
      have e2 : s.sp.toNat - 80 + 80 - 8 - 8 = s.sp.toNat - 16 := by omega
      have e3 : s.sp.toNat - 80 + 80 = s.sp.toNat := by omega
      rw [e1, e2, e3, hbits]; rfl
    have hob : openBits 1 = [0] := by decide
    have hI : frameItems S.mem (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S)) =
        [{ fn := s.sp.toNat - 32, bits := some 0, chain := P.defers S.mem (gOf S) }] := by
      rw [hF]
      simp only [frameItems, openItems, hbits, hob, List.map_cons, List.map_nil, hri, List.append_nil]
      have e3 : s.sp.toNat - 16 + 8 * 0 = s.sp.toNat - 16 := by omega
      rw [e3, hslot]
    refine GopanicContract.apply (fi := fi) hpan hSpc (by rw [hS30, hfi]; rfl) ?_ ?_
    · refine ⟨PanicPre.of_within hc (hSf.mono fun a n h => by
          simp only [outside_append] at h; exact h.2) (hl.env_frame _ _ henv hagS) (by omega) (by omega)
          (by rw [hSsp]; omega) hS28 (by rw [hS30]; decide) (by rw [hS30]; decide),
        by rw [hS0]; exact hne, ?_, ?_, ?_⟩
      · rw [hgS, hl.room_frame _ _ _ hagS]; exact hroom
      · intro _
        have e : fi.bitsAt S.sp.toNat = s.sp.toNat - 41 := by
          simp only [FuncInfo.bitsAt, FuncInfo.varp, f_frame, f_od, hSsp, Option.map_some, Option.getD_some]; omega
        rw [e]
        refine ⟨?_, Outside.of_sub hout (by omega) (by omega)⟩
        rw [hSf.accessible]
        exact Memory.accessible_weaken _ (Memory.accessible_mono _ hst (by omega) (by omega))
      · rw [hI, hF]
        refine ⟨⟨by omega, by rw [hSf.accessible]; exact Memory.accessible_mono _ hst (by omega) (by omega),
          Outside.of_sub hout (by omega) (by omega), by dsimp only; omega, ?_, ?_⟩, ?_⟩
        · rw [hbits, hob]
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl
          refine ⟨by omega, ?_, by omega, by dsimp only; omega, Outside.of_sub hout (by omega) (by omega)⟩
          rw [hSf.accessible]
          exact Janus.Contracts.IfaceModel.acc_read_of_write
            (Memory.accessible_mono _ hst (by omega) (by omega))
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
              (Memory.accessible_mono _ hst (by omega) (by omega))
          · rw [hfv]; try decide
          · rw [hfv]; try decide
    intro hE
    have hK : frameKeep S.mem (frameOf fi S.sp.toNat S.mem)
        (frameItems S.mem (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S))) =
        [(s.sp.toNat - 41, s.sp.toNat - 41 + 1), (s.sp.toNat - 16, s.sp.toNat - 16 + 8),
         (s.sp.toNat - 32, s.sp.toNat - 32 + 8)] := by
      rw [hI, hF]
      simp only [frameKeep, hbits, hob, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      have e3 : s.sp.toNat - 16 + 8 * 0 = s.sp.toNat - 16 := by omega
      rw [e3]
    rw [hK, hI, hF] at hE
    rw [Engine_cons] at hE
    obtain ⟨k1, e, hst1, ⟨hpc1, h26, h28, h18, h29, hal1, hlo1, hhi1, h30a, h30b, henv1⟩,
      hfr1, hb1, hd1, hpn1, hrm1, hrs1, hcont1, -⟩ := hE
    dsimp only at hpc1 h26 hlo1 hhi1 hfr1 hb1 hcont1 hrs1
    have hfr1' : MemFrame S.mem e.mem
        (P.priv ++ [(s.sp.toNat - 80 - P.depth, s.sp.toNat - 88), (s.sp.toNat - 41, s.sp.toNat - 40)]) := by
      refine hfr1.mono fun a n h => ?_
      simp only [outside_append, outside_cons, outside_nil, and_true, rtWin, bitsWin] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨⟨h1, by omega⟩, by omega⟩
    have hSfW : MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 112)), s.sp.toNat + 32)]) :=
      hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
    have hW_e : MemFrame s.mem e.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 112)), s.sp.toNat + 32)]) :=
      hSfW.trans hfr1' fun a n h => ⟨h, by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
        obtain ⟨h1, h2⟩ := h
        exact ⟨h1, by omega, by omega⟩⟩
    have hm_fv : e.mem.readLE (s.sp.toNat - 32) 8 = func1A := by
      rw [hfr1'.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
      exact hfv
    have hcalmS : P.panics S.mem (gOf S) = [] := by
      rw [hgS]; exact hl.calm_frame _ _ _ hcalm hagS
    have hm_cap : e.mem.readLE (s.sp.toNat - 24) 8 = s.sp.toNat - 40 := by
      rw [hfr1'.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
      exact hcap
    rw [hm_fv] at hpc1
    have hpn1' : P.panics e.mem (gOf s) = [{ arg := ⟨etyp.toNat, edata.toNat⟩, start := s.sp.toNat - 80 }] := by
      have := hpn1
      rw [hS28, hS0, hS1, hcalmS] at this
      simpa [hSsp, gOf] using this
    have hS28' : e.regs 28 = s.regs 28 := by rw [h28, hS28]
    have hS18' : e.regs 18 = s.regs 18 := by rw [h18, hS18]
    have hgv : e.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
      rw [hW_e.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨hgo, by omega⟩)]
    have hga : e.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by
      rw [hW_e.accessible]; exact hg2
    have hwin' : e.mem.accessible (s.sp.toNat - (P.depth + (P.depth + 112))) (P.depth + (P.depth + 112) + 32) true = true := by
      rw [hW_e.accessible]; exact hst
    refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
    have hcl : ReachesRet (Extracted.program.link impl) (e.regs 30) e (fun c' =>
        c'.pc = e.regs 30 ∧ c'.sp = e.sp ∧ c'.regs 28 = e.regs 28 ∧ c'.regs 18 = e.regs 18 ∧ P.Env c'.mem ∧
        P.panics c'.mem (gOf s) =
          [{ arg := ⟨etyp.toNat, edata.toNat⟩, start := s.sp.toNat - 80, recovered := true }] ∧ P.defers c'.mem (gOf s) = P.defers e.mem (gOf s) ∧
        P.saved c'.mem (gOf s) = P.saved e.mem (gOf s) ∧ P.room e.mem (gOf s) ≤ P.room c'.mem (gOf s) ∧
        MemFrame e.mem c'.mem (P.priv ++ [(e.sp.toNat - 32 - P.depth, e.sp.toNat),
          (s.sp.toNat - 40, s.sp.toNat - 32)]) ∧
        c'.mem.readLE (s.sp.toNat - 40) 8 = 7) := by
      janus_run until [Extracted.program.contractAddr "runtime.gorecover"]
      refine ReachesRet.call hrec rfl
        ⟨PanicPre.of_within hc ?hf ?henv ?hlo ?hhi ?hal (by simp [setReg]; exact hS28') ?hlr ?hlr', ?hga, ?hgb⟩ ?cont
      case hf => simp only [List.cons_append, List.nil_append]; janus_frame
      case henv =>
        apply hl.env_frame _ _ henv1
        apply Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + (P.depth + 112))) (hi := s.sp.toNat + 32)
        · janus_frame
        · exact Outside.of_sub hout (by omega) (by omega)
      case hlo => simp [setReg]; omega
      case hhi => simp [setReg]; omega
      case hal => simp [setReg]; omega
      case hlr => simp [setReg]
      case hlr' => simp [setReg]
      case hga =>
        simp [setReg]
        exact Janus.Contracts.IfaceModel.acc_read_of_write
          (Memory.accessible_mono _ hwin' (by omega) (by omega))
      case hgb => simp [setReg]; omega
      case cont =>
        intro G' hpcG hpost
        obtain ⟨⟨j2, f2, v2, m2, ex2, ep2, hs2, hfr2, henv2⟩, hdf2, hsv2', hrp2, hrm2, hnil2, hpanI⟩ := hpost
        have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        have hsegf : segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 36 = loc_RecoverSet_func1_36 := by decide
        have agG : ∀ m, MemFrame e.mem m [(s.sp.toNat - (P.depth + (P.depth + 112)), s.sp.toNat + 32)] →
            Map.Agrees e.mem m P.priv := fun m hf =>
          Map.Agrees.of_window hf (Outside.of_sub hout (by omega) (by omega))
        have hrpe : P.rp e.mem (gOf s) = (e.regs 30).toNat := by
          have := hrs1.1
          simpa [hS28, gOf] using this
        have hpanI' := hpanI { arg := ⟨etyp.toNat, edata.toNat⟩, start := s.sp.toNat - 80 } []
        have hw' : ¬ P.wrapper loc_RecoverSet_func1_36 := by rw [← hsegf]; exact hw
        have key : ∀ m g, g = (s.regs 28).toNat →
            MemFrame e.mem m [(s.sp.toNat - (P.depth + (P.depth + 112)), s.sp.toNat + 32)] →
            P.panics m g = [{ arg := ⟨etyp.toNat, edata.toNat⟩, start := s.sp.toNat - 80 }] := by
          intro m g hg hf
          rw [hg]; exact (hl.panics_frame _ _ _ (agG m hf)).trans hpn1'
        obtain ⟨hr0, hr1, hrec2⟩ := hpanI' (key _ _ (by dsimp only [gOf]; simp [setReg, hS28']) (by janus_frame)) rfl rfl
          (by dsimp only; simpa [setReg] using hw') (by
            have hes : 40 ≤ e.sp.toNat ∧ e.sp.toNat % 16 = 0 := ⟨by omega, hal1⟩
            have h40 : (e.sp - 40#64).toNat = e.sp.toNat - 40 := by
              rw [BitVec.toNat_sub]; simp; omega
            have hrpm : P.rp e.mem (gOf s) = (e.regs 30).toNat := hrpe
            have hrp' : ∀ m, MemFrame e.mem m [(s.sp.toNat - (P.depth + (P.depth + 112)), s.sp.toNat + 32)] →
                P.rp m (gOf s) = (e.regs 30).toNat := fun m hf => by
              rw [hl.rp_frame _ _ _ (agG m hf)]; exact hrpm
            have hrp'' : ∀ m g, g = (s.regs 28).toNat →
                MemFrame e.mem m [(s.sp.toNat - (P.depth + (P.depth + 112)), s.sp.toNat + 32)] →
                P.rp m g = (e.regs 30).toNat := fun m g hg hf => by rw [hg]; exact hrp' m hf
            dsimp only
            simp only [setReg_apply, Nat.reduceEqDiff, reduceIte, h40]
            have hrd : (((e.mem.writeLE (BitVec.toNat e.sp - 32) 8 (BitVec.toNat (e.regs 30))).writeLE
                (BitVec.toNat e.sp - 40) 8 (BitVec.toNat e.sp - 8)).writeLE (BitVec.toNat e.sp - 16) 8
                (S.mem.readLE (BitVec.toNat s.sp - 32 + 8) 8)).readLE (BitVec.toNat e.sp - 40 + 8) 8 =
                (e.regs 30).toNat := by
              rw [show BitVec.toNat e.sp - 40 + 8 = BitVec.toNat e.sp - 32 by omega]
              simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
              exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                         have := (e.regs 30).isLt; omega)
            rw [hrd]
            exact (hrp'' _ _ (by dsimp only [gOf]; simp [setReg, hS28']) (by janus_frame)).symm)
        subst hs2
        have h32 : (e.sp - 32#64).toNat = e.sp.toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
        simp only [calleeStack, h32, retStateX, callRegs_apply, List.getD_nil, setReg_apply, reduceIte,
          Nat.reduceEqDiff] at hfr2 hr0 hr1 hrec2 henv2
        have hj0 : j2 0 ≠ 0 := fun h => hne (by rw [← hr0, h]; rfl)
        have hcap' : S.mem.readLE (BitVec.toNat s.sp - 32 + 8) 8 = s.sp.toNat - 40 := by
          rw [show BitVec.toNat s.sp - 32 + 8 = BitVec.toNat s.sp - 24 by omega]; exact hcap
        have hacc7 : m2.accessible (s.sp.toNat - 40) 8 true = true := by
          rw [hfr2.accessible]; simp only [Memory.accessible_writeLE]
          exact Memory.accessible_mono _ hwin' (by omega) (by omega)
        janus_run [hcap']
        have hag7 : Map.Agrees m2 (m2.writeLE (s.sp.toNat - 40) 8 7) P.priv :=
          Map.Agrees.of_window (lo := s.sp.toNat - 40) (hi := s.sp.toNat - 32) (by janus_frame)
            (Outside.of_sub hout (by omega) (by omega))
        have hG : ∀ T : State, T.regs 28 = s.regs 28 → gOf T = gOf s := fun T h => by simp only [gOf, h]
        simp only [retStateX] at hdf2 hsv2' hrp2 hrm2
        rw [hG _ (by simp [setReg, hS28'])] at hdf2 hsv2' hrm2 hrec2
        have hagX : Map.Agrees e.mem
            (((e.mem.writeLE (BitVec.toNat e.sp - 32) 8 (BitVec.toNat (e.regs 30))).writeLE (BitVec.toNat e.sp - 40) 8
                (BitVec.toNat e.sp - 8)).writeLE (BitVec.toNat e.sp - 16) 8 (S.mem.readLE (BitVec.toNat s.sp - 32 + 8) 8))
            P.priv :=
          Map.Agrees.of_window (lo := e.sp.toNat - 32 - P.depth) (hi := e.sp.toNat) (by janus_frame)
            (Outside.of_sub hout (by omega) (by omega))
        have hp2' : P.panics (m2.writeLE (BitVec.toNat s.sp - 40) 8 7) (gOf s) =
            [{ arg := { typ := etyp.toNat, data := edata.toNat }, start := BitVec.toNat s.sp - 80, recovered := true }] := by
          rw [hl.panics_frame _ _ _ hag7]; exact hrec2
        refine ⟨hl.env_frame _ _ henv2 hag7, hp2', ?_, ?_, ?_, ?_⟩
        · rw [hl.defers_frame _ _ _ hag7]; rw [hdf2]; exact hl.defers_frame _ _ _ hagX
        · rw [hl.saved_frame _ _ _ hag7]; rw [hsv2']; exact hl.saved_frame _ _ _ hagX
        · rw [hl.room_frame _ _ _ hag7]; exact Nat.le_trans (Nat.le_of_eq (hl.room_frame _ _ _ hagX).symm) hrm2
        · try simp only [List.cons_append, List.nil_append]
          janus_frame
    obtain ⟨k2, c', hst2, -, hcpc, hcsp, hc28, hc18, hcenv, hcpan, hcdef, hcsv, hcrm, hcfr, hc7⟩ := hcl
    refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
    have hagc : Map.Agrees e.mem c'.mem ((e.sp.toNat, s.sp.toNat - 80) ::
        [(s.sp.toNat - 41, s.sp.toNat - 41 + 1), (s.sp.toNat - 16, s.sp.toNat - 16 + 8),
         (s.sp.toNat - 32, s.sp.toNat - 32 + 8)]) := by
      refine Map.Agrees.of_memFrame hcfr fun a ⟨r, hr, h1, h2⟩ => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [outside_append, outside_cons, outside_nil, and_true]
      rcases hr with rfl | rfl | rfl | rfl <;> simp only at h1 h2 <;>
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩
    have hdr1 : DeferReturned P (S.regs 28) (S.regs 18) (s.sp.toNat - 80)
        [(s.sp.toNat - 41, s.sp.toNat - 41 + 1), (s.sp.toNat - 16, s.sp.toNat - 16 + 8),
         (s.sp.toNat - 32, s.sp.toNat - 32 + 8)] e c' := by
      refine ⟨hcpc, hcsp, by rw [hc28, h28], by rw [hc18, h18], hagc, hcenv, ?_, ?_, ?_⟩
      · have := hcdef; simpa [gOf, hS28] using this
      · have := hcsv; simpa [gOf, hS28] using this
      · have := hcrm; simpa [gOf, hS28] using this
    have hpanc : P.panics c'.mem (S.regs 28).toNat =
        { arg := ⟨(S.regs 0).toNat, (S.regs 1).toNat⟩, start := S.sp.toNat, recovered := true } :: P.panics S.mem (gOf S) := by
      rw [hS28, hS0, hS1, hSsp, hcalmS]
      have := hcpan; simpa [gOf] using this
    have hrecov := (hcont1 c' hdr1).2 rfl _ _ rfl hpanc (by
      intro q hq
      rw [hpanc] at hq
      simp only [hcalmS, List.takeWhile] at hq
      split at hq
      · simp at hq; subst hq; rfl
      · simp at hq)
    obtain ⟨k3, d, hst3, hdpc, hdsp, hd29, hd28, hd18, hdfr, hdenv, hdpan, hddef, hdsv, hdroom⟩ := hrecov
    refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
    obtain ⟨dr, dsp, dpc, dfl, dm, ddz, dv, dtp, dfc, dfs⟩ := d
    dsimp only at hdpc hdsp hd29 hd28 hd18
    rw [show Extracted.entry + 132 = resumeA from rfl] at hdpc
    subst hdpc hdsp
    have hsp80' : BitVec.ofNat 64 (s.sp.toNat - 80) = s.sp - 80#64 := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hdr' : dr = setReg (setReg (setReg dr 18 (s.regs 18)) 28 (s.regs 28)) 29 (s.sp - 80#64 - 8) := by
      funext i; simp only [setReg]
      by_cases h29 : i = 29
      · rw [if_pos h29, h29]; rw [hsp80'] at hd29; exact hd29
      · rw [if_neg h29]
        by_cases h28 : i = 28
        · rw [if_pos h28, h28, hd28, hS28]
        · rw [if_neg h28]
          by_cases h18 : i = 18
          · rw [if_pos h18, h18, hd18, hS18]
          · rw [if_neg h18]
    rw [hdr']
    refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn"))
      hret.fetch_none ?_
    janus_run until [Extracted.program.contractAddr "runtime.deferreturn"]
    refine ReachesRet.done rfl ?_
    refine GoReturns.name fun D hD => ?_
    have hDm : D.mem = dm := by rw [hD]
    have hDsp : D.sp = BitVec.ofNat 64 (s.sp.toNat - 80) := by rw [hD]
    have hDspn : D.sp.toNat = s.sp.toNat - 80 := by
      rw [hDsp, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; have := s.sp.isLt; omega
    have hD28 : D.regs 28 = s.regs 28 := by rw [hD]; simp [setReg]
    have hD30 : D.regs 30 = (BitVec.ofNat 64 loc_RecoverSet_136) := by rw [hD]; simp [setReg]
    have hDpc : D.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by rw [hD]; rfl
    have hgD : gOf D = gOf s := by simp only [gOf, hD28]
    dsimp only at hdpan hddef hdsv hdroom
    have hsvD : P.saved D.mem (gOf D) = none := by
      rw [hDm, hgD]; have := hdsv; rw [if_pos (by decide)] at this; simpa [gOf, hS28] using this
    have hdefD : P.defers D.mem (gOf D) = P.defers s.mem (gOf s) := by
      rw [hDm, hgD]
      have h1 := hddef; have h2 := hcdef; have h3 := hd1
      simp only [gOf, hS28] at h1 h2 h3 ⊢
      rw [h1, h2, h3]; have h4 := hdsS; simp only [gOf, hS28] at h4; exact h4
    have hF : retFrame P D = ⟨s.sp.toNat - 80, s.sp.toNat - 80, 0, none⟩ := by
      simp only [retFrame, hsvD, hDspn]
    have hds' : ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat - 80 < d.sp := fun d hd => by have := hds d hd; omega
    have hdI : frameItems D.mem (retFrame P D) (P.defers D.mem (gOf D)) = [] := by
      rw [hF, hdefD]; simp only [frameItems, List.nil_append, recItems_above hds']
    have hWD : MemFrame s.mem dm (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 112)), s.sp.toNat + 32)]) := by
      have h1 : MemFrame s.mem c'.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 112)), s.sp.toNat + 32)]) :=
        hW_e.trans hcfr fun a n h => ⟨h, by
          simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
          obtain ⟨h1, h2⟩ := h
          exact ⟨h1, by omega, by omega⟩⟩
      refine h1.trans hdfr fun a n h => ⟨h, ?_⟩
      simp only [outside_append, outside_cons, outside_nil, and_true, rtWin] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega⟩
    have hpre : PanicPre P 0 D := PanicPre.of_within hc (hDm ▸ hWD) (hDm ▸ hdenv) (by omega) (by omega) (by rw [hDspn]; omega)
      hD28 (by rw [hD30]; decide) (by rw [hD30]; decide)
    refine DeferreturnContract.apply (S := D) hdr hDpc ⟨hpre, ?_⟩ ?_
    · rw [hdI, hF]; exact ⟨trivial, fun it h => absurd h (by simp)⟩
    intro hE
    rw [hdI, Engine_nil] at hE
    obtain ⟨k4, d2, hst4, hfin⟩ := hE
    obtain ⟨hfpc, hfsp, hf28, hf18, hf29, hfmf, hfenv, -⟩ := hfin
    refine GoReturns.of_steps (hst4.withExit hret.fetch_none) ?_
    have hD29 : D.regs 29 = s.sp - 88#64 := by rw [hD]; simp [setReg]
    have hD18 : D.regs 18 = s.regs 18 := by rw [hD]; simp [setReg]
    obtain ⟨er, esp, epc, efl, em, edz, ev, etp, efc, efs⟩ := d2
    dsimp only at hfpc hfsp hf28 hf18 hf29 hfmf
    rw [hD30] at hfpc
    rw [hDsp] at hfsp
    subst hfpc hfsp
    have her : er = setReg (setReg (setReg er 18 (s.regs 18)) 28 (s.regs 28)) 29 (s.sp - 88#64) := by
      funext i; simp only [setReg]
      by_cases h29 : i = 29
      · rw [if_pos h29, h29]; rw [hD29] at hf29; exact hf29
      · rw [if_neg h29]
        by_cases h28 : i = 28
        · rw [if_pos h28, h28, hf28, hD28]
        · rw [if_neg h28]
          by_cases h18 : i = 18
          · rw [if_pos h18, h18, hf18, hD18]
          · rw [if_neg h18]
    rw [her]
    rw [hDm, hF] at hfmf
    simp only [rtWin, bitsWin, List.append_nil] at hfmf
    -- the facts the epilogue reads, carried from the entry state through every frame
    have hxfer : ∀ a n v, Outside a n P.priv → s.sp.toNat - 88 ≤ a → a + n ≤ s.sp.toNat - 41 →
        S.mem.readLE a n = v → dm.readLE a n = v := by
      intro a n v hpr h1 h2 hv
      rw [hdfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true, rtWin]
        exact ⟨hpr, by omega⟩),
        hcfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpr, by omega, by omega⟩)]
      rw [← hv]
      exact hfr1'.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpr, by omega, by omega⟩)
    have hfpE : dm.readLE (s.sp.toNat - 80 - 8) 8 = (s.regs 29).toNat := by
      refine hxfer _ _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) ?_
      have e88 : s.sp.toNat - 80 - 8 = s.sp.toNat - 88 := by omega
      rw [hS, e88]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 have := (s.regs 29).isLt; omega)
    have hr48 : ret < 2 ^ 48 := hret.user
    have hra : ret % 4 = 0 := hret.aligned
    have hlrE : dm.readLE (s.sp.toNat - 80) 8 = ret := by
      refine hxfer _ _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) ?_
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 omega)
    have h7E : dm.readLE (s.sp.toNat - 80 + 40) 8 = 7 := by
      rw [hdfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true, rtWin]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩),
        show s.sp.toNat - 80 + 40 = s.sp.toNat - 40 by omega]
      exact hc7
    have hacE : em.accessible (s.sp.toNat - 88) 96 true = true := by
      rw [hfmf.accessible, hdfr.accessible, hcfr.accessible, hfr1'.accessible, hSf.accessible]
      exact Memory.accessible_mono _ hst (by omega) (by omega)
    refine GoReturns.of_reaches ?_
    janus_run [hlrE]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := s.sp.isLt; omega
    · rw [hfpE]; exact BitVec.ofNat_toNat _ _
    · rw [h7E]; rw [if_neg hx]


namespace Witness

open Janus.Contracts.PanicSat Janus.Contracts.PanicModel

abbrev T0 : List FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : PanicRuntime := P0 T0 RPa

def gA : Nat := Extracted.program.contractAddr "runtime.gopanic"
def rA : Nat := Extracted.program.contractAddr "runtime.gorecover"
def dA : Nat := Extracted.program.contractAddr "runtime.deferreturn"

/-- The code linked next to `RecoverSet`: the model engine and a branch to it at each contract
address. -/
def implW : List Segment :=
  panicImpl Extracted.program [("runtime.gopanic", eGopanic), ("runtime.gorecover", eGorecover),
    ("runtime.deferreturn", eDeferreturn)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

theorem stubG : StubAt (Extracted.program.link implW) gA eGopanic :=
  StubAt.of_decode (w := stubWord gA eGopanic) (imm := (eGopanic - gA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem stubR : StubAt (Extracted.program.link implW) rA eGorecover :=
  StubAt.of_decode (w := stubWord rA eGorecover) (imm := (eGorecover - rA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem stubD : StubAt (Extracted.program.link implW) dA eDeferreturn :=
  StubAt.of_decode (w := stubWord dA eDeferreturn) (imm := (eDeferreturn - dA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem hpan : GopanicContract (Extracted.program.link implW) gA PW U0 T0 :=
  gopanic_at stubG (gopanic_run engineAt T0 tok)

theorem hrec : GorecoverContract (Extracted.program.link implW) rA PW :=
  gorecover_at stubR (gorecover_run engineAt T0)

theorem hdr : DeferreturnContract (Extracted.program.link implW) dA PW U0 :=
  deferreturn_at stubD (deferreturn_run engineAt)

def wmW : Memory := witMem (tabWords T0)

abbrev wg : Nat := witG
abbrev wsp : Nat := witSP
abbrev ret : Nat := witRet

theorem env_w : Env0 T0 wmW := by
  unfold Env0
  have hnd : ndef wmW = 0 := by decide
  refine ⟨by decide, by decide, by decide, fun i hi => ?_, ?_⟩
  · omega
  · unfold TableOK
    exact ⟨by decide, by decide, by decide⟩

theorem hret : RetAddr (Extracted.program.link implW) ret := RetAddr.of_check (by decide)

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret
      else if i = 29 then BitVec.ofNat 64 (wsp - 8) else if i = 0 then 42#64
      else if i = 1 then 1#64 else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmW }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [42#64, 1#64, 0#64] s0 := by
  refine ⟨rfl, rfl, fun i h => ?_⟩
  simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

theorem pre : PanicCallerOK PW s0 (PW.depth + 112) 32 ∧ PW.Calm s0.mem (s0.regs 28).toNat ∧
    (1#64 : BitVec 64).toNat ≠ 0 ∧ 0 < PW.room s0.mem (gOf s0) ∧
    ∀ d ∈ PW.defers s0.mem (gOf s0), s0.sp.toNat ≤ d.sp := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_⟩, ?_, by decide, ?_, ?_⟩
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
theorem nonvacuous : ∃ (impl : List Segment) (P : PanicRuntime) (U : State → Nat → Nat → Prop) (ret : Nat)
    (s : State), P.Laws ∧
    GopanicContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gopanic") P U
      Extracted.funcs ∧
    GorecoverContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gorecover") P ∧
    DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P U ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [42#64, 1#64, 0#64] s ∧
    (PanicCallerOK P s (P.depth + 112) 32 ∧ P.Calm s.mem (s.regs 28).toNat ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧
      0 < P.room s.mem (gOf s) ∧ (∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp) ∧
      ¬ P.wrapper (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x24)) :=
  ⟨implW, PW, U0, ret, s0, P0_laws T0 RPa, hpan, hrec, hdr, hret, setup, by obtain ⟨a, b, c, d, e⟩ := pre; exact ⟨a, b, c, d, e, id⟩⟩

/-- So the guarantee is reached: with `x = 42` `RecoverSet` panics, recovers, and returns `7`. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClass PW) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧
        (s'.regs 0).toNat = if (42#64 : BitVec 64).toNat ≤ 10 then (42#64 : BitVec 64).toNat else 7
    | .panicked _ _ => False
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U0 hpan hrec hdr 42#64 1#64 0#64 ret hret s0 setup (by obtain ⟨a, b, c, d, e⟩ := pre; exact ⟨a, b, c, d, e, id⟩)

end Witness

end Proof
