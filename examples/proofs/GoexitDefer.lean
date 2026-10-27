import Extracted

/-!
# `GoexitDefer(p *uint64)`: `runtime.Goexit` runs the deferred call and terminates the goroutine (arm64)

`GoexitDefer` is
`defer func() { if recover() != nil { *p = 99 } else { *p = *p + 1 } }(); runtime.Goexit(); *p = 5`
with an open-coded defer.

**Guarantee (example 4 of docs/COVERAGE.md R6).** For every panic-runtime model `P` satisfying its
laws and every implementation of `runtime.Goexit` and `runtime.gorecover` meeting their contracts
(`Janus.Contracts.Panic`, pinned to the Go 1.26 runtime's code), every admissible return address
and every call state in which the runtime is usable with room for a record, `p` points to a
writable word outside the runtime's memory and the stack window: the call **never returns and never
panics**; it terminates the goroutine (`GoOutcome.goexited`) with `*p = *p + 1`. `Goexit` pushes a
`_panic` with `goexit` set, so the deferred call's `recover()` returns `nil` (a `Goexit` cannot be
recovered) and it takes the `else` branch; the store `*p = 5` after `Goexit` never happens.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Proof

local macro "func1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.GoexitDefer.func1"))
local macro "recoverRet" : term =>
  `(janus_eval% (segAddr Extracted.program "example.com/basic.GoexitDefer.func1" + 0x24))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hge : GoexitContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.Goexit") P U Extracted.funcs)
    (hrec : GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") P)
    (p : BitVec 64) :
    EnsuresGoX (Extracted.program.link impl) Extracted.entry [p]
      (fun s => PanicCallerOK P s (P.depth + 80) 16 ∧ Ptr s.mem p 8 true ∧
        Spec.Disjoint p.toNat 8 (s.sp.toNat - (P.depth + (P.depth + 80))) (P.depth + (P.depth + 80) + 16) ∧
        Outside p.toNat 8 P.priv ∧ 0 < P.room s.mem (gOf s) ∧
        ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp)
      (goClassU P U)
      (fun _ _ => False)
      (fun _ _ _ => False)
      (fun s s' => s'.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64) := by
  intro ret hret s hs ⟨hc, ⟨hp, hp'⟩, hdj, hpo, hroom, hds⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd hdj
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.Goexit"))
    hret.fetch_none ?_
  janus_run until [Extracted.program.contractAddr "runtime.Goexit"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun S hS => ?_
  have hSpc : S.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.Goexit") := by rw [hS]; rfl
  have hS30 : S.regs 30 = BitVec.ofNat 64 604708 := by rw [hS] <;> rfl
  have hS28 : S.regs 28 = s.regs 28 := by rw [hS] <;> simp [setReg]
  have hS18 : S.regs 18 = s.regs 18 := by rw [hS] <;> simp [setReg]
  have hSsp : S.sp.toNat = s.sp.toNat - 48 := by
    rw [hS]; simp only; rw [BitVec.toNat_sub]; simp; omega
  have hSf : MemFrame s.mem S.mem [(s.sp.toNat - (P.depth + (P.depth + 80)), s.sp.toNat + 16)] := by
    rw [hS]; janus_frame
  have hbits : S.mem.readLE (s.sp.toNat - 33) 1 = 1 := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have hslot : S.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 32 := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)
  have hfv : S.mem.readLE (s.sp.toNat - 32) 8 = func1A := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    try decide
  have hcap : S.mem.readLE (s.sp.toNat - 24) 8 = p.toNat := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := p.isLt; omega)
  obtain ⟨fi, hfi⟩ : ∃ fi : FuncInfo, fi = FuncInfo.named Extracted.funcs "example.com/basic.GoexitDefer" := ⟨_, rfl⟩
  have f_frame : fi.frame = 48 := by rw [hfi]; rfl
  have f_od : fi.openDefer = some (25, 8) := by rw [hfi]; rfl
  have f_res : fi.resume = Extracted.entry + 0x6c := by rw [hfi]; rfl
  have hagS : Map.Agrees s.mem S.mem P.priv :=
    Map.Agrees.of_window hSf (Outside.of_sub hout (by omega) (by omega))
  have hgS : gOf S = gOf s := by simp only [gOf, hS28]
  have hdsS : P.defers S.mem (gOf S) = P.defers s.mem (gOf s) := by rw [hgS]; exact hl.defers_frame _ _ _ hagS
  have hdsS' : ∀ d ∈ P.defers S.mem (gOf S), S.sp.toNat < d.sp := by
    intro d hd; rw [hdsS] at hd; have := hds d hd; omega
  have hri : recItems (s.sp.toNat - 48) (P.defers S.mem (gOf S)) = [] :=
    recItems_above (by rw [← hSsp]; exact hdsS')
  have hF : frameOf fi S.sp.toNat S.mem =
      ⟨s.sp.toNat - 48, s.sp.toNat, Extracted.entry + 0x6c, some (s.sp.toNat - 33, s.sp.toNat - 16)⟩ := by
    simp only [frameOf, FuncInfo.bound, FuncInfo.bitsAt, FuncInfo.slotsAt, FuncInfo.varp, f_frame, f_od, hSsp,
      Option.map_some, Option.getD_some, f_res]
    have e1 : s.sp.toNat - 48 + 48 - 8 - 25 = s.sp.toNat - 33 := by omega
    have e2 : s.sp.toNat - 48 + 48 - 8 - 8 = s.sp.toNat - 16 := by omega
    have e3 : s.sp.toNat - 48 + 48 = s.sp.toNat := by omega
    rw [e1, e2, e3, hbits]; rfl
  have hob : openBits 1 = [0] := by decide
  have hI : frameItems S.mem (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S)) =
      [{ fn := s.sp.toNat - 32, bits := some 0, chain := P.defers S.mem (gOf S) }] := by
    rw [hF]
    simp only [frameItems, openItems, hbits, hob, List.map_cons, List.map_nil, hri, List.append_nil]
    have e3 : s.sp.toNat - 16 + 8 * 0 = s.sp.toNat - 16 := by omega
    rw [e3, hslot]
  refine GoexitContract.apply (fi := fi) hge hSpc (by rw [hS30, hfi]; rfl) ?_ ?_
  · refine ⟨PanicPre.of_within hc (hSf.mono fun a n h => by
        simp only [outside_append] at h; exact h.2) (hl.env_frame _ _ henv hagS) (by omega) (by omega)
        (by rw [hSsp]; omega) hS28 (by rw [hS30]; decide) (by rw [hS30]; decide),
      ?_, ?_, ?_⟩
    · rw [hgS, hl.room_frame _ _ _ hagS]; exact hroom
    · intro _
      have e : fi.bitsAt S.sp.toNat = s.sp.toNat - 33 := by
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
      [(s.sp.toNat - 33, s.sp.toNat - 33 + 1), (s.sp.toNat - 16, s.sp.toNat - 16 + 8),
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
      (P.priv ++ [(s.sp.toNat - 48 - P.depth, s.sp.toNat - 56), (s.sp.toNat - 33, s.sp.toNat - 32)]) := by
    refine hfr1.mono fun a n h => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true, rtWin, bitsWin] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, by omega⟩, by omega⟩
  have hSfW : MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 80)), s.sp.toNat + 16)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  have hW_e : MemFrame s.mem e.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 80)), s.sp.toNat + 16)]) :=
    hSfW.trans hfr1' fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hm_fv : e.mem.readLE (s.sp.toNat - 32) 8 = func1A := by
    rw [hfr1'.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    exact hfv
  have hm_cap : e.mem.readLE (s.sp.toNat - 24) 8 = p.toNat := by
    rw [hfr1'.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    exact hcap
  rw [hm_fv] at hpc1
  have hpn1' : ∃ r rs, P.panics e.mem (gOf s) = r :: rs ∧ r.goexit = true := by
    refine ⟨{ arg := ⟨0, 0⟩, goexit := true, start := S.sp.toNat }, P.panics S.mem (gOf S), ?_, rfl⟩
    have := hpn1
    rw [hS28] at this
    simpa [gOf, hS28] using this
  have hS28' : e.regs 28 = s.regs 28 := by rw [h28, hS28]
  have hS18' : e.regs 18 = s.regs 18 := by rw [h18, hS18]
  have hgv : e.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hW_e.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨hgo, by omega⟩)]
  have hga : e.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by
    rw [hW_e.accessible]; exact hg2
  have hwin' : e.mem.accessible (s.sp.toNat - (P.depth + (P.depth + 80))) (P.depth + (P.depth + 80) + 16) true = true := by
    rw [hW_e.accessible]; exact hst
  have hpv : e.mem.readLE p.toNat 8 = s.mem.readLE p.toNat 8 := by
    rw [hW_e.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨hpo, by omega⟩)]
  have hpa : e.mem.accessible p.toNat 8 true = true := by rw [hW_e.accessible]; exact hp
  refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
  have hcl : ReachesRet (Extracted.program.link impl) (e.regs 30) e (fun c' =>
      c'.pc = e.regs 30 ∧ c'.sp = e.sp ∧ c'.regs 28 = e.regs 28 ∧ c'.regs 18 = e.regs 18 ∧ P.Env c'.mem ∧
      P.panics c'.mem (gOf s) = P.panics e.mem (gOf s) ∧ P.defers c'.mem (gOf s) = P.defers e.mem (gOf s) ∧
      P.saved c'.mem (gOf s) = P.saved e.mem (gOf s) ∧ P.room e.mem (gOf s) ≤ P.room c'.mem (gOf s) ∧
      MemFrame e.mem c'.mem (P.priv ++ [(e.sp.toNat - 32 - P.depth, e.sp.toNat), (p.toNat, p.toNat + 8)]) ∧
      c'.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64) := by
    janus_run until [Extracted.program.contractAddr "runtime.gorecover"]
    refine ReachesRet.call hrec rfl
      ⟨PanicPre.of_within hc ?hf ?henv ?hlo ?hhi ?hal (by simp [setReg]; exact hS28') ?hlr ?hlr', ?hga, ?hgb⟩ ?cont
    case hf => simp only [List.cons_append, List.nil_append]; janus_frame
    case henv =>
      apply hl.env_frame _ _ henv1
      apply Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + (P.depth + 80))) (hi := s.sp.toNat + 16)
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
      obtain ⟨⟨j2, f2, v2, m2, hs2, hfr2, henv2⟩, hdf2, hsv2', hrp2, hrm2, hnil2, -⟩ := hpost
      have agG : ∀ m, MemFrame e.mem m [(s.sp.toNat - (P.depth + (P.depth + 80)), s.sp.toNat + 16)] →
          Map.Agrees e.mem m P.priv := fun m hf =>
        Map.Agrees.of_window hf (Outside.of_sub hout (by omega) (by omega))
      obtain ⟨r, rs, hr, hgx⟩ := hpn1'
      have hkey : ∀ m g, g = (s.regs 28).toNat →
          MemFrame e.mem m [(s.sp.toNat - (P.depth + (P.depth + 80)), s.sp.toNat + 16)] →
          P.panics m g = r :: rs := fun m g hg hf => by
        rw [hg]; exact (hl.panics_frame _ _ _ (agG m hf)).trans hr
      obtain ⟨h0, h1, hpanI⟩ := hnil2 (Or.inr ⟨r, rs,
        hkey _ _ (by dsimp only [gOf]; simp [setReg, hS28']) (by janus_frame), Or.inl hgx⟩)
      subst hs2
      have h32 : (e.sp - 32#64).toNat = e.sp.toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
      simp only [calleeStack, h32, retState, callRegs_apply, List.getD_nil, setReg_apply, reduceIte,
        Nat.reduceEqDiff] at hfr2 h0 h1 henv2 hpanI
      have hcap' : S.mem.readLE (BitVec.toNat s.sp - 32 + 8) 8 = p.toNat := by
        rw [show BitVec.toNat s.sp - 32 + 8 = BitVec.toNat s.sp - 24 by omega]; exact hcap
      have hsl : m2.readLE (e.sp.toNat - 16) 8 = p.toNat := by
        rw [hfr2.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
        simp only [Memory.readLE_writeLE_self]; rw [hcap', h64]; exact Nat.mod_eq_of_lt p.isLt
      have hpv2 : m2.readLE p.toNat 8 = s.mem.readLE p.toNat 8 := by
        rw [hfr2.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hpo, by omega, by omega⟩)]
        simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hpv
      have hpa2 : m2.accessible p.toNat 8 true = true := by
        rw [hfr2.accessible]; simp only [Memory.accessible_writeLE]; exact hpa
      have h0'' : j2 0 = 0 := by simpa using h0
      have h0' : (j2 0).toNat = 0 := by rw [h0'']; rfl
      janus_run [hcap', hsl, hpv2]
      have hag7 : Map.Agrees m2 (m2.writeLE p.toNat 8 (s.mem.readLE p.toNat 8 + 1)) P.priv :=
        Map.agrees_writeLE m2 _ hpo
      have hG : ∀ T : State, T.regs 28 = s.regs 28 → gOf T = gOf s := fun T h => by simp only [gOf, h]
      simp only [retState] at hdf2 hsv2' hrp2 hrm2
      rw [hG _ (by simp [setReg, hS28'])] at hdf2 hsv2' hrm2 hpanI
      have hagX : Map.Agrees e.mem
          (((e.mem.writeLE (BitVec.toNat e.sp - 32) 8 (BitVec.toNat (e.regs 30))).writeLE (BitVec.toNat e.sp - 40) 8
              (BitVec.toNat e.sp - 8)).writeLE (BitVec.toNat e.sp - 16) 8 (S.mem.readLE (BitVec.toNat s.sp - 32 + 8) 8))
          P.priv :=
        Map.Agrees.of_window (lo := e.sp.toNat - 32 - P.depth) (hi := e.sp.toNat) (by janus_frame)
          (Outside.of_sub hout (by omega) (by omega))
      refine ⟨hl.env_frame _ _ henv2 hag7, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hl.panics_frame _ _ _ hag7, hpanI]; exact hl.panics_frame _ _ _ hagX
      · rw [hl.defers_frame _ _ _ hag7]; rw [hdf2]; exact hl.defers_frame _ _ _ hagX
      · rw [hl.saved_frame _ _ _ hag7]; rw [hsv2']; exact hl.saved_frame _ _ _ hagX
      · rw [hl.room_frame _ _ _ hag7]; exact Nat.le_trans (Nat.le_of_eq (hl.room_frame _ _ _ hagX).symm) hrm2
      · try simp only [List.cons_append, List.nil_append]
        janus_frame
  obtain ⟨k2, c', hst2, -, hcpc, hcsp, hc28, hc18, hcenv, hcpan, hcdef, hcsv, hcrm, hcfr, hcp⟩ := hcl
  refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
  have hagc : Map.Agrees e.mem c'.mem ((e.sp.toNat, s.sp.toNat - 48) ::
      [(s.sp.toNat - 33, s.sp.toNat - 33 + 1), (s.sp.toNat - 16, s.sp.toNat - 16 + 8),
       (s.sp.toNat - 32, s.sp.toNat - 32 + 8)]) := by
    refine Map.Agrees.of_memFrame hcfr fun a ⟨r, hr, h1, h2⟩ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [outside_append, outside_cons, outside_nil, and_true]
    rcases hr with rfl | rfl | rfl | rfl <;> simp only at h1 h2 <;>
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩
  have hdr1 : DeferReturned P (S.regs 28) (S.regs 18) (s.sp.toNat - 48)
      [(s.sp.toNat - 33, s.sp.toNat - 33 + 1), (s.sp.toNat - 16, s.sp.toNat - 16 + 8),
       (s.sp.toNat - 32, s.sp.toNat - 32 + 8)] e c' := by
    refine ⟨hcpc, hcsp, by rw [hc28, h28], by rw [hc18, h18], hagc, hcenv, ?_, ?_, ?_⟩
    · have := hcdef; simpa [gOf, hS28] using this
    · have := hcsv; simpa [gOf, hS28] using this
    · have := hcrm; simpa [gOf, hS28] using this
  have hpanc : P.panics c'.mem (S.regs 28).toNat =
      { arg := ⟨0, 0⟩, goexit := true, start := S.sp.toNat } :: P.panics S.mem (gOf S) := by
    have h1 := hcpan; have h2 := hpn1
    simp only [gOf, hS28] at h1 h2 ⊢
    rw [h1]; exact h2
  have hE1 := (hcont1 c' hdr1).1 hpanc
  rw [Engine_nil] at hE1
  obtain ⟨k3, d, hst3, hU, hpd, -, hfrd, -, -, -⟩ := hE1
  refine GoReturns.goexit (hst3.withExit hret.fetch_none) ?_ ?_
  · refine ⟨?_, { arg := ⟨0, 0⟩, goexit := true, start := S.sp.toNat }, P.panics S.mem (gOf S), ?_, rfl⟩
    · have hg' : gOf s = (S.regs 28).toNat := by simp only [gOf, hS28]
      rw [hg']; exact hU
    · have hg' : gOf s = (S.regs 28).toNat := by simp only [gOf, hS28]
      rw [hg']; exact hpd
  · show d.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64
    rw [hfrd.readLE _ _ (by
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hpo, by omega⟩, by omega⟩)]
    exact hcp

/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSat` (code that
`Janus.Contracts.PanicSatRun` proves meets the `Goexit` and `gorecover` contracts in every program
that contains it) linked into `GoexitDefer`'s program with a branch to it at each contract
address, and a call state satisfying the precondition: so `correctness` applies (`nonvacuous`),
and `GoexitDefer` terminates the goroutine from that state (`returns`). -/

namespace Witness

open Janus.Contracts.PanicSat Janus.Contracts.PanicModel

abbrev T0 : List FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : PanicRuntime := P0 T0 RPa

def geA : Nat := Extracted.program.contractAddr "runtime.Goexit"
def rcA : Nat := Extracted.program.contractAddr "runtime.gorecover"

/-- The code linked next to `GoexitDefer`: the model engine and a branch to it at each contract
address. -/
def implW : List Segment :=
  panicImpl Extracted.program [("runtime.Goexit", eGoexit), ("runtime.gorecover", eGorecover)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

theorem stubGe : StubAt (Extracted.program.link implW) geA eGoexit :=
  StubAt.of_decode (w := stubWord geA eGoexit) (imm := (eGoexit - geA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem stubRc : StubAt (Extracted.program.link implW) rcA eGorecover :=
  StubAt.of_decode (w := stubWord rcA eGorecover) (imm := (eGorecover - rcA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem hge : GoexitContract (Extracted.program.link implW) geA PW U0 T0 :=
  goexit_at stubGe (goexit_run engineAt T0 tok)

theorem hrec : GorecoverContract (Extracted.program.link implW) rcA PW :=
  gorecover_at stubRc (gorecover_run engineAt T0)

def wmW : Memory := witMem (tabWords T0)

def wg : Nat := 0x50000
def wsp : Nat := 0x48000
def pA : Nat := 0x41000
def ret : Nat := 0x200000

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
      else if i = 29 then BitVec.ofNat 64 (wsp - 8) else if i = 0 then BitVec.ofNat 64 pA else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmW }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [BitVec.ofNat 64 pA] s0 := by
  refine ⟨rfl, rfl, fun i h => ?_⟩
  simp at h; subst h; rfl

theorem pre : PanicCallerOK PW s0 (PW.depth + 80) 16 ∧ Ptr s0.mem (BitVec.ofNat 64 pA) 8 true ∧
    Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 (s0.sp.toNat - (PW.depth + (PW.depth + 80)))
      (PW.depth + (PW.depth + 80) + 16) ∧
    Outside (BitVec.ofNat 64 pA).toNat 8 PW.priv ∧ 0 < PW.room s0.mem (gOf s0) ∧
    ∀ d ∈ PW.defers s0.mem (gOf s0), s0.sp.toNat ≤ d.sp := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_⟩
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
theorem nonvacuous : ∃ (impl : List Segment) (P : PanicRuntime) (U : State → Nat → Nat → Prop) (ret : Nat)
    (s : State), P.Laws ∧
    GoexitContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.Goexit") P U
      Extracted.funcs ∧
    GorecoverContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gorecover") P ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 pA] s ∧
    (PanicCallerOK P s (P.depth + 80) 16 ∧ Ptr s.mem (BitVec.ofNat 64 pA) 8 true ∧
      Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 (s.sp.toNat - (P.depth + (P.depth + 80)))
        (P.depth + (P.depth + 80) + 16) ∧
      Outside (BitVec.ofNat 64 pA).toNat 8 P.priv ∧ 0 < P.room s.mem (gOf s) ∧
      ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp) :=
  ⟨implW, PW, U0, ret, s0, P0_laws T0 RPa, hge, hrec, hret, setup, pre⟩

/-- So the guarantee is reached: `GoexitDefer` runs its deferred call (which adds 1 to `*p`) and
terminates the goroutine. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClassU PW U0 s0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ False
    | .panicked _ _ => False
    | .goexited s' => s'.mem.readLE (BitVec.ofNat 64 pA).toNat 8 =
        (s0.mem.readLE (BitVec.ofNat 64 pA).toNat 8 + 1) % 2 ^ 64 :=
  correctness implW PW (P0_laws T0 RPa) U0 hge hrec (BitVec.ofNat 64 pA) ret hret s0 setup pre

end Witness

end Proof
