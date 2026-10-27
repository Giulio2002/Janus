import Extracted

/-!
# `NestedRecover(e1, e2 any) (r uint64)`: recovering a nested panic recovers both (arm64)

`NestedRecover` is
`defer func() { if recover() != nil { r = 7 } }(); defer func() { panic(e2) }(); panic(e1)`
(two open-coded defers). `panic(e1)` runs the second deferred call, which panics with `e2` while
`e1` is unwinding; `e2` becomes the active panic and the walk goes on to the remaining deferred
call, whose `recover()` returns `e2` (it is called directly by the deferred call the `e2` panic
runs): that recovers `e2`, and with it the aborted `e1`; the runtime drops both and resumes the
frame at its `deferreturn` call.

**Guarantee (example 9 of docs/COVERAGE.md R6).** For every panic-runtime model `P` satisfying its
laws, every implementation of `runtime.gopanic`, `runtime.gorecover` and `runtime.deferreturn`
meeting their contracts (`Janus.Contracts.Panic`, pinned to the Go 1.26 runtime's code), every
admissible return address and every call state with no active panic, the runtime usable with
stack for the frame and the nested panic's runtime window, both `any`s non-nil and room for two
`_panic` records: the call **returns `7`**. It never panics.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Proof

local macro "func1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedRecover.func1"))
local macro "func2A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedRecover.func2"))
local macro "resumeA" : term => `(janus_eval% (Extracted.entry + 0x80))

/-- The memory the run may change: the runtime's memory, the window below and around the frame, but
not the two slots holding the saved return address and frame pointer. -/
abbrev W2 (P : PanicRuntime) (s : State) : List (Nat × Nat) :=
  P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat - 120), (s.sp.toNat - 104, s.sp.toNat + 40)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
/-- The deferred closure `NestedRecover.func1` run by the runtime while the nested panic (value
`(et, ed)`, started at `st`) unwinds on top of the aborted `(bt, bd)` panic: its `recover()` returns
the top panic's value, so it sets the named result to `7`; the top panic is marked recovered. -/
theorem closure_run (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (hrec : GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") P)
    (s e : State) (hc : PanicCallerOK P s (P.depth + 144) 40) (et ed bt bd st : Nat)
    (hne2 : et ≠ 0) (hw : ¬ P.wrapper (segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 0x24))
    (hpc1 : e.pc = BitVec.ofNat 64 func1A) (h26 : e.regs 26 = BitVec.ofNat 64 (s.sp.toNat - 40)) (h29 : e.regs 29 = e.sp - 8#64) (hS28e : e.regs 28 = s.regs 28)
    (hal1 : e.sp.toNat % 16 = 0) (hlo1 : s.sp.toNat - 112 - P.depth ≤ e.sp.toNat)
    (hhi1 : e.sp.toNat + 16 ≤ s.sp.toNat - 112)
    (hl30a : (e.regs 30).toNat % 4 = 0) (hl30b : (e.regs 30).toNat < 2 ^ 48)
    (henv1 : P.Env e.mem)
    (hW_e : MemFrame s.mem e.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)]))
    (hm_cap : e.mem.readLE (s.sp.toNat - 40 + 8) 8 = s.sp.toNat - 72)
    (hpn1' : P.panics e.mem (gOf s) = [{ arg := ⟨et, ed⟩, start := st }, { arg := ⟨bt, bd⟩, start := s.sp.toNat - 112 }])
    (hrpe0 : P.rp e.mem (gOf s) = (e.regs 30).toNat) :
    ReachesRet (Extracted.program.link impl) (e.regs 30) e (fun c' =>
      c'.pc = e.regs 30 ∧ c'.sp = e.sp ∧ c'.regs 28 = e.regs 28 ∧ c'.regs 18 = e.regs 18 ∧ P.Env c'.mem ∧
      P.panics c'.mem (gOf s) =
        [{ arg := ⟨et, ed⟩, start := st, recovered := true }, { arg := ⟨bt, bd⟩, start := s.sp.toNat - 112 }] ∧
      P.defers c'.mem (gOf s) = P.defers e.mem (gOf s) ∧
      P.saved c'.mem (gOf s) = P.saved e.mem (gOf s) ∧ P.room e.mem (gOf s) ≤ P.room c'.mem (gOf s) ∧
      MemFrame e.mem c'.mem (P.priv ++ [(e.sp.toNat - 32 - P.depth, e.sp.toNat),
        (s.sp.toNat - 72, s.sp.toNat - 64)]) ∧
      c'.mem.readLE (s.sp.toNat - 72) 8 = 7) := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd
  have hgv : e.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hW_e.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨hgo, by omega⟩)]
  have hga : e.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by
    rw [hW_e.accessible]; exact hg2
  have hwin' : e.mem.accessible (s.sp.toNat - (P.depth + (P.depth + 144))) (P.depth + (P.depth + 144) + 40) true = true := by
    rw [hW_e.accessible]; exact hst
  have hS28 : e.regs 28 = s.regs 28 := hS28e
  rw [show (e.regs 28) = e.regs 28 from rfl]
  have hpc1 := hpc1
  janus_run until [Extracted.program.contractAddr "runtime.gorecover"]
  refine ReachesRet.call hrec rfl
    ⟨PanicPre.of_within hc ?hf ?henv ?hlo ?hhi ?hal (by simp [setReg]; exact hS28e) ?hlr ?hlr', ?hga, ?hgb⟩ ?cont
  case hf => simp only [List.cons_append, List.nil_append]; janus_frame
  case henv =>
    apply hl.env_frame _ _ henv1
    apply Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + (P.depth + 144))) (hi := s.sp.toNat + 40)
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
    obtain ⟨⟨j2, f2, v2, m2, hs2, hfr2, henv2⟩, hdf2, hsv2', hrp2, hrm2, hnil2, hpanI⟩ := hpost
    have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    have hsegf : segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 36 = 598404 := by decide
    have agG : ∀ m, MemFrame e.mem m [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)] →
        Map.Agrees e.mem m P.priv := fun m hf =>
      Map.Agrees.of_window hf (Outside.of_sub hout (by omega) (by omega))
    have hrpe := hrpe0
    have hpanI' := hpanI { arg := ⟨et, ed⟩, start := st } [{ arg := ⟨bt, bd⟩, start := s.sp.toNat - 112 }]
    have hw' : ¬ P.wrapper 598404 := by rw [← hsegf]; exact hw
    have key : ∀ m g, g = (s.regs 28).toNat →
        MemFrame e.mem m [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)] →
        P.panics m g = [{ arg := ⟨et, ed⟩, start := st }, { arg := ⟨bt, bd⟩, start := s.sp.toNat - 112 }] := by
      intro m g hg hf
      rw [hg]; exact (hl.panics_frame _ _ _ (agG m hf)).trans hpn1'
    obtain ⟨hr0, hr1, hrec2⟩ := hpanI' (key _ _ (by dsimp only [gOf]; simp [setReg, hS28e]) (by janus_frame)) rfl rfl
      (by dsimp only; simpa [setReg] using hw') (by
        have hes : 40 ≤ e.sp.toNat ∧ e.sp.toNat % 16 = 0 := ⟨by omega, hal1⟩
        have h40 : (e.sp - 40#64).toNat = e.sp.toNat - 40 := by
          rw [BitVec.toNat_sub]; simp; omega
        have hrpm : P.rp e.mem (gOf s) = (e.regs 30).toNat := hrpe
        have hrp' : ∀ m, MemFrame e.mem m [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)] →
            P.rp m (gOf s) = (e.regs 30).toNat := fun m hf => by
          rw [hl.rp_frame _ _ _ (agG m hf)]; exact hrpm
        have hrp'' : ∀ m g, g = (s.regs 28).toNat →
            MemFrame e.mem m [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)] →
            P.rp m g = (e.regs 30).toNat := fun m g hg hf => by rw [hg]; exact hrp' m hf
        dsimp only
        simp only [setReg_apply, Nat.reduceEqDiff, reduceIte, h40]
        have hrd : (((e.mem.writeLE (BitVec.toNat e.sp - 32) 8 (BitVec.toNat (e.regs 30))).writeLE
            (BitVec.toNat e.sp - 40) 8 (BitVec.toNat e.sp - 8)).writeLE (BitVec.toNat e.sp - 16) 8
            (e.mem.readLE (BitVec.toNat s.sp - 40 + 8) 8)).readLE (BitVec.toNat e.sp - 40 + 8) 8 =
            (e.regs 30).toNat := by
          rw [show BitVec.toNat e.sp - 40 + 8 = BitVec.toNat e.sp - 32 by omega]
          simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
          exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                     have := (e.regs 30).isLt; omega)
        rw [hrd]
        exact (hrp'' _ _ (by dsimp only [gOf]; simp [setReg, hS28e]) (by janus_frame)).symm)
    subst hs2
    have h32 : (e.sp - 32#64).toNat = e.sp.toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
    simp only [calleeStack, h32, retState, callRegs_apply, List.getD_nil, setReg_apply, reduceIte,
      Nat.reduceEqDiff] at hfr2 hr0 hr1 hrec2 henv2
    have hj0 : j2 0 ≠ 0 := fun h => hne2 (by rw [← hr0, h]; rfl)
    have hcap' : e.mem.readLE (BitVec.toNat s.sp - 40 + 8) 8 = s.sp.toNat - 72 := by
      exact hm_cap
    have hacc7 : m2.accessible (s.sp.toNat - 72) 8 true = true := by
      rw [hfr2.accessible]; simp only [Memory.accessible_writeLE]
      exact Memory.accessible_mono _ hwin' (by omega) (by omega)
    janus_run [hcap']
    have hag7 : Map.Agrees m2 (m2.writeLE (s.sp.toNat - 72) 8 7) P.priv :=
      Map.Agrees.of_window (lo := s.sp.toNat - 72) (hi := s.sp.toNat - 40) (by janus_frame)
        (Outside.of_sub hout (by omega) (by omega))
    have hG : ∀ T : State, T.regs 28 = s.regs 28 → gOf T = gOf s := fun T h => by simp only [gOf, h]
    simp only [retState] at hdf2 hsv2' hrp2 hrm2
    rw [hG _ (by simp [setReg, hS28e])] at hdf2 hsv2' hrm2 hrec2
    have hagX : Map.Agrees e.mem
        (((e.mem.writeLE (BitVec.toNat e.sp - 32) 8 (BitVec.toNat (e.regs 30))).writeLE (BitVec.toNat e.sp - 40) 8
            (BitVec.toNat e.sp - 8)).writeLE (BitVec.toNat e.sp - 16) 8 (e.mem.readLE (BitVec.toNat s.sp - 40 + 8) 8))
        P.priv :=
      Map.Agrees.of_window (lo := e.sp.toNat - 32 - P.depth) (hi := e.sp.toNat) (by janus_frame)
        (Outside.of_sub hout (by omega) (by omega))
    have hp2' : P.panics (m2.writeLE (BitVec.toNat s.sp - 72) 8 7) (gOf s) =
        [{ arg := ⟨et, ed⟩, start := st, recovered := true }, { arg := ⟨bt, bd⟩, start := s.sp.toNat - 112 }] := by
      rw [hl.panics_frame _ _ _ hag7]; exact hrec2
    refine ⟨hl.env_frame _ _ henv2 hag7, hp2', ?_, ?_, ?_, ?_⟩
    · rw [hl.defers_frame _ _ _ hag7]; rw [hdf2]; exact hl.defers_frame _ _ _ hagX
    · rw [hl.saved_frame _ _ _ hag7]; rw [hsv2']; exact hl.saved_frame _ _ _ hagX
    · rw [hl.room_frame _ _ _ hag7]; exact Nat.le_trans (Nat.le_of_eq (hl.room_frame _ _ _ hagX).symm) hrm2
    · try simp only [List.cons_append, List.nil_append]
      janus_frame

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hpan : GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs)
    (hrec : GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U)
    (e1t e1d e2t e2d : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [e1t, e1d, e2t, e2d]
      (fun s => PanicCallerOK P s (P.depth + 144) 40 ∧ P.Calm s.mem (s.regs 28).toNat ∧
        e1t.toNat ≠ 0 ∧ e2t.toNat ≠ 0 ∧ 2 ≤ P.room s.mem (gOf s) ∧
        (∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp) ∧
        ¬ P.wrapper (segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 0x24))
      (goClassU P U)
      (fun _ s' => (s'.regs 0).toNat = 7)
      (fun _ _ _ => False) := by
  intro ret hret s hs ⟨hc, hcalm, hne1, hne2, hroom, hds, hw⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd
  have h96 : (s.sp - 112#64).toNat = s.sp.toNat - 112 := by rw [BitVec.toNat_sub]; simp; omega
  have h256 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
    hret.fetch_none ?_
  janus_run until [Extracted.program.contractAddr "runtime.gopanic"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun S hS => ?_
  have hSpc : S.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by rw [hS]; rfl
  have hS30 : S.regs 30 = BitVec.ofNat 64 598268 := by rw [hS] <;> rfl
  have hS0 : S.regs 0 = e1t := by rw [hS] <;> simp [setReg, h_x0]
  have hS1 : S.regs 1 = e1d := by rw [hS] <;> simp [setReg, h_x1]
  have hS28 : S.regs 28 = s.regs 28 := by rw [hS] <;> simp [setReg]
  have hS18 : S.regs 18 = s.regs 18 := by rw [hS] <;> simp [setReg]
  have hSsp : S.sp.toNat = s.sp.toNat - 112 := by
    rw [hS]; simp only; rw [BitVec.toNat_sub]; simp; omega
  have hSf : MemFrame s.mem S.mem [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)] := by
    rw [hS]; janus_frame
  have hbits : S.mem.readLE (s.sp.toNat - 73) 1 = 3 := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  have hslot0 : S.mem.readLE (s.sp.toNat - 24) 8 = s.sp.toNat - 40 := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)
  have hslot1 : S.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 64 := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)
  have hfv1 : S.mem.readLE (s.sp.toNat - 40) 8 = func1A := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    try decide
  have hfv2 : S.mem.readLE (s.sp.toNat - 64) 8 = func2A := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    try decide
  have hcap1 : S.mem.readLE (s.sp.toNat - 32) 8 = s.sp.toNat - 72 := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)
  have hcap2t : S.mem.readLE (s.sp.toNat - 56) 8 = e2t.toNat := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := e2t.isLt; omega)
  have hcap2d : S.mem.readLE (s.sp.toNat - 48) 8 = e2d.toNat := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := e2d.isLt; omega)
  obtain ⟨fi, hfi⟩ : ∃ fi : FuncInfo, fi = FuncInfo.named Extracted.funcs "example.com/basic.NestedRecover" := ⟨_, rfl⟩
  have f_frame : fi.frame = 112 := by rw [hfi]; rfl
  have f_od : fi.openDefer = some (65, 16) := by rw [hfi]; rfl
  have f_res : fi.resume = Extracted.entry + 0x80 := by rw [hfi]; rfl
  have hagS : Map.Agrees s.mem S.mem P.priv :=
    Map.Agrees.of_window hSf (Outside.of_sub hout (by omega) (by omega))
  have hgS : gOf S = gOf s := by simp only [gOf, hS28]
  have hdsS : P.defers S.mem (gOf S) = P.defers s.mem (gOf s) := by rw [hgS]; exact hl.defers_frame _ _ _ hagS
  have hdsS' : ∀ d ∈ P.defers S.mem (gOf S), S.sp.toNat < d.sp := by
    intro d hd; rw [hdsS] at hd; have := hds d hd; omega
  have hri : recItems (s.sp.toNat - 112) (P.defers S.mem (gOf S)) = [] :=
    recItems_above (by rw [← hSsp]; exact hdsS')
  have hF : frameOf fi S.sp.toNat S.mem =
      ⟨s.sp.toNat - 112, s.sp.toNat, Extracted.entry + 0x80, some (s.sp.toNat - 73, s.sp.toNat - 24)⟩ := by
    simp only [frameOf, FuncInfo.bound, FuncInfo.bitsAt, FuncInfo.slotsAt, FuncInfo.varp, f_frame, f_od, hSsp,
      Option.map_some, Option.getD_some, f_res]
    have e1 : s.sp.toNat - 112 + 112 - 8 - 65 = s.sp.toNat - 73 := by omega
    have e2 : s.sp.toNat - 112 + 112 - 8 - 16 = s.sp.toNat - 24 := by omega
    have e3 : s.sp.toNat - 112 + 112 = s.sp.toNat := by omega
    rw [e1, e2, e3, hbits]; rfl
  have hob : openBits 3 = [1, 0] := by decide
  have hI : frameItems S.mem (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S)) =
      [{ fn := s.sp.toNat - 64, bits := some 1, chain := P.defers S.mem (gOf S) },
       { fn := s.sp.toNat - 40, bits := some 0, chain := P.defers S.mem (gOf S) }] := by
    have e1 : s.sp.toNat - 24 + 8 * 1 = s.sp.toNat - 16 := by omega
    have e2 : s.sp.toNat - 24 + 8 * 0 = s.sp.toNat - 24 := by omega
    rw [hF]
    simp only [frameItems, openItems, hbits, hob, List.map_cons, List.map_nil, hri, List.append_nil, e1, e2,
      hslot0, hslot1, Nat.reducePow, Nat.reduceMod]
  refine GopanicContract.apply (fi := fi) hpan hSpc (by rw [hS30, hfi]; rfl) ?_ ?_
  · refine ⟨PanicPre.of_within hc (hSf.mono fun a n h => by
        simp only [outside_append] at h; exact h.2) (hl.env_frame _ _ henv hagS) (by omega) (by omega)
        (by rw [hSsp]; omega) hS28 (by rw [hS30]; decide) (by rw [hS30]; decide),
      by rw [hS0]; exact hne1, ?_, ?_, ?_⟩
    · rw [hgS, hl.room_frame _ _ _ hagS]; omega
    · intro _
      have e : fi.bitsAt S.sp.toNat = s.sp.toNat - 73 := by
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
        rcases hi with rfl | rfl <;>
          refine ⟨by omega, ?_, by omega, by dsimp only; omega, Outside.of_sub hout (by omega) (by omega)⟩ <;>
          rw [hSf.accessible] <;>
          exact Janus.Contracts.IfaceModel.acc_read_of_write
            (Memory.accessible_mono _ hst (by omega) (by omega))
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
              (Memory.accessible_mono _ hst (by omega) (by omega)))
          | (simp only [hfv1, hfv2]; try decide)
  intro hE
  have hK : frameKeep S.mem (frameOf fi S.sp.toNat S.mem)
      (frameItems S.mem (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S))) =
      [(s.sp.toNat - 73, s.sp.toNat - 73 + 1), (s.sp.toNat - 16, s.sp.toNat - 16 + 8),
       (s.sp.toNat - 24, s.sp.toNat - 24 + 8), (s.sp.toNat - 64, s.sp.toNat - 64 + 8),
       (s.sp.toNat - 40, s.sp.toNat - 40 + 8)] := by
    have e1 : s.sp.toNat - 24 + 8 * 1 = s.sp.toNat - 16 := by omega
    have e2 : s.sp.toNat - 24 + 8 * 0 = s.sp.toNat - 24 := by omega
    rw [hI, hF]
    simp only [frameKeep, hbits, hob, List.map_cons, List.map_nil, List.cons_append, List.nil_append, e1, e2]
  rw [hK, hI, hF] at hE
  rw [Engine_cons] at hE
  obtain ⟨k1, eA, hst1A, ⟨hpc1A, h26A, h28A, h18A, h29A, hal1A, hlo1A, hhi1A, h30aA, h30bA, henv1A⟩,
    hfr1A, hb1A, hd1A, hpn1A, hrm1A, hrs1A, hcont1A, hnest1A⟩ := hE
  dsimp only at hpc1A h26A hlo1A hhi1A hfr1A hb1A hcont1A hrs1A hnest1A
  have hSfWA : MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  have hfr1'A : MemFrame S.mem eA.mem
      (P.priv ++ [(s.sp.toNat - 112 - P.depth, s.sp.toNat - 112 - 8), (s.sp.toNat - 73, s.sp.toNat - 73 + 1)]) := by
    refine hfr1A.mono fun a n h => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true, rtWin, bitsWin] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, by omega⟩, by omega⟩
  have hW_eA : MemFrame s.mem eA.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)]) :=
    hSfWA.trans hfr1'A fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hbyte : ∀ a, (a + 1 ≤ s.sp.toNat - 112 - P.depth ∨ s.sp.toNat - 112 - 8 ≤ a) →
      (a + 1 ≤ s.sp.toNat - 73 ∨ s.sp.toNat - 64 ≤ a) → Outside a 1 P.priv → eA.mem.readLE a 1 = S.mem.readLE a 1 := by
    intro a h1 h2 h3
    rw [hfr1'A.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h3, by omega, by omega⟩)]
  have hwd' : ∀ a n, Outside a n P.priv → (a + n ≤ s.sp.toNat - 112 - P.depth ∨ s.sp.toNat - 112 - 8 ≤ a) →
      (a + n ≤ s.sp.toNat - 73 ∨ s.sp.toNat - 64 ≤ a) → eA.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    rw [hfr1'A.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h1, by omega, by omega⟩)]
  have hwd : ∀ a, Outside a 8 P.priv → (a + 8 ≤ s.sp.toNat - 112 - P.depth ∨ s.sp.toNat - 112 - 8 ≤ a) →
      (a + 8 ≤ s.sp.toNat - 73 ∨ s.sp.toNat - 64 ≤ a) → eA.mem.readLE a 8 = S.mem.readLE a 8 :=
    fun a => hwd' a 8
  have hm_fv2 : eA.mem.readLE (s.sp.toNat - 64) 8 = func2A := by
    rw [hwd _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hfv2
  have hm_c2t : eA.mem.readLE (s.sp.toNat - 56) 8 = e2t.toNat := by
    rw [hwd _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hcap2t
  have hm_c2d : eA.mem.readLE (s.sp.toNat - 48) 8 = e2d.toNat := by
    rw [hwd _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hcap2d
  have hgv : eA.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hW_eA.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hgo, by omega⟩)]
  have hga : eA.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by
    rw [hW_eA.accessible]; exact hg2
  have hwin : eA.mem.accessible (s.sp.toNat - (P.depth + (P.depth + 144))) (P.depth + (P.depth + 144) + 40) true = true := by
    rw [hW_eA.accessible]; exact hst
  have hS28' : eA.regs 28 = s.regs 28 := by rw [h28A, hS28]
  have hS18' : eA.regs 18 = s.regs 18 := by rw [h18A, hS18]
  have hpn_e : P.panics eA.mem (gOf s) =
      { arg := ⟨e1t.toNat, e1d.toNat⟩, start := s.sp.toNat - 112 } :: P.panics s.mem (gOf s) := by
    have := hpn1A
    rw [hS0, hS1, hSsp, hgS, hl.panics_frame _ _ _ hagS, hS28] at this
    exact this
  rw [hm_fv2] at hpc1A
  refine GoReturns.of_steps (hst1A.withExit hret.fetch_none) ?_
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
    hret.fetch_none ?_
  janus_run [hm_c2t, hm_c2d] until [Extracted.program.contractAddr "runtime.gopanic"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun S2 hS2 => ?_
  have hesp : eA.sp.toNat = eA.sp.toNat := rfl
  have h32 : (eA.sp - 32#64).toNat = eA.sp.toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
  have hS2sp : S2.sp = eA.sp - 32#64 := by rw [hS2] <;> rfl
  have hS2spn : S2.sp.toNat = eA.sp.toNat - 32 := by rw [hS2sp]; exact h32
  have hS2f : MemFrame eA.mem S2.mem [(eA.sp.toNat - 40, eA.sp.toNat)] := by rw [hS2]; janus_frame
  have hcap2t' : S.mem.readLE (s.sp.toNat - 64 + 8) 8 = e2t.toNat := by
    rw [show s.sp.toNat - 64 + 8 = s.sp.toNat - 56 by omega]; exact hcap2t
  have hcap2d' : S.mem.readLE (s.sp.toNat - 64 + 16) 8 = e2d.toNat := by
    rw [show s.sp.toNat - 64 + 16 = s.sp.toNat - 48 by omega]; exact hcap2d
  have hS20 : S2.regs 0 = e2t := by rw [hS2]; simp [setReg, hcap2t']
  have hS21 : S2.regs 1 = e2d := by rw [hS2]; simp [setReg, hcap2d']
  have hS228 : S2.regs 28 = s.regs 28 := by rw [hS2]; simp [setReg]; exact hS28'
  have hS218 : S2.regs 18 = s.regs 18 := by rw [hS2]; simp [setReg]; exact hS18'
  have hS230 : S2.regs 30 = BitVec.ofNat 64 598352 := by rw [hS2] <;> rfl
  have hS2pc : S2.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by rw [hS2] <;> rfl
  have hgS2 : gOf S2 = gOf s := by simp only [gOf, hS228]
  have hS2fW : MemFrame s.mem S2.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)]) :=
    hW_eA.trans hS2f fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      omega⟩
  have hagE : Map.Agrees eA.mem S2.mem P.priv :=
    Map.Agrees.of_window (lo := eA.sp.toNat - 40) (hi := eA.sp.toNat) hS2f
      (Outside.of_sub hout (by omega) (by omega))
  obtain ⟨fi2, hfi2⟩ : ∃ fi : FuncInfo, fi = FuncInfo.named Extracted.funcs "example.com/basic.NestedRecover.func2" := ⟨_, rfl⟩
  have f2_frame : fi2.frame = 32 := by rw [hfi2]; rfl
  have f2_od : fi2.openDefer = none := by rw [hfi2]; rfl
  have f2_res : fi2.resume = func2A := by rw [hfi2]; rfl
  have hdE : P.defers eA.mem (gOf s) = P.defers s.mem (gOf s) := by
    have := hd1A; rw [hS28] at this; simp only [gOf] at this ⊢; exact this.trans hdsS
  have hdS2 : P.defers S2.mem (gOf S2) = P.defers s.mem (gOf s) := by
    rw [hgS2, hl.defers_frame _ _ _ hagE, hdE]
  have hds2 : ∀ d ∈ P.defers S2.mem (gOf S2), S2.sp.toNat < d.sp := by
    intro d hd; rw [hdS2] at hd; have := hds d hd; omega
  have hF2 : frameOf fi2 S2.sp.toNat S2.mem = ⟨eA.sp.toNat - 32, eA.sp.toNat, func2A, none⟩ := by
    simp only [frameOf, FuncInfo.bound, f2_frame, f2_od, hS2spn, Option.map_none, f2_res]
    have e3 : eA.sp.toNat - 32 + 32 = eA.sp.toNat := by omega
    rw [e3]
  have hri2 : recItems (eA.sp.toNat - 32) (P.defers S2.mem (gOf S2)) = [] :=
    recItems_above (by rw [← hS2spn]; exact hds2)
  have hI2 : frameItems S2.mem (frameOf fi2 S2.sp.toNat S2.mem) (P.defers S2.mem (gOf S2)) = [] := by
    rw [hF2]; simp only [frameItems, List.nil_append, hri2]
  have hrmS : P.room S.mem (gOf S) = P.room s.mem (gOf s) := by rw [hgS, hl.room_frame _ _ _ hagS]
  have hrmE : P.room s.mem (gOf s) ≤ P.room eA.mem (gOf s) + 1 := by
    have := hrm1A; rw [hS28] at this; simp only [gOf] at this ⊢; rw [hrmS] at this; simp only [gOf] at this; omega
  have hroomS2 : P.room S2.mem (gOf S2) = P.room eA.mem (gOf s) := by
    rw [hgS2, hl.room_frame _ _ _ hagE]
  refine GopanicContract.apply (fi := fi2) hpan hS2pc (by rw [hS230, hfi2]; rfl) ?_ ?_
  · refine ⟨PanicPre.of_within hc hS2fW (hl.env_frame _ _ henv1A hagE) (by omega) (by omega)
        (by rw [hS2spn]; omega) hS228 (by rw [hS230]; decide) (by rw [hS230]; decide),
      by rw [hS20]; exact hne2, ?_, ?_, ?_⟩
    · rw [hroomS2]; omega
    · intro h; rw [f2_od] at h; cases h
    · rw [hI2, hF2]; exact ⟨trivial, fun it h => absurd h (by simp)⟩
  intro hE2
  rw [hI2, hF2] at hE2
  rw [Engine_nil] at hE2
  obtain ⟨k2, d, hst2, hU, hpd, hdd, hdfr, hdenv, hdrm, hdsv⟩ := hE2
  refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
  have hS28g : (S.regs 28).toNat = gOf s := by simp [gOf, hS28]
  have hS2g : (S2.regs 28).toNat = gOf s := by simp [gOf, hS228]
  have hS2f' : MemFrame eA.mem S2.mem (P.priv ++ [(eA.sp.toNat - 32 - P.depth, eA.sp.toNat)]) :=
    hS2f.mono fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      omega
  have hWd : MemFrame eA.mem d.mem (P.priv ++ [(eA.sp.toNat - 32 - P.depth, eA.sp.toNat)]) :=
    hS2f'.trans hdfr fun a n h => ⟨h, by
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega⟩⟩
  have hU' : U d (S.regs 28).toNat eA.sp.toNat := by
    rw [hS28g, ← hS2g]; exact hU
  have hAg : Map.Agrees eA.mem d.mem
      [(eA.sp.toNat, s.sp.toNat - 112), (s.sp.toNat - 73, s.sp.toNat - 73 + 1),
        (s.sp.toNat - 16, s.sp.toNat - 16 + 8), (s.sp.toNat - 24, s.sp.toNat - 24 + 8),
        (s.sp.toNat - 64, s.sp.toNat - 64 + 8), (s.sp.toNat - 40, s.sp.toNat - 40 + 8)] := by
    refine Map.Agrees.of_memFrame hWd fun a ⟨r, hr, h1, h2⟩ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [outside_append, outside_cons, outside_nil, and_true]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at h1 h2 <;>
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩
  have hdef' : P.defers d.mem (S.regs 28).toNat = P.defers eA.mem (S.regs 28).toNat := by
    rw [hS28g, ← hS2g, hdd, (frameRecs_above (sp := eA.sp.toNat - 32) (by rw [← hS2spn]; exact hds2)).2, hdS2]
    rw [hS2g, hdE]
  have hsv' : P.saved d.mem (S.regs 28).toNat = P.saved eA.mem (S.regs 28).toNat := by
    rw [hS28g, ← hS2g, hdsv, hS2g, ← hgS2, hl.saved_frame _ _ _ hagE]
  have hpnS : P.panics S.mem (gOf S) = P.panics s.mem (gOf s) := by rw [hgS, hl.panics_frame _ _ _ hagS]
  have hpnS2 : P.panics S2.mem (gOf S2) = { arg := ⟨e1t.toNat, e1d.toNat⟩, start := s.sp.toNat - 112 } :: P.panics s.mem (gOf s) := by
    rw [hgS2, hl.panics_frame _ _ _ hagE]; exact hpn_e
  have hpn' : P.panics d.mem (S.regs 28).toNat =
      { arg := ⟨e2t.toNat, e2d.toNat⟩, start := eA.sp.toNat - 32 } ::
      { arg := ⟨(S.regs 0).toNat, (S.regs 1).toNat⟩, start := S.sp.toNat } :: P.panics S.mem (gOf S) := by
    rw [hS28g, ← hS2g, hpd, hpnS2, hpnS, hS0, hS1, hSsp, hS20, hS21, hS2spn]
  have hrm' : P.room S.mem (gOf S) - 1 ≤ P.room d.mem (S.regs 28).toNat + 1 := by
    have a1 : P.room S.mem (gOf S) - 1 ≤ P.room eA.mem (gOf s) := by have := hrm1A; rwa [hS28g] at this
    have a2 : P.room S2.mem (gOf S2) - 1 ≤ P.room d.mem (gOf s) := by have := hdrm; rwa [hS2g] at this
    rw [hS28g]; omega
  have hE' := hnest1A rfl d { arg := ⟨e2t.toNat, e2d.toNat⟩, start := eA.sp.toNat - 32 } hU' hAg hdenv hdef' hsv' hpn' rfl rfl
    (show eA.sp.toNat - 32 ≤ eA.sp.toNat by omega) hrm'
  have hcalmS : P.panics S.mem (gOf S) = [] := by rw [hgS]; exact hl.calm_frame _ _ _ hcalm hagS
  rw [Engine_cons] at hE'
  obtain ⟨k3, e, hst1, ⟨hpc1, h26, h28, h18, h29, hal1, hlo1, hhi1, h30a, h30b, henv1⟩,
    hfr1, hb1, hd1, hpn1, hrm1, hrs1, hcont1, -⟩ := hE'
  dsimp only at hpc1 h26 hlo1 hhi1 hfr1 hb1 hcont1 hrs1
  refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
  -- the memory the whole run may change: everything but the saved return address and frame pointer
  have hM_eA : MemFrame S.mem eA.mem (W2 P s) := hfr1'A.mono fun a n h => by
    simp only [W2, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, by omega, by omega⟩
  have hM_d : MemFrame S.mem d.mem (W2 P s) := hM_eA.trans hWd fun a n h => ⟨h, by
    simp only [W2, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, by omega⟩⟩
  have hM_e : MemFrame S.mem e.mem (W2 P s) := hM_d.trans hfr1 fun a n h => ⟨h, by
    simp only [W2, rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, by omega⟩, by omega⟩⟩
  have hW_e : MemFrame s.mem e.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)]) :=
    hSfWA.trans hM_e fun a n h => ⟨h, by
      simp only [W2, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hread : ∀ a n, Outside a n P.priv → s.sp.toNat - 40 ≤ a → a + n ≤ s.sp.toNat - 24 →
      e.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    rw [hfr1.readLE _ _ (by
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨h1, by omega⟩, by omega⟩),
      hWd.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h1, by omega⟩), hwd' a n h1 (by omega) (by omega)]
  have hm_fv : e.mem.readLE (s.sp.toNat - 40) 8 = func1A := by
    rw [hread _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hfv1
  have hm_cap : e.mem.readLE (s.sp.toNat - 40 + 8) 8 = s.sp.toNat - 72 := by
    rw [hread _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega),
      show s.sp.toNat - 40 + 8 = s.sp.toNat - 32 by omega]; exact hcap1
  have hS28' : e.regs 28 = s.regs 28 := by rw [h28, hS28]
  have hS18' : e.regs 18 = s.regs 18 := by rw [h18, hS18]
  have hpn1' : P.panics e.mem (gOf s) = [{ arg := ⟨e2t.toNat, e2d.toNat⟩, start := eA.sp.toNat - 32 },
      { arg := ⟨e1t.toNat, e1d.toNat⟩, start := s.sp.toNat - 112 }] := by
    have := hpn1
    rw [hS28, hS0, hS1, hSsp, hcalmS] at this
    simpa [gOf] using this
  have hgv : e.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hW_e.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨hgo, by omega⟩)]
  have hga : e.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by
    rw [hW_e.accessible]; exact hg2
  have hwin' : e.mem.accessible (s.sp.toNat - (P.depth + (P.depth + 144))) (P.depth + (P.depth + 144) + 40) true = true := by
    rw [hW_e.accessible]; exact hst
  have hsegf : segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 36 = 598404 := by decide
  rw [hm_fv] at hpc1
  have hrpe : P.rp e.mem (gOf s) = (e.regs 30).toNat := by
    have := hrs1.1
    simpa [hS28, gOf] using this
  have hcl := closure_run impl P hl hrec s e hc e2t.toNat e2d.toNat e1t.toNat e1d.toNat (eA.sp.toNat - 32)
    hne2 hw hpc1 h26 h29 hS28' hal1 (by omega) (by omega) h30a h30b henv1 hW_e hm_cap hpn1' hrpe
  obtain ⟨k2, c', hst2, -, hcpc, hcsp, hc28, hc18, hcenv, hcpan, hcdef, hcsv, hcrm, hcfr, hc7⟩ := hcl
  refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
  have hagc : Map.Agrees e.mem c'.mem ((e.sp.toNat, s.sp.toNat - 112) ::
      [(s.sp.toNat - 73, s.sp.toNat - 73 + 1), (s.sp.toNat - 16, s.sp.toNat - 16 + 8),
       (s.sp.toNat - 24, s.sp.toNat - 24 + 8), (s.sp.toNat - 64, s.sp.toNat - 64 + 8),
       (s.sp.toNat - 40, s.sp.toNat - 40 + 8)]) := by
    refine Map.Agrees.of_memFrame hcfr fun a ⟨r, hr, h1, h2⟩ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [outside_append, outside_cons, outside_nil, and_true]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at h1 h2 <;>
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩
  have hdr1 : DeferReturned P (S.regs 28) (S.regs 18) (s.sp.toNat - 112)
      [(s.sp.toNat - 73, s.sp.toNat - 73 + 1), (s.sp.toNat - 16, s.sp.toNat - 16 + 8),
       (s.sp.toNat - 24, s.sp.toNat - 24 + 8), (s.sp.toNat - 64, s.sp.toNat - 64 + 8),
       (s.sp.toNat - 40, s.sp.toNat - 40 + 8)] e c' := by
    refine ⟨hcpc, hcsp, by rw [hc28, h28], by rw [hc18, h18], hagc, hcenv, ?_, ?_, ?_⟩
    · have := hcdef; simpa [gOf, hS28] using this
    · have := hcsv; simpa [gOf, hS28] using this
    · have := hcrm; simpa [gOf, hS28] using this
  have hpanc : P.panics c'.mem (S.regs 28).toNat =
      { arg := ⟨e2t.toNat, e2d.toNat⟩, start := eA.sp.toNat - 32, recovered := true } ::
      ({ arg := ⟨(S.regs 0).toNat, (S.regs 1).toNat⟩, start := S.sp.toNat } :: P.panics S.mem (gOf S)) := by
    rw [hS28, hS0, hS1, hSsp, hcalmS]
    have := hcpan; simpa [gOf] using this
  have hr2s : eA.sp.toNat - 32 ≤ s.sp.toNat - 112 := by omega
  have hrecov := (hcont1 c' hdr1).2 rfl _ _ rfl hpanc (by
    intro q hq
    rw [hpanc] at hq
    simp only [hcalmS, List.takeWhile, hr2s, hSsp] at hq
    simp at hq
    rcases hq with rfl | rfl <;> rfl)
  obtain ⟨k3, d5, hst3, hdpc5, hdsp5, hd295, hd285, hd185, hdfr5, hdenv5, hdpan5, hddef5, hdsv5, hdroom5⟩ := hrecov
  refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
  have hM_c : MemFrame S.mem c'.mem (W2 P s) := hM_e.trans hcfr fun a n h => ⟨h, by
    simp only [W2, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, by omega, by omega⟩⟩
  have hM_d5 : MemFrame S.mem d5.mem (W2 P s) := hM_c.trans hdfr5 fun a n h => ⟨h, by
    simp only [W2, rtWin, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, by omega⟩⟩
  obtain ⟨dr, dsp, dpc, dfl, dm, ddz, dv, dtp, dfc, dfs⟩ := d5
  dsimp only at hdpc5 hdsp5 hd295 hd285 hd185
  rw [show Extracted.entry + 128 = resumeA from rfl] at hdpc5
  subst hdpc5 hdsp5
  have hsp112' : BitVec.ofNat 64 (s.sp.toNat - 112) = s.sp - 112#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hdr' : dr = setReg (setReg (setReg dr 18 (s.regs 18)) 28 (s.regs 28)) 29 (s.sp - 112#64 - 8) := by
    funext i; simp only [setReg]
    by_cases h29 : i = 29
    · rw [if_pos h29, h29]; rw [hsp112'] at hd295; exact hd295
    · rw [if_neg h29]
      by_cases h28 : i = 28
      · rw [if_pos h28, h28, hd285, hS28]
      · rw [if_neg h28]
        by_cases h18 : i = 18
        · rw [if_pos h18, h18, hd185, hS18]
        · rw [if_neg h18]
  rw [hdr']
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn"))
    hret.fetch_none ?_
  janus_run until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun D hD => ?_
  have hDm : D.mem = dm := by rw [hD]
  have hDsp : D.sp = BitVec.ofNat 64 (s.sp.toNat - 112) := by rw [hD]
  have hDspn : D.sp.toNat = s.sp.toNat - 112 := by
    rw [hDsp, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; have := s.sp.isLt; omega
  have hD28 : D.regs 28 = s.regs 28 := by rw [hD]; simp [setReg]
  have hD30 : D.regs 30 = 598276#64 := by rw [hD]; simp [setReg]
  have hDpc : D.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by rw [hD]; rfl
  have hgD : gOf D = gOf s := by simp only [gOf, hD28]
  dsimp only at hdpan5 hddef5 hdsv5 hdroom5
  have hsvD : P.saved D.mem (gOf D) = none := by
    rw [hDm, hgD]; have := hdsv5; rw [if_pos (by decide)] at this; simpa [gOf, hS28] using this
  have hdefD : P.defers D.mem (gOf D) = P.defers s.mem (gOf s) := by
    rw [hDm, hgD]
    have h1 := hddef5; have h2 := hcdef; have h3 := hd1
    simp only [gOf, hS28] at h1 h2 h3 ⊢
    rw [h1, h2, h3]; have h4 := hdsS; simp only [gOf, hS28] at h4; exact h4
  have hF : retFrame P D = ⟨s.sp.toNat - 112, s.sp.toNat - 112, 0, none⟩ := by
    simp only [retFrame, hsvD, hDspn]
  have hds' : ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat - 112 < d.sp := fun d hd => by have := hds d hd; omega
  have hdI : frameItems D.mem (retFrame P D) (P.defers D.mem (gOf D)) = [] := by
    rw [hF, hdefD]; simp only [frameItems, List.nil_append, recItems_above hds']
  have hWD : MemFrame s.mem dm (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)]) := by
    have h1 : MemFrame s.mem c'.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 144)), s.sp.toNat + 40)]) :=
      hW_e.trans hcfr fun a n h => ⟨h, by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
        obtain ⟨h1, h2⟩ := h
        exact ⟨h1, by omega, by omega⟩⟩
    refine h1.trans hdfr5 fun a n h => ⟨h, ?_⟩
    simp only [outside_append, outside_cons, outside_nil, and_true, rtWin] at h ⊢
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, by omega⟩
  have hpre : PanicPre P 0 D := PanicPre.of_within hc (hDm ▸ hWD) (hDm ▸ hdenv5) (by omega) (by omega) (by rw [hDspn]; omega)
    hD28 (by rw [hD30]; decide) (by rw [hD30]; decide)
  refine DeferreturnContract.apply (S := D) hdr hDpc ⟨hpre, ?_⟩ ?_
  · rw [hdI, hF]; exact ⟨trivial, fun it h => absurd h (by simp)⟩
  intro hE
  rw [hdI, Engine_nil] at hE
  obtain ⟨k4, d2, hst4, hfin⟩ := hE
  obtain ⟨hfpc, hfsp, hf28, hf18, hf29, hfmf, hfenv, -⟩ := hfin
  refine GoReturns.of_steps (hst4.withExit hret.fetch_none) ?_
  have hD29 : D.regs 29 = s.sp - 120#64 := by rw [hD]; simp [setReg]
  have hD18 : D.regs 18 = s.regs 18 := by rw [hD]; simp [setReg]
  obtain ⟨er, esp, epc, efl, em, edz, ev, etp, efc, efs⟩ := d2
  dsimp only at hfpc hfsp hf28 hf18 hf29 hfmf
  rw [hD30] at hfpc
  rw [hDsp] at hfsp
  subst hfpc hfsp
  have her : er = setReg (setReg (setReg er 18 (s.regs 18)) 28 (s.regs 28)) 29 (s.sp - 120#64) := by
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
  have hxfer : ∀ a n v, Outside a n P.priv → s.sp.toNat - 120 ≤ a → a + n ≤ s.sp.toNat - 104 →
      S.mem.readLE a n = v → dm.readLE a n = v := by
    intro a n v hpr h1 h2 hv
    rw [← hv]
    exact hM_d5.readLE _ _ (by
      simp only [W2, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpr, by omega, by omega⟩)
  have hfpE : dm.readLE (s.sp.toNat - 112 - 8) 8 = (s.regs 29).toNat := by
    refine hxfer _ _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) ?_
    have e120 : s.sp.toNat - 112 - 8 = s.sp.toNat - 120 := by omega
    rw [hS, e120]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                               have := (s.regs 29).isLt; omega)
  have hlrE : dm.readLE (s.sp.toNat - 112) 8 = ret := by
    refine hxfer _ _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) ?_
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                               have := hret.user; omega)
  have h7E : dm.readLE (s.sp.toNat - 112 + 40) 8 = 7 := by
    rw [hdfr5.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true, rtWin]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩),
      show s.sp.toNat - 112 + 40 = s.sp.toNat - 72 by omega]
    exact hc7
  have hr48 : ret < 2 ^ 48 := hret.user
  have hra : ret % 4 = 0 := hret.aligned
  refine GoReturns.of_reaches ?_
  janus_run [hlrE]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := s.sp.isLt; omega
  · have hfpS : S.mem.readLE (s.sp.toNat - 112 - 8) 8 = (s.regs 29).toNat := by
      have e120 : s.sp.toNat - 112 - 8 = s.sp.toNat - 120 := by omega
      rw [hS, e120]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 have := (s.regs 29).isLt; omega)
    rw [hfpS]; exact BitVec.ofNat_toNat _ _
  · exact h7E

namespace Witness

open Janus.Contracts.PanicSat Janus.Contracts.PanicModel

abbrev T0 : List FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : PanicRuntime := P0 T0 RPa

def gA : Nat := Extracted.program.contractAddr "runtime.gopanic"
def rA : Nat := Extracted.program.contractAddr "runtime.gorecover"
def dA : Nat := Extracted.program.contractAddr "runtime.deferreturn"

/-- The code linked next to `NestedRecover`: the model engine and a branch to it at each contract
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

def wg : Nat := 0x50000
def wsp : Nat := 0x48000
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
      else if i = 29 then BitVec.ofNat 64 (wsp - 8) else if i = 0 then 1#64
      else if i = 2 then 2#64 else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmW }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [1#64, 0#64, 2#64, 0#64] s0 := by
  refine ⟨rfl, rfl, fun i h => ?_⟩
  simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
theorem pre : PanicCallerOK PW s0 (PW.depth + 144) 40 ∧ PW.Calm s0.mem (s0.regs 28).toNat ∧
    (1#64 : BitVec 64).toNat ≠ 0 ∧ (2#64 : BitVec 64).toNat ≠ 0 ∧ 2 ≤ PW.room s0.mem (gOf s0) ∧
    (∀ d ∈ PW.defers s0.mem (gOf s0), s0.sp.toNat ≤ d.sp) ∧
    ¬ PW.wrapper (segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 0x24) := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_⟩, ?_, by decide, by decide, ?_, ?_, id⟩
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
theorem nonvacuous : ∃ (impl : List Segment) (P : PanicRuntime) (U : State → Nat → Nat → Prop) (ret : Nat)
    (s : State), P.Laws ∧
    GopanicContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gopanic") P U
      Extracted.funcs ∧
    GorecoverContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gorecover") P ∧
    DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P U ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [1#64, 0#64, 2#64, 0#64] s ∧
    (PanicCallerOK P s (P.depth + 144) 40 ∧ P.Calm s.mem (s.regs 28).toNat ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧
      (2#64 : BitVec 64).toNat ≠ 0 ∧ 2 ≤ P.room s.mem (gOf s) ∧
      (∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp) ∧
      ¬ P.wrapper (segAddr Extracted.program "example.com/basic.NestedRecover.func1" + 0x24)) :=
  ⟨implW, PW, U0, ret, s0, P0_laws T0 RPa, hpan, hrec, hdr, hret, setup, pre⟩

/-- So the guarantee is reached: `NestedRecover` panics, the nested panic is recovered by the
remaining deferred call, and the call returns `7`. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClassU PW U0 s0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ (s'.regs 0).toNat = 7
    | .panicked _ _ => False
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U0 hpan hrec hdr 1#64 0#64 2#64 0#64 ret hret s0 setup pre

end Witness

end Proof
