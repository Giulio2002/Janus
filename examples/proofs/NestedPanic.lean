import Extracted

/-!
# `NestedPanic(p *uint64, e1, e2 any)`: a deferred call panics while a panic unwinds (arm64)

`NestedPanic` is `defer func() { *p = 1 }(); defer func() { panic(e2) }(); panic(e1)` (two
open-coded defers). `panic(e1)` runs the second deferred call, which panics with `e2` while `e1`
is unwinding: the new `runtime.gopanic` pushes its `_panic`, aborts `e1`'s and carries on with the
same walk of the frame's deferred calls, so the remaining call (`*p = 1`) runs and the frame is
left with `e2`'s panic on top of the aborted `e1`'s.

**Guarantee (example 8 of docs/COVERAGE.md R6).** For every panic-runtime model `P` satisfying its
laws, every implementation of `runtime.gopanic` meeting its contract (`Janus.Contracts.Panic`, pinned
to the Go 1.26 runtime's code; the contract is used twice, for the outer and the nested panic),
every admissible return address and every call state in which the runtime is usable with stack for
the frame and the nested panic's runtime window below it, `p` points to a writable word outside the
runtime's memory and the stack window, both `any`s are non-nil and the runtime has room for two
`_panic` records: the call **panics with `e2`**, never returns, and `*p = 1`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Proof


/-! Code addresses are read off the extraction (`janus_eval%`), never copied: a relinked
binary needs no edit. -/
local macro "loc_NestedPanic_124" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedPanic" + 124))
local macro "loc_NestedPanic_func2_32" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedPanic.func2" + 32))

local macro "func1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedPanic.func1"))
local macro "func2A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedPanic.func2"))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hpan : GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs)
    (p e1t e1d e2t e2d : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [p, e1t, e1d, e2t, e2d]
      (fun s => PanicCallerOK P s (P.depth + 128) 48 ∧ Ptr s.mem p 8 true ∧
        Spec.Disjoint p.toNat 8 (s.sp.toNat - (P.depth + (P.depth + 128))) (P.depth + (P.depth + 128) + 48) ∧
        Outside p.toNat 8 P.priv ∧ e1t.toNat ≠ 0 ∧ e2t.toNat ≠ 0 ∧ 2 ≤ P.room s.mem (gOf s) ∧
        ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp)
      (goClassU P U)
      (fun _ _ => False)
      (fun s v s' => v = ⟨e2t.toNat, e2d.toNat⟩ ∧ s'.mem.readLE p.toNat 8 = 1) := by
  intro ret hret s hs ⟨hc, ⟨hp, hp'⟩, hdj, hpo, hne1, hne2, hroom, hds⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd hdj
  have h96 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := by rw [BitVec.toNat_sub]; simp; omega
  have h256 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
    hret.fetch_none ?_
  janus_run until [Extracted.program.contractAddr "runtime.gopanic"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun S hS => ?_
  have hSpc : S.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by rw [hS]; rfl
  have hS30 : S.regs 30 = BitVec.ofNat 64 loc_NestedPanic_124 := by rw [hS] <;> rfl
  have hS0 : S.regs 0 = e1t := by rw [hS] <;> simp [setReg]
  have hS1 : S.regs 1 = e1d := by rw [hS] <;> simp [setReg]
  have hS28 : S.regs 28 = s.regs 28 := by rw [hS] <;> simp [setReg]
  have hS18 : S.regs 18 = s.regs 18 := by rw [hS] <;> simp [setReg]
  have hSsp : S.sp.toNat = s.sp.toNat - 96 := by
    rw [hS]; simp only; rw [BitVec.toNat_sub]; simp; omega
  have hSf : MemFrame s.mem S.mem [(s.sp.toNat - (P.depth + (P.depth + 128)), s.sp.toNat + 48)] := by
    rw [hS]; janus_frame
  have hbits : S.mem.readLE (s.sp.toNat - 65) 1 = 3 := by
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
  have hcap1 : S.mem.readLE (s.sp.toNat - 32) 8 = p.toNat := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := p.isLt; omega)
  have hcap2t : S.mem.readLE (s.sp.toNat - 56) 8 = e2t.toNat := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := e2t.isLt; omega)
  have hcap2d : S.mem.readLE (s.sp.toNat - 48) 8 = e2d.toNat := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := e2d.isLt; omega)
  obtain ⟨fi, hfi⟩ : ∃ fi : FuncInfo, fi = FuncInfo.named Extracted.funcs "example.com/basic.NestedPanic" := ⟨_, rfl⟩
  have f_frame : fi.frame = 96 := by rw [hfi]; rfl
  have f_od : fi.openDefer = some (57, 16) := by rw [hfi]; rfl
  have f_res : fi.resume = Extracted.entry + 0x80 := by rw [hfi]; rfl
  have hagS : Map.Agrees s.mem S.mem P.priv :=
    Map.Agrees.of_window hSf (Outside.of_sub hout (by omega) (by omega))
  have hgS : gOf S = gOf s := by simp only [gOf, hS28]
  have hdsS : P.defers S.mem (gOf S) = P.defers s.mem (gOf s) := by rw [hgS]; exact hl.defers_frame _ _ _ hagS
  have hdsS' : ∀ d ∈ P.defers S.mem (gOf S), S.sp.toNat < d.sp := by
    intro d hd; rw [hdsS] at hd; have := hds d hd; omega
  have hri : recItems (s.sp.toNat - 96) (P.defers S.mem (gOf S)) = [] :=
    recItems_above (by rw [← hSsp]; exact hdsS')
  have hF : frameOf fi S.sp.toNat S.mem =
      ⟨s.sp.toNat - 96, s.sp.toNat, Extracted.entry + 0x80, some (s.sp.toNat - 65, s.sp.toNat - 24)⟩ := by
    simp only [frameOf, FuncInfo.bound, FuncInfo.bitsAt, FuncInfo.slotsAt, FuncInfo.varp, f_frame, f_od, hSsp,
      Option.map_some, Option.getD_some, f_res]
    have e1 : s.sp.toNat - 96 + 96 - 8 - 57 = s.sp.toNat - 65 := by omega
    have e2 : s.sp.toNat - 96 + 96 - 8 - 16 = s.sp.toNat - 24 := by omega
    have e3 : s.sp.toNat - 96 + 96 = s.sp.toNat := by omega
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
      have e : fi.bitsAt S.sp.toNat = s.sp.toNat - 65 := by
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
      [(s.sp.toNat - 65, s.sp.toNat - 65 + 1), (s.sp.toNat - 16, s.sp.toNat - 16 + 8),
       (s.sp.toNat - 24, s.sp.toNat - 24 + 8), (s.sp.toNat - 64, s.sp.toNat - 64 + 8),
       (s.sp.toNat - 40, s.sp.toNat - 40 + 8)] := by
    have e1 : s.sp.toNat - 24 + 8 * 1 = s.sp.toNat - 16 := by omega
    have e2 : s.sp.toNat - 24 + 8 * 0 = s.sp.toNat - 24 := by omega
    rw [hI, hF]
    simp only [frameKeep, hbits, hob, List.map_cons, List.map_nil, List.cons_append, List.nil_append, e1, e2]
  rw [hK, hI, hF] at hE
  rw [Engine_cons] at hE
  obtain ⟨k1, e, hst1, ⟨hpc1, h26, h28, h18, h29, hal1, hlo1, hhi1, h30a, h30b, henv1⟩,
    hfr1, hb1, hd1, hpn1, hrm1, hrs1, hcont1, hnest1⟩ := hE
  dsimp only at hpc1 h26 hlo1 hhi1 hfr1 hb1 hcont1 hrs1 hnest1
  have hSfW : MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 128)), s.sp.toNat + 48)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  have hfr1' : MemFrame S.mem e.mem
      (P.priv ++ [(s.sp.toNat - 96 - P.depth, s.sp.toNat - 96 - 8), (s.sp.toNat - 65, s.sp.toNat - 65 + 1)]) := by
    refine hfr1.mono fun a n h => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true, rtWin, bitsWin] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, by omega⟩, by omega⟩
  have hW_e : MemFrame s.mem e.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 128)), s.sp.toNat + 48)]) :=
    hSfW.trans hfr1' fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hbyte : ∀ a, (a + 1 ≤ s.sp.toNat - 96 - P.depth ∨ s.sp.toNat - 96 - 8 ≤ a) →
      (a + 1 ≤ s.sp.toNat - 65 ∨ s.sp.toNat - 64 ≤ a) → Outside a 1 P.priv → e.mem.readLE a 1 = S.mem.readLE a 1 := by
    intro a h1 h2 h3
    rw [hfr1'.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h3, by omega, by omega⟩)]
  have hwd' : ∀ a n, Outside a n P.priv → (a + n ≤ s.sp.toNat - 96 - P.depth ∨ s.sp.toNat - 96 - 8 ≤ a) →
      (a + n ≤ s.sp.toNat - 65 ∨ s.sp.toNat - 64 ≤ a) → e.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    rw [hfr1'.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h1, by omega, by omega⟩)]
  have hwd : ∀ a, Outside a 8 P.priv → (a + 8 ≤ s.sp.toNat - 96 - P.depth ∨ s.sp.toNat - 96 - 8 ≤ a) →
      (a + 8 ≤ s.sp.toNat - 65 ∨ s.sp.toNat - 64 ≤ a) → e.mem.readLE a 8 = S.mem.readLE a 8 :=
    fun a => hwd' a 8
  have hm_fv2 : e.mem.readLE (s.sp.toNat - 64) 8 = func2A := by
    rw [hwd _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hfv2
  have hm_c2t : e.mem.readLE (s.sp.toNat - 56) 8 = e2t.toNat := by
    rw [hwd _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hcap2t
  have hm_c2d : e.mem.readLE (s.sp.toNat - 48) 8 = e2d.toNat := by
    rw [hwd _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hcap2d
  have hgv : e.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hW_e.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hgo, by omega⟩)]
  have hga : e.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by
    rw [hW_e.accessible]; exact hg2
  have hwin : e.mem.accessible (s.sp.toNat - (P.depth + (P.depth + 128))) (P.depth + (P.depth + 128) + 48) true = true := by
    rw [hW_e.accessible]; exact hst
  have hS28' : e.regs 28 = s.regs 28 := by rw [h28, hS28]
  have hS18' : e.regs 18 = s.regs 18 := by rw [h18, hS18]
  have hpn_e : P.panics e.mem (gOf s) =
      { arg := ⟨e1t.toNat, e1d.toNat⟩, start := s.sp.toNat - 96 } :: P.panics s.mem (gOf s) := by
    have := hpn1
    rw [hS0, hS1, hSsp, hgS, hl.panics_frame _ _ _ hagS, hS28] at this
    exact this
  rw [hm_fv2] at hpc1
  refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
    hret.fetch_none ?_
  janus_run [hm_c2t, hm_c2d] until [Extracted.program.contractAddr "runtime.gopanic"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun S2 hS2 => ?_
  have hesp : e.sp.toNat = e.sp.toNat := rfl
  have h32 : (e.sp - 32#64).toNat = e.sp.toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
  have hS2sp : S2.sp = e.sp - 32#64 := by rw [hS2] <;> rfl
  have hS2spn : S2.sp.toNat = e.sp.toNat - 32 := by rw [hS2sp]; exact h32
  have hS2f : MemFrame e.mem S2.mem [(e.sp.toNat - 40, e.sp.toNat)] := by rw [hS2]; janus_frame
  have hcap2t' : S.mem.readLE (s.sp.toNat - 64 + 8) 8 = e2t.toNat := by
    rw [show s.sp.toNat - 64 + 8 = s.sp.toNat - 56 by omega]; exact hcap2t
  have hcap2d' : S.mem.readLE (s.sp.toNat - 64 + 16) 8 = e2d.toNat := by
    rw [show s.sp.toNat - 64 + 16 = s.sp.toNat - 48 by omega]; exact hcap2d
  have hS20 : S2.regs 0 = e2t := by rw [hS2]; simp [setReg, hcap2t']
  have hS21 : S2.regs 1 = e2d := by rw [hS2]; simp [setReg, hcap2d']
  have hS228 : S2.regs 28 = s.regs 28 := by rw [hS2]; simp [setReg]; exact hS28'
  have hS218 : S2.regs 18 = s.regs 18 := by rw [hS2]; simp [setReg]; exact hS18'
  have hS230 : S2.regs 30 = BitVec.ofNat 64 loc_NestedPanic_func2_32 := by rw [hS2] <;> rfl
  have hS2pc : S2.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by rw [hS2] <;> rfl
  have hgS2 : gOf S2 = gOf s := by simp only [gOf, hS228]
  have hS2fW : MemFrame s.mem S2.mem (P.priv ++ [(s.sp.toNat - (P.depth + (P.depth + 128)), s.sp.toNat + 48)]) :=
    hW_e.trans hS2f fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      omega⟩
  have hagE : Map.Agrees e.mem S2.mem P.priv :=
    Map.Agrees.of_window (lo := e.sp.toNat - 40) (hi := e.sp.toNat) hS2f
      (Outside.of_sub hout (by omega) (by omega))
  obtain ⟨fi2, hfi2⟩ : ∃ fi : FuncInfo, fi = FuncInfo.named Extracted.funcs "example.com/basic.NestedPanic.func2" := ⟨_, rfl⟩
  have f2_frame : fi2.frame = 32 := by rw [hfi2]; rfl
  have f2_od : fi2.openDefer = none := by rw [hfi2]; rfl
  have f2_res : fi2.resume = func2A := by rw [hfi2]; rfl
  have hdE : P.defers e.mem (gOf s) = P.defers s.mem (gOf s) := by
    have := hd1; rw [hS28] at this; simp only [gOf] at this ⊢; exact this.trans hdsS
  have hdS2 : P.defers S2.mem (gOf S2) = P.defers s.mem (gOf s) := by
    rw [hgS2, hl.defers_frame _ _ _ hagE, hdE]
  have hds2 : ∀ d ∈ P.defers S2.mem (gOf S2), S2.sp.toNat < d.sp := by
    intro d hd; rw [hdS2] at hd; have := hds d hd; omega
  have hF2 : frameOf fi2 S2.sp.toNat S2.mem = ⟨e.sp.toNat - 32, e.sp.toNat, func2A, none⟩ := by
    simp only [frameOf, FuncInfo.bound, f2_frame, f2_od, hS2spn, Option.map_none, f2_res]
    have e3 : e.sp.toNat - 32 + 32 = e.sp.toNat := by omega
    rw [e3]
  have hri2 : recItems (e.sp.toNat - 32) (P.defers S2.mem (gOf S2)) = [] :=
    recItems_above (by rw [← hS2spn]; exact hds2)
  have hI2 : frameItems S2.mem (frameOf fi2 S2.sp.toNat S2.mem) (P.defers S2.mem (gOf S2)) = [] := by
    rw [hF2]; simp only [frameItems, List.nil_append, hri2]
  have hrmS : P.room S.mem (gOf S) = P.room s.mem (gOf s) := by rw [hgS, hl.room_frame _ _ _ hagS]
  have hrmE : P.room s.mem (gOf s) ≤ P.room e.mem (gOf s) + 1 := by
    have := hrm1; rw [hS28] at this; simp only [gOf] at this ⊢; rw [hrmS] at this; simp only [gOf] at this; omega
  have hroomS2 : P.room S2.mem (gOf S2) = P.room e.mem (gOf s) := by
    rw [hgS2, hl.room_frame _ _ _ hagE]
  refine GopanicContract.apply (fi := fi2) hpan hS2pc (by rw [hS230, hfi2]; rfl) ?_ ?_
  · refine ⟨PanicPre.of_within hc hS2fW (hl.env_frame _ _ henv1 hagE) (by omega) (by omega)
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
  have hS2f' : MemFrame e.mem S2.mem (P.priv ++ [(e.sp.toNat - 32 - P.depth, e.sp.toNat)]) :=
    hS2f.mono fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      omega
  have hWd : MemFrame e.mem d.mem (P.priv ++ [(e.sp.toNat - 32 - P.depth, e.sp.toNat)]) :=
    hS2f'.trans hdfr fun a n h => ⟨h, by
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega⟩⟩
  have hU' : U d (S.regs 28).toNat e.sp.toNat := by
    rw [hS28g, ← hS2g]; exact hU
  have hAg : Map.Agrees e.mem d.mem
      [(e.sp.toNat, s.sp.toNat - 96), (s.sp.toNat - 65, s.sp.toNat - 65 + 1),
        (s.sp.toNat - 16, s.sp.toNat - 16 + 8), (s.sp.toNat - 24, s.sp.toNat - 24 + 8),
        (s.sp.toNat - 64, s.sp.toNat - 64 + 8), (s.sp.toNat - 40, s.sp.toNat - 40 + 8)] := by
    refine Map.Agrees.of_memFrame hWd fun a ⟨r, hr, h1, h2⟩ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [outside_append, outside_cons, outside_nil, and_true]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at h1 h2 <;>
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩
  have hdef' : P.defers d.mem (S.regs 28).toNat = P.defers e.mem (S.regs 28).toNat := by
    rw [hS28g, ← hS2g, hdd, (frameRecs_above (sp := e.sp.toNat - 32) (by rw [← hS2spn]; exact hds2)).2, hdS2]
    rw [hS2g, hdE]
  have hsv' : P.saved d.mem (S.regs 28).toNat = P.saved e.mem (S.regs 28).toNat := by
    rw [hS28g, ← hS2g, hdsv, hS2g, ← hgS2, hl.saved_frame _ _ _ hagE]
  have hpnS : P.panics S.mem (gOf S) = P.panics s.mem (gOf s) := by rw [hgS, hl.panics_frame _ _ _ hagS]
  have hpnS2 : P.panics S2.mem (gOf S2) = { arg := ⟨e1t.toNat, e1d.toNat⟩, start := s.sp.toNat - 96 } :: P.panics s.mem (gOf s) := by
    rw [hgS2, hl.panics_frame _ _ _ hagE]; exact hpn_e
  have hpn' : P.panics d.mem (S.regs 28).toNat =
      { arg := ⟨e2t.toNat, e2d.toNat⟩, start := e.sp.toNat - 32 } ::
      { arg := ⟨(S.regs 0).toNat, (S.regs 1).toNat⟩, start := S.sp.toNat } :: P.panics S.mem (gOf S) := by
    rw [hS28g, ← hS2g, hpd, hpnS2, hpnS, hS0, hS1, hSsp, hS20, hS21, hS2spn]
  have hrm' : P.room S.mem (gOf S) - 1 ≤ P.room d.mem (S.regs 28).toNat + 1 := by
    have a1 : P.room S.mem (gOf S) - 1 ≤ P.room e.mem (gOf s) := by have := hrm1; rwa [hS28g] at this
    have a2 : P.room S2.mem (gOf S2) - 1 ≤ P.room d.mem (gOf s) := by have := hdrm; rwa [hS2g] at this
    rw [hS28g]; omega
  have hE' := hnest1 rfl d { arg := ⟨e2t.toNat, e2d.toNat⟩, start := e.sp.toNat - 32 } hU' hAg hdenv hdef' hsv' hpn' rfl rfl
    (show e.sp.toNat - 32 ≤ e.sp.toNat by omega) hrm'
  rw [Engine_cons] at hE'
  obtain ⟨k3, e3, hst3, ⟨hpc3, h26_3, h28_3, h18_3, h29_3, hal3, hlo3, hhi3, h30a3, h30b3, henvE3⟩,
    hfrE3, -, -, hpn3, -, -, hcont3, -⟩ := hE'
  dsimp only at hpc3 h26_3 hlo3 hhi3 hfrE3 hcont3
  refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
  -- facts about the memory at the third state, relative to the entry memory
  have hread : ∀ a n, Outside a n P.priv → s.sp.toNat - 40 ≤ a → a + n ≤ s.sp.toNat - 24 →
      e3.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    rw [hfrE3.readLE _ _ (by
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨h1, by omega⟩, by omega⟩),
      hWd.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h1, by omega⟩),
      hwd' a n h1 (by omega) (by omega)]
  have hm3 : e3.mem.readLE (s.sp.toNat - 40) 8 = func1A := by
    rw [hread _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hfv1
  have hc3 : e3.mem.readLE (s.sp.toNat - 40 + 8) 8 = p.toNat := by
    rw [hread _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega),
      show s.sp.toNat - 40 + 8 = s.sp.toNat - 32 by omega]; exact hcap1
  have hv3 : e3.mem.readLE p.toNat 8 = S.mem.readLE p.toNat 8 := by
    rw [hfrE3.readLE _ _ (by
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hpo, by omega⟩, by omega⟩),
      hWd.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpo, by omega⟩), hwd' _ _ hpo (by omega) (by omega)]
  have hpa3 : e3.mem.accessible p.toNat 8 true = true := by
    rw [hfrE3.accessible, hWd.accessible, hfr1'.accessible, hSf.accessible]; exact hp
  rw [hm3] at hpc3
  clear hread hwd hwd' hAg hdef' hsv' hpn' hrm' hU' hnest1 hcont1
  have hcl3 : ReachesRet (Extracted.program.link impl) (e3.regs 30) e3 (fun e' =>
      e'.pc = e3.regs 30 ∧ e'.sp = e3.sp ∧ e'.regs 28 = e3.regs 28 ∧ e'.regs 18 = e3.regs 18 ∧
      MemFrame e3.mem e'.mem [(p.toNat, p.toNat + 8)] ∧ e'.mem.readLE p.toNat 8 = 1) := by
    janus_run [hc3]
    janus_frame
  obtain ⟨j3, f3, hj3, -, hfpc3, hfsp3, hf283, hf183, hff3, hpv3⟩ := hcl3
  refine GoReturns.of_steps (hj3.withExit hret.fetch_none) ?_
  obtain ⟨hdr3, hpf3⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 96)
    (keep := [(s.sp.toNat - 65, s.sp.toNat - 65 + 1), (s.sp.toNat - 16, s.sp.toNat - 16 + 8),
      (s.sp.toNat - 24, s.sp.toNat - 24 + 8), (s.sp.toNat - 64, s.sp.toNat - 64 + 8),
      (s.sp.toNat - 40, s.sp.toNat - 40 + 8)]) hl hfpc3 hfsp3 (hf283.trans h28_3) (hf183.trans h18_3)
    henvE3 hff3 (by
      simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpo, by omega, by omega, by omega, by omega, by omega, by omega⟩)
  have hE3 := (hcont3 f3 hdr3).1 (hpf3.trans hpn3)
  rw [Engine_nil] at hE3
  obtain ⟨k4, d4, hst4, hU4, hpd4, -, hfrd4, -, -, -⟩ := hE3
  refine GoReturns.leave (v := ⟨e2t.toNat, e2d.toNat⟩) (hst4.withExit hret.fetch_none) ?_ ?_
  · have hg' : gOf s = (S.regs 28).toNat := by simp only [gOf, hS28]
    have hU5 := hU4; have hp5 := hpd4
    rw [← hg'] at hU5 hp5
    exact ⟨hU5, _, _, hp5, rfl, rfl⟩
  · show _ = _ ∧ _
    refine ⟨rfl, ?_⟩
    rw [hfrd4.readLE _ _ (by
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hpo, by omega⟩, by omega⟩)]
    exact hpv3

/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSat` (code that
`Janus.Contracts.PanicSatRun` proves meets the `gopanic` contract in every program that contains
it) linked into `NestedPanic`'s program with a branch to it at the `runtime.gopanic` address, and a
call state in the precondition; the call panics (with `e2`). -/

namespace Witness

open Janus.Contracts.PanicSat Janus.Contracts.PanicModel

abbrev T0 : List FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : PanicRuntime := P0 T0 RPa

def gA : Nat := Extracted.program.contractAddr "runtime.gopanic"

/-- The code linked next to `NestedPanic`: the model engine and the branch to it at `runtime.gopanic`. -/
def implW : List Segment := panicImpl Extracted.program [("runtime.gopanic", eGopanic)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

theorem stubAt : StubAt (Extracted.program.link implW) gA eGopanic :=
  StubAt.of_decode (w := stubWord gA eGopanic) (imm := (eGopanic - gA) / 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem hpan : GopanicContract (Extracted.program.link implW) gA PW U0 T0 :=
  gopanic_at stubAt (gopanic_run engineAt T0 tok)

def wmW : Memory := witMem (tabWords T0)

abbrev pA : Nat := witArg
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
      else if i = 29 then BitVec.ofNat 64 (wsp - 8) else if i = 0 then BitVec.ofNat 64 pA
      else if i = 1 then 1#64 else if i = 3 then 2#64 else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmW }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [BitVec.ofNat 64 pA, 1#64, 0#64, 2#64, 0#64] s0 := by
  refine ⟨rfl, rfl, fun i h => ?_⟩
  simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
theorem pre : PanicCallerOK PW s0 (PW.depth + 128) 48 ∧ Ptr s0.mem (BitVec.ofNat 64 pA) 8 true ∧
    Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 (s0.sp.toNat - (PW.depth + (PW.depth + 128)))
      (PW.depth + (PW.depth + 128) + 48) ∧
    Outside (BitVec.ofNat 64 pA).toNat 8 PW.priv ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧ (2#64 : BitVec 64).toNat ≠ 0 ∧
    2 ≤ PW.room s0.mem (gOf s0) ∧ ∀ d ∈ PW.defers s0.mem (gOf s0), s0.sp.toNat ≤ d.sp := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_⟩, ⟨by decide, by decide⟩, ?_, ?_, by decide, by decide, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
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
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry
      [BitVec.ofNat 64 pA, 1#64, 0#64, 2#64, 0#64] s ∧
    (PanicCallerOK P s (P.depth + 128) 48 ∧ Ptr s.mem (BitVec.ofNat 64 pA) 8 true ∧
      Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 (s.sp.toNat - (P.depth + (P.depth + 128)))
        (P.depth + (P.depth + 128) + 48) ∧
      Outside (BitVec.ofNat 64 pA).toNat 8 P.priv ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧ (2#64 : BitVec 64).toNat ≠ 0 ∧
      2 ≤ P.room s.mem (gOf s) ∧ ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp) :=
  ⟨implW, PW, U0, ret, s0, P0_laws T0 RPa, hpan, hret, setup, pre⟩

/-- So the guarantee is reached: `NestedPanic` panics with `e2` (type word `2`), having run the
remaining deferred call (`*p = 1`). -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClassU PW U0 s0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ False
    | .panicked v s' => v = ⟨(2#64 : BitVec 64).toNat, (0#64 : BitVec 64).toNat⟩ ∧
        s'.mem.readLE (BitVec.ofNat 64 pA).toNat 8 = 1
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U0 hpan (BitVec.ofNat 64 pA) 1#64 0#64 2#64 0#64 ret hret s0 setup pre

end Witness

end Proof
