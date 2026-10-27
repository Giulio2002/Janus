import Janus
import Extracted

/-!
# `NestedPanic(p *uint64, e1, e2 any)`: a deferred call panics while a panic unwinds (amd64)

`NestedPanic` is `defer func() { *p = 1 }(); defer func() { panic(e2) }(); panic(e1)` (two
open-coded defers). `panic(e1)` runs the second deferred call, which panics with `e2` while `e1`
is unwinding: the new `runtime.gopanic` pushes its `_panic`, aborts `e1`'s and carries on with the
same walk of the frame's deferred calls, so the remaining call (`*p = 1`) runs and the frame is
left with `e2`'s panic on top of the aborted `e1`'s.

**Guarantee (example 8 of docs/COVERAGE.md R6).** For every panic-runtime model `P` satisfying its
laws, every implementation of `runtime.gopanic` meeting its contract (`Janus.Contracts.PanicAmd64`,
pinned to the Go 1.26 runtime's code; the contract is used twice, for the outer and the nested
panic), every admissible return address and every call state in which the runtime is usable with
stack for the frame and the nested panic's runtime window below it, `p` points to a writable word
outside the runtime's memory and the stack window, both `any`s are non-nil and the runtime has room
for two `_panic` records: the call **panics with `e2`**, never returns, and `*p = 1`.
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64
open Janus.Contracts.Panic (frameItems openItems frameKeep bitsWin recItems recItems_above Frame frameRecs_above)
open Janus.Spec (openBits)

local macro "func1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedPanic.func1"))
local macro "func2A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.NestedPanic.func2"))

set_option maxHeartbeats 0 in
/-- The deferred closure `NestedPanic.func1` (a leaf `RET`): `*p = 1`. -/
theorem cl1 (impl : List Janus.Amd64.Segment) (e : State) (p : BitVec 64) (a : Nat)
    (hpe : e.rip = BitVec.ofNat 64 func1A) (hrdx : e.regs 2 = BitVec.ofNat 64 a) (ha : a + 8 < 2 ^ 64)
    (hcap : e.mem.readLE (a + 8) 8 = p.toNat)
    (haa : e.mem.accessible (a + 8) 8 false = true) (hpa : e.mem.accessible p.toNat 8 true = true)
    (hra : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 47)
    (hdj : p.toNat + 8 ≤ (e.regs 4).toNat ∨ (e.regs 4).toNat + 8 ≤ p.toNat)
    (hrac : e.mem.accessible (e.regs 4).toNat 8 false = true) :
    ReachesRet (Extracted.program.link impl) (retAddrOf e) e (fun e' =>
      e'.rip = retAddrOf e ∧ e'.regs 4 = e.regs 4 + 8 ∧ e'.regs 14 = e.regs 14 ∧ e'.regs 5 = e.regs 5 ∧
      e'.xmm 15 = e.xmm 15 ∧ e'.df = e.df ∧ MemFrame e.mem e'.mem [(p.toNat, p.toNat + 8)] ∧
      e'.mem.readLE p.toNat 8 = 1) := by
  have hpn : p.toNat % 2 ^ 64 = p.toNat := Nat.mod_eq_of_lt p.isLt
  have hpa' : e.mem.accessible p.toNat 8 false = true := Janus.Arm64.Memory.accessible_weaken _ hpa
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpe
  have hcr : cr = setRegF cr 2 (BitVec.ofNat 64 a) := by
    funext i; simp only [setRegF]; split
    · subst_vars; exact hrdx
    · rfl
  rw [hcr]
  janus64_run [hcap, hpn]
  exact MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 0 in
/-- The deferred closure `NestedPanic.func2` up to its call of `runtime.gopanic`: `panic(e2)`. -/
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
set_option maxRecDepth 20000 in
theorem correctness (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hpan : GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs)
    (p e1t e1d e2t e2d : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [p, e1t, e1d, e2t, e2d]
      (fun s => PanicCallerOK P s (P.depth + 120) 48 ∧ Buffer s p 8 true ∧
        Spec.Disjoint p.toNat 8 ((s.regs regSP).toNat - (P.depth + (P.depth + 120)))
          (P.depth + (P.depth + 120) + 48) ∧
        Outside p.toNat 8 P.priv ∧ e1t.toNat ≠ 0 ∧ e2t.toNat ≠ 0 ∧ 2 ≤ P.room s.mem (gOf s) ∧
        ∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp)
      (goClassU P U)
      (fun _ _ => False)
      (fun s v s' => v = ⟨e2t.toNat, e2d.toNat⟩ ∧ s'.mem.readLE p.toNat 8 = 1) := by
  intro ret hret s hs ⟨hc, ⟨hpb, hps⟩, hdj, hpo, hne1, hne2, hroom, hds⟩
  have hc' := hc
  obtain ⟨henv, hg, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd hb hal hds hdj
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
    hret.fetch_none ?_
  janus64_run until [Extracted.program.contractAddr "runtime.gopanic"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun S hS => ?_
  have h96 : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hSsp : S.regs 4 = s.regs 4 - 96#64 := by rw [hS] <;> simp [setRegF]
  have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hSsp]; exact h96
  have hSpc : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by rw [hS] <;> rfl
  have hS0 : S.regs 0 = e1t := by rw [hS] <;> simp [setRegF]
  have hS3 : S.regs 3 = e1d := by rw [hS] <;> simp [setRegF]
  have hS14 : S.regs 14 = s.regs 14 := by rw [hS] <;> simp [setRegF]
  have hSx : S.xmm 15 = 0 := by rw [hS]; exact h_x15
  have hSdf : S.df = false := by rw [hS]
  have hSf : MemFrame s.mem S.mem [((s.regs 4).toNat - (P.depth + (P.depth + 120)), (s.regs 4).toNat + 48)] := by
    rw [hS]; janus_frame
  have hSra : S.mem.readLE (S.regs 4).toNat 8 = 4747237 := by
    rw [hS]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h96, Janus.Arm64.Memory.readLE_writeLE_self]
  have hbits : S.mem.readLE ((s.regs 4).toNat - 65) 1 = 3 := by
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
  have hcap1 : S.mem.readLE ((s.regs 4).toNat - 32) 8 = p.toNat := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := p.isLt; omega)
  have hcap2t : S.mem.readLE ((s.regs 4).toNat - 56) 8 = e2t.toNat := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := e2t.isLt; omega)
  have hcap2d : S.mem.readLE ((s.regs 4).toNat - 48) 8 = e2d.toNat := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := e2d.isLt; omega)
  clear hS
  obtain ⟨fi, hfi⟩ : ∃ fi : Spec.FuncInfo, fi = Spec.FuncInfo.named Extracted.funcs "example.com/basic.NestedPanic" :=
    ⟨_, rfl⟩
  have f_frame : fi.frame = 88 := by rw [hfi]; rfl
  have f_od : fi.openDefer = some (57, 16) := by rw [hfi]; rfl
  have f_res : fi.resume = Extracted.entry + 0x86 := by rw [hfi]; rfl
  have hagS : Spec.Map.Agrees s.mem S.mem P.priv :=
    Spec.Map.Agrees.of_window hSf (Outside.of_sub hout (by omega) (by omega))
  have hgS : gOf S = gOf s := by simp only [gOf, hS14]
  have hdsS : P.defers S.mem (gOf S) = P.defers s.mem (gOf s) := by
    rw [hgS]; exact hl.defers_frame _ _ _ hagS
  have hfsp : fspOf S = (s.regs 4).toNat - 88 := by simp only [fspOf, hSspn]; omega
  have hdsS' : ∀ d ∈ P.defers S.mem (gOf S), (S.regs 4).toNat + 8 < d.sp := by
    intro d hd; rw [hdsS] at hd; have := hds d hd; omega
  have hri : recItems ((s.regs 4).toNat - 88) (P.defers S.mem (gOf S)) = [] :=
    recItems_above (by rw [← hfsp]; exact hdsS')
  have hF : frameOf fi (fspOf S) S.mem =
      ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat, Extracted.entry + 0x86,
        some ((s.regs 4).toNat - 65, (s.regs 4).toNat - 24)⟩ := by
    simp only [frameOf, Panic.frameOf, Spec.FuncInfo.bound, Spec.FuncInfo.bitsAt, Spec.FuncInfo.slotsAt,
      Spec.FuncInfo.varp, f_frame, f_od, hfsp, Option.map_some, Option.getD_some, f_res]
    have e1 : (s.regs 4).toNat - 88 + 88 - 8 - 57 = (s.regs 4).toNat - 65 := by omega
    have e2 : (s.regs 4).toNat - 88 + 88 - 8 - 16 = (s.regs 4).toNat - 24 := by omega
    have e3 : (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat := by omega
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
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 120)), (s.regs 4).toNat + 48)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  refine GopanicContract.apply (fi := fi) hpan hSpc (by rw [hSra, hfi]; rfl) ?_ ?_
  · refine ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
        (by rw [hSspn]; omega) hS14 hSx hSdf (by rw [hSra]; decide),
      by rw [hS0]; exact hne1, ?_, ?_, ?_⟩
    · rw [hgS, hl.room_frame _ _ _ hagS]; omega
    · intro _
      have e : fi.bitsAt (fspOf S) = (s.regs 4).toNat - 65 := by
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
      [((s.regs 4).toNat - 65, (s.regs 4).toNat - 65 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8),
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
      (P.priv ++ [((s.regs 4).toNat - 88 - P.depth, (s.regs 4).toNat - 96), ((s.regs 4).toNat - 65, (s.regs 4).toNat - 65 + 1)]) := by
    refine hfr1.mono fun a n h => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true, rtWin, bitsWin] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, by omega⟩, by omega⟩
  have hW_e : MemFrame s.mem e.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 120)), (s.regs 4).toNat + 48)]) :=
    hSfW.trans hfr1' fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hwd' : ∀ a n, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - 88 - P.depth ∨ (s.regs 4).toNat - 96 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 65 ∨ (s.regs 4).toNat - 64 ≤ a) → e.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    rw [hfr1'.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h1, by omega, by omega⟩)]
  have hwd : ∀ a, Outside a 8 P.priv → (a + 8 ≤ (s.regs 4).toNat - 88 - P.depth ∨ (s.regs 4).toNat - 96 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 65 ∨ (s.regs 4).toNat - 64 ≤ a) → e.mem.readLE a 8 = S.mem.readLE a 8 :=
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
  have hwin : e.mem.accessible ((s.regs 4).toNat - (P.depth + (P.depth + 120)))
      (P.depth + (P.depth + 120) + 48) true = true := by
    rw [hW_e.accessible]; exact hst
  have hpn_e : P.panics e.mem (gOf s) =
      { arg := ⟨e1t.toNat, e1d.toNat⟩, start := (s.regs 4).toNat - 88 } :: P.panics s.mem (gOf s) := by
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
      (P.priv ++ [((s.regs 4).toNat - (P.depth + (P.depth + 120)), (s.regs 4).toNat + 48)]) :=
    hW_e.trans hS2f fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      omega⟩
  have hagE : Spec.Map.Agrees e.mem S2.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (e.regs 4).toNat - 32) (hi := (e.regs 4).toNat) hS2f
      (Outside.of_sub hout (by omega) (by omega))
  obtain ⟨fi2, hfi2⟩ : ∃ fi : Spec.FuncInfo, fi = Spec.FuncInfo.named Extracted.funcs
      "example.com/basic.NestedPanic.func2" := ⟨_, rfl⟩
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
      [((e.regs 4).toNat, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 65, (s.regs 4).toNat - 65 + 1),
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
      { arg := ⟨e1t.toNat, e1d.toNat⟩, start := (s.regs 4).toNat - 88 } :: P.panics s.mem (gOf s) := by
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
    hfrE3, -, -, hpn3, -, -, hcont3, -⟩ := hE'
  dsimp only at hpc3 h2_3 hlo3 hhi3 hra3 hfrE3 hcont3
  refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
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
  have hm3 : e3.mem.readLE ((s.regs 4).toNat - 40) 8 = func1A := by
    rw [hread _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hfv1
  have hc3 : e3.mem.readLE ((s.regs 4).toNat - 40 + 8) 8 = p.toNat := by
    rw [hread _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega),
      show (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 by omega]; exact hcap1
  have hpa3 : e3.mem.accessible p.toNat 8 true = true := by
    rw [hfrE3.accessible, hWd.accessible, hW_e.accessible]; exact hps
  have haa3 : e3.mem.accessible ((s.regs 4).toNat - 40 + 8) 8 false = true := by
    rw [hfrE3.accessible, hWd.accessible, hW_e.accessible]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
  have hrac3 : e3.mem.accessible (e3.regs 4).toNat 8 false = true := by
    rw [hfrE3.accessible, hWd.accessible, hW_e.accessible]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
  rw [hm3] at hpc3
  clear hread hwd hwd' hdef' hsv' hpn' hrm' hU' hnest1 hcont1
  have hcl3 := cl1 impl e3 p ((s.regs 4).toNat - 40) hpc3 (by rw [h2_3]) (by omega) hc3 haa3 hpa3 hra3
    (by omega) hrac3
  obtain ⟨j3, f3, hj3, -, hfpc3, hfsp3, hf143, hf53, hfx3, hfdf3, hff3, hpv3⟩ := hcl3
  refine GoReturns.of_steps (hj3.withExit hret.fetch_none) ?_
  obtain ⟨hdr3, hpf3⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 88)
    (keep := [((s.regs 4).toNat - 65, (s.regs 4).toNat - 65 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8),
      ((s.regs 4).toNat - 24, (s.regs 4).toNat - 24 + 8), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 64 + 8),
      ((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 8)]) hl
    (by rw [hfpc3, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
    hfsp3 (hf143.trans h14_3) hf53 (by rw [hfx3]; exact hx3) (by rw [hfdf3]; exact hdf3)
    henvE3 hff3 (by
      simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpo, by omega, by omega, by omega, by omega, by omega, by omega⟩)
  have hE3 := (hcont3 f3 hdr3).1 (hpf3.trans hpn3)
  rw [Engine_nil] at hE3
  obtain ⟨k4, d4, hst4, hU4, hpd4, -, hfrd4, -, -, -⟩ := hE3
  refine GoReturns.leave (v := ⟨e2t.toNat, e2d.toNat⟩) (hst4.withExit hret.fetch_none) ?_ ?_
  · have hg' : gOf s = (S.regs 14).toNat := by simp only [gOf, hS14]
    have hU5 := hU4; have hp5 := hpd4
    rw [← hg'] at hU5 hp5
    exact ⟨hU5, _, _, hp5, rfl, rfl⟩
  · refine ⟨rfl, ?_⟩
    rw [hfrd4.readLE _ _ (by
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hpo, by omega⟩, by omega⟩)]
    exact hpv3

namespace Witness

open Janus.Contracts.PanicSat (tabWords witMem)
open Janus.Contracts.PanicSatAmd64
open Janus.Contracts.PanicModel

abbrev T0 : List Spec.FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : Spec.PanicRuntime := P0 T0 RPa

def gA : Nat := Extracted.program.contractAddr "runtime.gopanic"

/-- The code linked next to `NestedPanic`: the model engine and a `jmp` to it at `runtime.gopanic`. -/
def implW : List Janus.Amd64.Segment := panicImpl Extracted.program [("runtime.gopanic", eGopanic)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

set_option maxRecDepth 100000 in
theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubAt : StubAt (Extracted.program.link implW) gA eGopanic :=
  StubAt.of_jmp (bs := stubCode gA eGopanic) (rel := (eGopanic + 2 ^ 64 - (gA + 5)) % 2 ^ 64) (len := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem hpan : GopanicContract (Extracted.program.link implW) gA PW U1 T0 :=
  gopanic_at stubAt (gopanic_run engineAt T0 tok)

def pA : Nat := 0x41000
def ret : Nat := 0x200000

/-- Memory: the model's table and runtime range writable, a stack `[0x40000, 0x50000)` holding the
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
      else if i = 0 then BitVec.ofNat 64 pA else if i = 3 then 1#64 else if i = 7 then 2#64 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmW }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [BitVec.ofNat 64 pA, 1#64, 0#64, 2#64, 0#64] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, fun i h => ?_, rfl⟩
  simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem pre : PanicCallerOK PW s0 (PW.depth + 120) 48 ∧ Buffer s0 (BitVec.ofNat 64 pA) 8 true ∧
    Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 ((s0.regs regSP).toNat - (PW.depth + (PW.depth + 120))) (PW.depth + (PW.depth + 120) + 48) ∧
    Outside (BitVec.ofNat 64 pA).toNat 8 PW.priv ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧ (2#64 : BitVec 64).toNat ≠ 0 ∧
    2 ≤ PW.room s0.mem (gOf s0) ∧ ∀ d ∈ PW.defers s0.mem (gOf s0), (s0.regs regSP).toNat ≤ d.sp := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩,
    ⟨by decide, by decide⟩, ?_, ?_, by decide, by decide, ?_, ?_⟩
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
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime)
    (U : Janus.Amd64.State → Nat → Nat → Prop) (ret : Nat) (s : Janus.Amd64.State), P.Laws ∧
    GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry
      [BitVec.ofNat 64 pA, 1#64, 0#64, 2#64, 0#64] s ∧
    (PanicCallerOK P s (P.depth + 120) 48 ∧ Buffer s (BitVec.ofNat 64 pA) 8 true ∧
      Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 ((s.regs regSP).toNat - (P.depth + (P.depth + 120))) (P.depth + (P.depth + 120) + 48) ∧
      Outside (BitVec.ofNat 64 pA).toNat 8 P.priv ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧ (2#64 : BitVec 64).toNat ≠ 0 ∧
      2 ≤ P.room s.mem (gOf s) ∧ ∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp) :=
  ⟨implW, PW, U1, ret, s0, P0_laws T0 RPa, hpan, hret, setup, pre⟩

/-- So the guarantee is reached: `NestedPanic` panics with `e2` (type word `2`), having run the
remaining deferred call (`*p = 1`). -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClassU PW U1 s0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ False
    | .panicked v s' => v = ⟨(2#64 : BitVec 64).toNat, (0#64 : BitVec 64).toNat⟩ ∧
        s'.mem.readLE (BitVec.ofNat 64 pA).toNat 8 = 1
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U1 hpan (BitVec.ofNat 64 pA) 1#64 0#64 2#64 0#64 ret hret s0 setup pre

end Witness

end Proof
