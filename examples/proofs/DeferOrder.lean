import Extracted

/-!
# `DeferOrder(p *uint64, x uint64, e any) uint64`: three open-coded defers run in LIFO order (arm64)

`DeferOrder` defers `*p = *p*10+1`, `*p = *p*10+2`, `*p = *p*10+3` (open-coded: `deferBits` bits
0, 1, 2), then returns `x` if `x ≤ 10` and panics with `e` otherwise.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Proof

/-- `DeferOrder`'s metadata, as the extractor read it from the binary. -/
def fi : FuncInfo := FuncInfo.named Extracted.funcs "example.com/basic.DeferOrder"

local macro "func1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferOrder.func1"))
local macro "func2A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferOrder.func2"))
local macro "func3A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferOrder.func3"))

/-- `DeferOrder`'s frame as the panic runtime finds it, for the call state `s`: `SP = s.sp - 128`,
the `deferBits` byte at `s.sp - 89`, the slots from `s.sp - 32`. -/
def frame0 (s : State) : Frame :=
  ⟨s.sp.toNat - 128, s.sp.toNat, Extracted.entry + 0xe0, some (s.sp.toNat - 89, s.sp.toNat - 32)⟩

/-- The memory the runtime reads again between the deferred calls (`frameKeep`). -/
def keep0 (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 89, s.sp.toNat - 89 + 1), (s.sp.toNat - 16, s.sp.toNat - 8),
   (s.sp.toNat - 24, s.sp.toNat - 16), (s.sp.toNat - 32, s.sp.toNat - 24),
   (s.sp.toNat - 80, s.sp.toNat - 72), (s.sp.toNat - 64, s.sp.toNat - 56),
   (s.sp.toNat - 48, s.sp.toNat - 40)]

/-- What the runtime and the deferred calls write during the panic: `P.priv`, the runtime's
window below the frame, the `deferBits` byte and `*p`. -/
def win0 (P : PanicRuntime) (s : State) (p : BitVec 64) : List (Nat × Nat) :=
  P.priv ++ [(s.sp.toNat - 128 - P.depth, s.sp.toNat - 128 - 8),
    (s.sp.toNat - 89, s.sp.toNat - 89 + 1), (p.toNat, p.toNat + 8)]

/-- One deferred call: append the decimal digit `k` (mod `2^64`). -/
def digit (k v : Nat) : Nat := (v * 10 + k) % 2 ^ 64

/-- The three deferred calls in LIFO order. -/
def order (v : Nat) : Nat := digit 1 (digit 2 (digit 3 v))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hpan : GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs)
    (p x etyp edata : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [p, x, etyp, edata]
      (fun s => PanicCallerOK P s 128 40 ∧ Ptr s.mem p 8 true ∧
        Spec.Disjoint p.toNat 8 (s.sp.toNat - (P.depth + 128)) (P.depth + 128 + 40) ∧
        Outside p.toNat 8 P.priv ∧ etyp.toNat ≠ 0 ∧ 0 < P.room s.mem (gOf s) ∧
        ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp)
      (goClassU P U)
      (fun s s' => x.toNat ≤ 10 ∧ (s'.regs 0).toNat = x.toNat ∧
        s'.mem.readLE p.toNat 8 = order (s.mem.readLE p.toNat 8))
      (fun s v s' => 10 < x.toNat ∧ v = ⟨etyp.toNat, edata.toNat⟩ ∧
        s'.mem.readLE p.toNat 8 = order (s.mem.readLE p.toNat 8)) := by
  intro ret hret s hs ⟨hc, ⟨hp, hp'⟩, hdj, hpo, hne, hroom, hds⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd hdj
  by_cases hx : x.toNat ≤ 10
  · refine GoReturns.of_reaches ?_
    janus_run
    refine ⟨hx, ?_⟩
    simp only [order, digit]
    generalize s.mem.readLE p.toNat 8 = v
    omega
  · have hx' : 10 < x.toNat := by omega
    refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
      hret.fetch_none ?_
    janus_run until [Extracted.program.contractAddr "runtime.gopanic"]
    refine ReachesRet.done rfl ?_
    refine GoReturns.name fun S hS => ?_
    have hSpc : S.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by
      rw [hS]; rfl
    have hS30 : S.regs 30 = BitVec.ofNat 64 (Extracted.entry + 0xdc) := by rw [hS]; rfl
    have hS0 : S.regs 0 = etyp := by rw [hS]; simp [setReg]
    have hS1 : S.regs 1 = edata := by rw [hS]; simp [setReg]
    have hS28 : S.regs 28 = s.regs 28 := by rw [hS]; simp [setReg]
    have hS18 : S.regs 18 = s.regs 18 := by rw [hS]; simp [setReg]
    have hSsp : S.sp.toNat = s.sp.toNat - 128 := by rw [hS]; simp only; rw [BitVec.toNat_sub]; simp; omega
    have hSf : MemFrame s.mem S.mem [(s.sp.toNat - (P.depth + 128), s.sp.toNat + 40)] := by
      rw [hS]; janus_frame
    have hrd : ∀ a v, S.mem.readLE a 8 = v → S.mem.readLE a 8 = v := fun _ _ h => h
    have hbits : S.mem.readLE (s.sp.toNat - 89) 1 = 7 := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    have hsl0 : S.mem.readLE (s.sp.toNat - 32) 8 = s.sp.toNat - 48 := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 omega)
    have hsl1 : S.mem.readLE (s.sp.toNat - 24) 8 = s.sp.toNat - 64 := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 omega)
    have hsl2 : S.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 80 := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 omega)
    have hfv1 : S.mem.readLE (s.sp.toNat - 48) 8 = func1A := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      try decide
    have hfv2 : S.mem.readLE (s.sp.toNat - 64) 8 = func2A := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      try decide
    have hfv3 : S.mem.readLE (s.sp.toNat - 80) 8 = func3A := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      try decide
    have hcap1 : S.mem.readLE (s.sp.toNat - 40) 8 = p.toNat := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 have := p.isLt; omega)
    have hcap2 : S.mem.readLE (s.sp.toNat - 56) 8 = p.toNat := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 have := p.isLt; omega)
    have hcap3 : S.mem.readLE (s.sp.toNat - 72) 8 = p.toNat := by
      rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                                 have := p.isLt; omega)
    clear hS
    have f_frame : fi.frame = 128 := by rfl
    have f_od : fi.openDefer = some (81, 24) := by rfl
    have f_res : fi.resume = Extracted.entry + 0xe0 := by rfl
    have hag : Map.Agrees s.mem S.mem P.priv :=
      Map.Agrees.of_window hSf (Outside.of_sub hout (by omega) (by omega))
    have hgS : gOf S = gOf s := by simp only [gOf, hS28]
    have hdsS : P.defers S.mem (gOf S) = P.defers s.mem (gOf s) := by
      rw [hgS]; exact hl.defers_frame _ _ _ hag
    have hdsS' : ∀ d ∈ P.defers S.mem (gOf S), S.sp.toNat < d.sp := by
      intro d hd; rw [hdsS] at hd; have := hds d hd; omega
    obtain ⟨-, hrest⟩ := frameRecs_above hdsS'
    rw [hSsp] at hrest
    have hri : recItems (s.sp.toNat - 128) (P.defers S.mem (gOf S)) = [] :=
      recItems_above (by rw [← hSsp]; exact hdsS')
    have hF : frameOf fi S.sp.toNat S.mem = frame0 s := by
      have e3 : s.sp.toNat - 128 + 128 = s.sp.toNat := by omega
      simp only [frameOf, FuncInfo.bound, FuncInfo.bitsAt, FuncInfo.slotsAt,
        FuncInfo.varp, f_frame, f_od, hSsp, Option.map_some, Option.getD_some, e3, f_res]
      have e1 : s.sp.toNat - 8 - 81 = s.sp.toNat - 89 := by omega
      have e2 : s.sp.toNat - 8 - 24 = s.sp.toNat - 32 := by omega
      rw [e1, e2, hbits]; rfl
    have hob : openBits 7 = [2, 1, 0] := by decide
    have hI : frameItems S.mem (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S)) =
        [{ fn := s.sp.toNat - 80, bits := some 3, chain := P.defers S.mem (gOf S) },
         { fn := s.sp.toNat - 64, bits := some 1, chain := P.defers S.mem (gOf S) },
         { fn := s.sp.toNat - 48, bits := some 0, chain := P.defers S.mem (gOf S) }] := by
      have e1 : s.sp.toNat - 32 + 8 * 2 = s.sp.toNat - 16 := by omega
      have e2 : s.sp.toNat - 32 + 8 * 1 = s.sp.toNat - 24 := by omega
      have e3 : s.sp.toNat - 32 + 8 * 0 = s.sp.toNat - 32 := by omega
      rw [hF]
      unfold frame0
      simp only [frameItems, openItems, hbits, hob, List.map_cons, List.map_nil, hri,
        List.append_nil, e1, e2, e3, hsl0, hsl1, hsl2, Nat.reducePow, Nat.reduceMod]
    refine GopanicContract.apply (fi := fi) hpan hSpc (by rw [hS30]; rfl) ?_ ?_
    · refine ⟨PanicPre.of_within hc (hSf.mono fun a n h => by
          simp only [outside_append] at h; exact h.2) (hl.env_frame _ _ henv hag) (by omega) (by omega)
          (by rw [hSsp]; omega) hS28 (by rw [hS30]; decide) (by rw [hS30]; decide),
        by rw [hS0]; exact hne, ?_, ?_, ?_⟩
      · rw [hgS, hl.room_frame _ _ _ hag]; exact hroom
      · intro _
        have e : fi.bitsAt S.sp.toNat = s.sp.toNat - 89 := by
          simp only [FuncInfo.bitsAt, FuncInfo.varp, f_frame, f_od, hSsp, Option.map_some, Option.getD_some]; omega
        rw [e]
        refine ⟨?_, Outside.of_sub hout (by omega) (by omega)⟩
        rw [hSf.accessible]
        exact Memory.accessible_weaken _ (Memory.accessible_mono _ hst (by omega) (by omega))
      · rw [hI, hF]
        unfold frame0
        refine ⟨⟨by omega, by rw [hSf.accessible]; exact Memory.accessible_mono _ hst (by omega) (by omega),
          Outside.of_sub hout (by omega) (by omega), by dsimp only; omega, ?_, ?_⟩, ?_⟩
        · rw [hbits, hob]
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl <;> refine ⟨by omega, ?_, by omega, by dsimp only; omega, Outside.of_sub hout (by omega) (by omega)⟩ <;>
            rw [hSf.accessible] <;>
            exact Janus.Contracts.IfaceModel.acc_read_of_write
              (Memory.accessible_mono _ hst (by omega) (by omega))
        · intro it hit
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
          rcases hit with rfl | rfl | rfl <;> dsimp only <;> omega
        · intro it hit
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
          rcases hit with rfl | rfl | rfl <;> dsimp only <;> refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first
            | (exact Outside.of_sub hout (by omega) (by omega))
            | omega
            | (rw [hSf.accessible]; exact Janus.Contracts.IfaceModel.acc_read_of_write
                (Memory.accessible_mono _ hst (by omega) (by omega)))
            | (simp only [hfv1, hfv2, hfv3]; try decide)
    intro hE
    have hK : frameKeep S.mem (frameOf fi S.sp.toNat S.mem)
        (frameItems S.mem (frameOf fi S.sp.toNat S.mem) (P.defers S.mem (gOf S))) =
        keep0 s := by
      have e1 : s.sp.toNat - 32 + 8 * 2 = s.sp.toNat - 16 := by omega
      have e2 : s.sp.toNat - 32 + 8 * 1 = s.sp.toNat - 24 := by omega
      have e3 : s.sp.toNat - 32 + 8 * 0 = s.sp.toNat - 32 := by omega
      have e4 : s.sp.toNat - 16 + 8 = s.sp.toNat - 8 := by omega
      have e5 : s.sp.toNat - 24 + 8 = s.sp.toNat - 16 := by omega
      have e6 : s.sp.toNat - 32 + 8 = s.sp.toNat - 24 := by omega
      have e7 : s.sp.toNat - 80 + 8 = s.sp.toNat - 72 := by omega
      have e8 : s.sp.toNat - 64 + 8 = s.sp.toNat - 56 := by omega
      have e9 : s.sp.toNat - 48 + 8 = s.sp.toNat - 40 := by omega
      rw [hI, hF]
      unfold frame0 keep0
      simp only [frameKeep, hbits, hob, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        e1, e2, e3, e4, e5, e6, e7, e8, e9]
    rw [hK, hI, hF] at hE
    unfold frame0 at hE
    -- the third deferred call (bit 2): `*p = *p*10 + 3`
    have hpa0 : S.mem.accessible p.toNat 8 true = true := by rw [hSf.accessible]; exact hp
    have hv0 : S.mem.readLE p.toNat 8 = s.mem.readLE p.toNat 8 := hSf.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)
    have hsubR : ∀ a n, Outside a n (win0 P s p) →
        Outside a n (P.priv ++ rtWin P (frame0 s) ++ bitsWin (frame0 s)) := by
      intro a n h
      unfold win0 frame0 at *
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨⟨h.1, h.2.1⟩, h.2.2.1⟩
    have hsubP : ∀ a n, Outside a n (win0 P s p) → Outside a n [(p.toNat, p.toNat + 8)] := by
      intro a n h
      unfold win0 at h
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact h.2.2.2
    have hacc0 : MemFrame S.mem S.mem (win0 P s p) := MemFrame.refl _ _
    rw [Engine_cons] at hE
    obtain ⟨k1, e1, hst1, ⟨hpc1, h26_1, h28_1, h18_1, h29_1, hal1, hlo1, hhi1, h30a1, h30b1, henv1⟩,
      hfr1, -, -, hpn1, -, -, hcont1, -⟩ := hE
    dsimp only at hpc1 h26_1 hlo1 hhi1 hfr1 hcont1
    refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
    have hae1 : MemFrame S.mem e1.mem (win0 P s p) := hacc0.trans hfr1 fun a n h => ⟨h, hsubR a n h⟩
    have hm1 : e1.mem.readLE (s.sp.toNat - 80) 8 = func3A := by
      rw [hae1.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hfv3
    have hc1 : e1.mem.readLE (s.sp.toNat - 80 + 8) 8 = p.toNat := by
      rw [show s.sp.toNat - 80 + 8 = s.sp.toNat - 72 by omega]
      rw [hae1.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hcap3
    have hv1 : e1.mem.readLE p.toNat 8 = s.mem.readLE p.toNat 8 := by
      rw [hfr1.readLE _ _ (by
        simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hpo, by omega⟩, by omega⟩)]; exact hv0
    rw [hm1] at hpc1
    have hpa1 : e1.mem.accessible p.toNat 8 true = true := by
      rw [hae1.accessible]; exact hpa0
    have hcl1 : ReachesRet (Extracted.program.link impl) (e1.regs 30) e1 (fun e' =>
        e'.pc = e1.regs 30 ∧ e'.sp = e1.sp ∧ e'.regs 28 = e1.regs 28 ∧ e'.regs 18 = e1.regs 18 ∧
        MemFrame e1.mem e'.mem [(p.toNat, p.toNat + 8)] ∧
        e'.mem.readLE p.toNat 8 = digit 3 (s.mem.readLE p.toNat 8)) := by
      janus_run
      simp only [hc1, hv1]
      refine ⟨MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega), ?_⟩
      try rw [Memory.readLE_writeLE_self]
      simp only [digit]; omega
    obtain ⟨j1, f1, hj1, -, hfpc1, hfsp1, hf281, hf181, hff1, hpv1⟩ := hcl1
    refine GoReturns.of_steps (hj1.withExit hret.fetch_none) ?_
    have hacc1 : MemFrame S.mem f1.mem (win0 P s p) := hae1.trans hff1 fun a n h => ⟨h, hsubP a n h⟩
    obtain ⟨hdr1, hpf1⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 128) (keep := keep0 s) hl hfpc1 hfsp1 (hf281.trans h28_1)
      (hf181.trans h18_1) henv1 hff1 (by
        unfold keep0; simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpo, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    have hE1 := (hcont1 f1 hdr1).1 (hpf1.trans hpn1)
    rw [Engine_cons] at hE1
    obtain ⟨k2, e2, hst2, ⟨hpc2, h26_2, h28_2, h18_2, h29_2, hal2, hlo2, hhi2, h30a2, h30b2, henv2⟩,
      hfr2, -, -, hpn2, -, -, hcont2, -⟩ := hE1
    dsimp only at hpc2 h26_2 hlo2 hhi2 hfr2 hcont2
    refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
    have hae2 : MemFrame S.mem e2.mem (win0 P s p) := hacc1.trans hfr2 fun a n h => ⟨h, hsubR a n h⟩
    have hm2 : e2.mem.readLE (s.sp.toNat - 64) 8 = func2A := by
      rw [hae2.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hfv2
    have hc2 : e2.mem.readLE (s.sp.toNat - 64 + 8) 8 = p.toNat := by
      rw [show s.sp.toNat - 64 + 8 = s.sp.toNat - 56 by omega]
      rw [hae2.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hcap2
    have hv2 : e2.mem.readLE p.toNat 8 = digit 3 (s.mem.readLE p.toNat 8) := by
      rw [hfr2.readLE _ _ (by
        simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hpo, by omega⟩, by omega⟩)]; exact hpv1
    rw [hm2] at hpc2
    have hpa2 : e2.mem.accessible p.toNat 8 true = true := by
      rw [hae2.accessible]; exact hpa0
    have hcl2 : ReachesRet (Extracted.program.link impl) (e2.regs 30) e2 (fun e' =>
        e'.pc = e2.regs 30 ∧ e'.sp = e2.sp ∧ e'.regs 28 = e2.regs 28 ∧ e'.regs 18 = e2.regs 18 ∧
        MemFrame e2.mem e'.mem [(p.toNat, p.toNat + 8)] ∧
        e'.mem.readLE p.toNat 8 = digit 2 (digit 3 (s.mem.readLE p.toNat 8))) := by
      janus_run
      simp only [hc2, hv2]
      refine ⟨MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega), ?_⟩
      try rw [Memory.readLE_writeLE_self]
      simp only [digit]; omega
    obtain ⟨j2, f2, hj2, -, hfpc2, hfsp2, hf282, hf182, hff2, hpv2⟩ := hcl2
    refine GoReturns.of_steps (hj2.withExit hret.fetch_none) ?_
    have hacc2 : MemFrame S.mem f2.mem (win0 P s p) := hae2.trans hff2 fun a n h => ⟨h, hsubP a n h⟩
    obtain ⟨hdr2, hpf2⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 128) (keep := keep0 s) hl hfpc2 hfsp2 (hf282.trans h28_2)
      (hf182.trans h18_2) henv2 hff2 (by
        unfold keep0; simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpo, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    have hE2 := (hcont2 f2 hdr2).1 (hpf2.trans hpn2)
    rw [Engine_cons] at hE2
    obtain ⟨k3, e3, hst3, ⟨hpc3, h26_3, h28_3, h18_3, h29_3, hal3, hlo3, hhi3, h30a3, h30b3, henv3⟩,
      hfr3, -, -, hpn3, -, -, hcont3, -⟩ := hE2
    dsimp only at hpc3 h26_3 hlo3 hhi3 hfr3 hcont3
    refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
    have hae3 : MemFrame S.mem e3.mem (win0 P s p) := hacc2.trans hfr3 fun a n h => ⟨h, hsubR a n h⟩
    have hm3 : e3.mem.readLE (s.sp.toNat - 48) 8 = func1A := by
      rw [hae3.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hfv1
    have hc3 : e3.mem.readLE (s.sp.toNat - 48 + 8) 8 = p.toNat := by
      rw [show s.sp.toNat - 48 + 8 = s.sp.toNat - 40 by omega]
      rw [hae3.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hcap1
    have hv3 : e3.mem.readLE p.toNat 8 = digit 2 (digit 3 (s.mem.readLE p.toNat 8)) := by
      rw [hfr3.readLE _ _ (by
        simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hpo, by omega⟩, by omega⟩)]; exact hpv2
    rw [hm3] at hpc3
    have hpa3 : e3.mem.accessible p.toNat 8 true = true := by
      rw [hae3.accessible]; exact hpa0
    have hcl3 : ReachesRet (Extracted.program.link impl) (e3.regs 30) e3 (fun e' =>
        e'.pc = e3.regs 30 ∧ e'.sp = e3.sp ∧ e'.regs 28 = e3.regs 28 ∧ e'.regs 18 = e3.regs 18 ∧
        MemFrame e3.mem e'.mem [(p.toNat, p.toNat + 8)] ∧
        e'.mem.readLE p.toNat 8 = digit 1 (digit 2 (digit 3 (s.mem.readLE p.toNat 8)))) := by
      janus_run
      simp only [hc3, hv3]
      refine ⟨MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega), ?_⟩
      try rw [Memory.readLE_writeLE_self]
      simp only [digit]; omega
    obtain ⟨j3, f3, hj3, -, hfpc3, hfsp3, hf283, hf183, hff3, hpv3⟩ := hcl3
    refine GoReturns.of_steps (hj3.withExit hret.fetch_none) ?_
    have hacc3 : MemFrame S.mem f3.mem (win0 P s p) := hae3.trans hff3 fun a n h => ⟨h, hsubP a n h⟩
    obtain ⟨hdr3, hpf3⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 128) (keep := keep0 s) hl hfpc3 hfsp3 (hf283.trans h28_3)
      (hf183.trans h18_3) henv3 hff3 (by
        unfold keep0; simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpo, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    have hE3 := (hcont3 f3 hdr3).1 (hpf3.trans hpn3)
    rw [Engine_nil] at hE3
    obtain ⟨k4, d, hst4, hU, hpd, -, hfrd, -, -, -⟩ := hE3
    refine GoReturns.leave (v := ⟨etyp.toNat, edata.toNat⟩) (hst4.withExit hret.fetch_none) ?_ ?_
    · have hg' : gOf s = (S.regs 28).toNat := by simp only [gOf, hS28]
      have hU' := hU; rw [← hg'] at hU'
      have hpd' := hpd; rw [show (S.regs 28).toNat = gOf s from hg'.symm] at hpd'
      refine ⟨hU', _, _, hpd', ?_, rfl⟩
      simp only [hS0, hS1]
    · refine ⟨hx', rfl, ?_⟩
      rw [hfrd.readLE _ _ (by
        simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hpo, by omega⟩, by omega⟩), hpv3]
      rfl


/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSat` (code that
`Janus.Contracts.PanicSatRun` proves meets the `gopanic` contract in every program that contains
it), linked into `DeferOrder`'s program with a branch to it at the `runtime.gopanic` address, and a
call state — an `any` of type word `1`, `x = 11` — in the precondition; the call panics. -/

namespace Witness

open Janus.Contracts.PanicSat Janus.Contracts.PanicModel

abbrev T0 : List FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : PanicRuntime := P0 T0 RPa

def gA : Nat := Extracted.program.contractAddr "runtime.gopanic"

/-- The code linked next to `DeferOrder`: the model engine and the branch to it at `runtime.gopanic`. -/
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
      else if i = 1 then 11#64 else if i = 2 then 1#64 else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmW }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [BitVec.ofNat 64 pA, 11#64, 1#64, 0#64] s0 := by
  refine ⟨rfl, rfl, fun i h => ?_⟩
  simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem pre : PanicCallerOK PW s0 128 40 := by
  refine ⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide

theorem pre' : PanicCallerOK PW s0 128 40 ∧ Ptr s0.mem (BitVec.ofNat 64 pA) 8 true ∧
    Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 (s0.sp.toNat - (PW.depth + 128)) (PW.depth + 128 + 40) ∧
    Outside (BitVec.ofNat 64 pA).toNat 8 PW.priv ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧
    0 < PW.room s0.mem (gOf s0) ∧ ∀ d ∈ PW.defers s0.mem (gOf s0), s0.sp.toNat ≤ d.sp := by
  refine ⟨pre, ⟨by decide, by decide⟩, ?_, ?_, by decide, ?_, ?_⟩
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
    GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry
      [BitVec.ofNat 64 pA, 11#64, 1#64, 0#64] s ∧
    (PanicCallerOK P s 128 40 ∧ Ptr s.mem (BitVec.ofNat 64 pA) 8 true ∧
      Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 (s.sp.toNat - (P.depth + 128)) (P.depth + 128 + 40) ∧
      Outside (BitVec.ofNat 64 pA).toNat 8 P.priv ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧
      0 < P.room s.mem (gOf s) ∧ ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp) :=
  ⟨implW, PW, U0, ret, s0, P0_laws T0 RPa, hpan, hret, setup, pre'⟩

/-- So the guarantee is reached: with `x = 11` `DeferOrder` panics with `e`, after the three
deferred calls ran in LIFO order. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClassU PW U0 s0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ ((11#64 : BitVec 64).toNat ≤ 10 ∧ (s'.regs 0).toNat = (11#64 : BitVec 64).toNat ∧
        s'.mem.readLE (BitVec.ofNat 64 pA).toNat 8 = order (s0.mem.readLE (BitVec.ofNat 64 pA).toNat 8))
    | .panicked v s' => 10 < (11#64 : BitVec 64).toNat ∧ v = ⟨(1#64 : BitVec 64).toNat, (0#64 : BitVec 64).toNat⟩ ∧
        s'.mem.readLE (BitVec.ofNat 64 pA).toNat 8 = order (s0.mem.readLE (BitVec.ofNat 64 pA).toNat 8)
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U0 hpan (BitVec.ofNat 64 pA) 11#64 1#64 0#64 ret hret s0 setup pre'

end Witness

end Proof
