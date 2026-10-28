import Extracted

/-!
# `DeferTwice()` runs two heap-allocated defers (arm64)

**Guarantee (example 6 of docs/COVERAGE.md R6).** `DeferTwice` is
`for i := 0; i < 2; i++ { defer func() {}() }`. A defer inside a loop is never open-coded: each
iteration calls `runtime.deferproc` (a heap `_defer` record) and the function's exit calls
`runtime.deferreturn`, which runs the recorded calls. For every panic-runtime model `P` satisfying
its laws, every implementation of `runtime.deferproc` and `runtime.deferreturn` meeting their
contracts (`Janus.Contracts.Panic`, pinned to the Go 1.26 runtime's code), every admissible return
address and every call state in which the runtime is usable and has `P.depth` bytes of stack
below the 32-byte frame (`PanicCallerOK`), the closure's funcval (a `.rodata` object, outside the
runtime's memory and the stack window) is in memory and the runtime has room for two records, the
call **returns** (obeying the ABI) — both `deferproc` calls return, `deferreturn` calls the closure
twice (it runs the program's own code, here a `RET`) and returns — and memory changes only in the
runtime's memory and the stack window. It never panics.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Proof


/-! Code addresses are read off the extraction (`janus_eval%`), never copied: a relinked
binary needs no edit. -/
local macro "loc_DeferTwice_64" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferTwice" + 64))
local macro "loc_DeferTwice_88" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferTwice" + 88))

local macro "fvA" : term => `(janus_eval% (Extracted.program.data.head!.base))
local macro "func1A" : term =>
  `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferTwice.func1"))

set_option maxRecDepth 100000 in
/-- `DeferTwice`'s funcval: the closure's entry, in `.rodata`. -/
theorem fv_read (m : Memory) (hd : Extracted.program.DataLoaded m) : m.readLE fvA 8 = func1A :=
  readLE_of_dataRead hd (by decide)

set_option maxRecDepth 100000 in
theorem fv_acc (m : Memory) (hd : Extracted.program.DataLoaded m) : m.accessible fvA 8 false = true :=
  accessible_of_dataRead hd (by decide)

set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hdp : DeferprocContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferproc") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry []
      (fun s => PanicCallerOK P s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside fvA 8 (P.priv ++ [(s.sp.toNat - (P.depth + 32), s.sp.toNat)]) ∧ 2 ≤ P.room s.mem (gOf s) ∧
        P.saved s.mem (gOf s) = none ∧ ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp)
      (fun _ => goClass P)
      (fun s s' => MemFrame s.mem s'.mem (P.priv ++ [(s.sp.toNat - (P.depth + 32), s.sp.toNat)]) ∧
        P.Env s'.mem)
      (fun _ _ _ => False) := by
  intro ret hret s hs ⟨hc, hd, hfo, hroom, hsave, hds⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd', hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd
  have h32 : (s.sp - 32#64).toNat = s.sp.toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn"))
    hret.fetch_none ?_
  have hagw : ∀ m, MemFrame s.mem m [(s.sp.toNat - (P.depth + 32), s.sp.toNat)] → Map.Agrees s.mem m P.priv :=
    fun m hf => Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 32)) (hi := s.sp.toNat) hf
      (Outside.of_sub hout (by omega) (by omega))
  -- first iteration: deferproc
  janus_run until [Extracted.program.contractAddr "runtime.deferproc"]
  refine ReachesRet.name fun S hS => ?_
  have hSsp : S.sp = s.sp - 32#64 := by rw [hS] <;> rfl
  have hSspn : S.sp.toNat = s.sp.toNat - 32 := by rw [hSsp]; exact h32
  have hSf : MemFrame s.mem S.mem [(s.sp.toNat - (P.depth + 32), s.sp.toNat)] := by rw [hS]; janus_frame
  have hS0 : S.regs 0 = BitVec.ofNat 64 fvA := by rw [hS] <;> rfl
  have hS28 : S.regs 28 = s.regs 28 := by rw [hS] <;> rfl
  have hS18 : S.regs 18 = s.regs 18 := by rw [hS] <;> rfl
  have hS30 : S.regs 30 = BitVec.ofNat 64 loc_DeferTwice_64 := by rw [hS] <;> rfl
  have hSpc : S.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferproc") := by rw [hS] <;> rfl
  have hgS : gOf S = gOf s := by simp only [gOf, hS28]
  have hagS : Map.Agrees s.mem S.mem P.priv := hagw _ hSf
  have hSfW : MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + 32), s.sp.toNat)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  refine ReachesRet.call hdp hSpc ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
      (by rw [hSspn]; omega) hS28 (by rw [hS30]; decide) (by rw [hS30]; decide),
    by rw [hgS, hl.room_frame _ _ _ hagS]; omega⟩ ?_
  intro s1 hpc1 hq1
  obtain ⟨⟨j1, f1, v1, m1, ex1, ep1, hs1, hfr1, henv1⟩, hdef1, hpan1, hsav1, hrp1, hroom1⟩ := hq1
  have hm1 : s1.mem = m1 := by rw [hs1]; rfl
  have hS0n : (S.regs 0).toNat = fvA := by rw [hS0]; simp
  have hd1 : P.defers m1 (gOf s) = { sp := s.sp.toNat - 32, fns := [fvA] } :: P.defers s.mem (gOf s) := by
    have := hdef1; rw [hm1, hgS, hSspn, hS0n, hl.defers_frame _ _ _ hagS] at this; exact this
  have hsv1 : P.saved m1 (gOf s) = none := by
    have := hsav1; rw [hm1, hgS, hl.saved_frame _ _ _ hagS] at this; rw [this]; exact hsave
  have hrm1 : P.room s.mem (gOf s) ≤ P.room m1 (gOf s) + 1 := by
    have := hroom1; rw [hm1, hgS, hl.room_frame _ _ _ hagS] at this; exact this
  have hstep : ∀ (S : State) (m : Memory), MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + 32), s.sp.toNat)]) →
      S.sp.toNat = s.sp.toNat - 32 → MemFrame S.mem m (P.priv ++ calleeStack S P.depth 1) →
      MemFrame s.mem m (P.priv ++ [(s.sp.toNat - (P.depth + 32), s.sp.toNat)]) := by
    intro S m h1 h2 h3
    refine h1.trans h3 fun a n h => ⟨h, ?_⟩
    simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack, h2] at h ⊢
    obtain ⟨h4, h5⟩ := h
    refine ⟨h4, ?_, ?_⟩ <;> omega
  have hW1 := hstep S m1 hSfW hSspn hfr1
  clear hdef1 hpan1 hsav1 hrp1 hroom1 hSf hSfW hagS hS0 hS28 hS18 hS30 hSpc hgS hSsp hSspn hS0n hm1 hpc1
  subst hs1
  subst hS
  simp only [calleeStack, h32] at hfr1
  -- second iteration: deferproc
  janus_run until [Extracted.program.contractAddr "runtime.deferproc"]
  refine ReachesRet.name fun S2 hS2 => ?_
  have hS2sp : S2.sp = s.sp - 32#64 := by rw [hS2] <;> rfl
  have hS2spn : S2.sp.toNat = s.sp.toNat - 32 := by rw [hS2sp]; exact h32
  have hS2f : MemFrame m1 S2.mem [(s.sp.toNat - (P.depth + 32), s.sp.toNat)] := by rw [hS2]; janus_frame
  have hS20 : S2.regs 0 = BitVec.ofNat 64 fvA := by rw [hS2] <;> rfl
  have hS228 : S2.regs 28 = s.regs 28 := by rw [hS2] <;> rfl
  have hS230 : S2.regs 30 = BitVec.ofNat 64 loc_DeferTwice_64 := by rw [hS2] <;> rfl
  have hS2pc : S2.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferproc") := by rw [hS2] <;> rfl
  have hgS2 : gOf S2 = gOf s := by simp only [gOf, hS228]
  have hS2fW : MemFrame s.mem S2.mem (P.priv ++ [(s.sp.toNat - (P.depth + 32), s.sp.toNat)]) :=
    hW1.trans hS2f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagS2 : Map.Agrees m1 S2.mem P.priv :=
    Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 32)) (hi := s.sp.toNat) hS2f
      (Outside.of_sub hout (by omega) (by omega))
  refine ReachesRet.call hdp hS2pc ⟨PanicPre.of_within hc hS2fW (hl.env_frame _ _ henv1 hagS2) (by omega) (by omega)
      (by rw [hS2spn]; omega) hS228 (by rw [hS230]; decide) (by rw [hS230]; decide),
    by rw [hgS2, hl.room_frame _ _ _ hagS2]; omega⟩ ?_
  intro s2 hpc2 hq2
  obtain ⟨⟨j2, f2, v2, m2, ex2, ep2, hs2, hfr2, henv2⟩, hdef2, hpan2, hsav2, hrp2, hroom2⟩ := hq2
  have hm2 : s2.mem = m2 := by rw [hs2]; rfl
  have hS20n : (S2.regs 0).toNat = fvA := by rw [hS20]; simp
  have hd2 : P.defers m2 (gOf s) = { sp := s.sp.toNat - 32, fns := [fvA] } ::
      { sp := s.sp.toNat - 32, fns := [fvA] } :: P.defers s.mem (gOf s) := by
    have := hdef2; rw [hm2, hgS2, hS2spn, hS20n, hl.defers_frame _ _ _ hagS2, hd1] at this; exact this
  have hsv2 : P.saved m2 (gOf s) = none := by
    have := hsav2; rw [hm2, hgS2, hl.saved_frame _ _ _ hagS2] at this; rw [this]; exact hsv1
  have hW2 := hstep S2 m2 hS2fW hS2spn hfr2
  clear hdef2 hpan2 hsav2 hrp2 hroom2 hS2f hS2fW hagS2 hS20 hS228 hS230 hS2pc hgS2 hS2sp hS2spn hS20n hm2 hpc2 hd1 hrm1 hsv1 hW1 henv1
  subst hs2
  subst hS2
  simp only [calleeStack, h32] at hfr2
  -- the exit: deferreturn
  janus_run until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun S3 hS3 => ?_
  have hS3sp : S3.sp = s.sp - 32#64 := by rw [hS3] <;> rfl
  have hS3spn : S3.sp.toNat = s.sp.toNat - 32 := by rw [hS3sp]; exact h32
  have hS3f : MemFrame m2 S3.mem [(s.sp.toNat - (P.depth + 32), s.sp.toNat)] := by rw [hS3]; janus_frame
  have hS328 : S3.regs 28 = s.regs 28 := by rw [hS3] <;> rfl
  have hS318 : S3.regs 18 = s.regs 18 := by rw [hS3] <;> rfl
  have hS3pc : S3.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by rw [hS3] <;> rfl
  have hgS3 : gOf S3 = gOf s := by simp only [gOf, hS328]
  have hS3fW : MemFrame s.mem S3.mem (P.priv ++ [(s.sp.toNat - (P.depth + 32), s.sp.toNat)]) :=
    hW2.trans hS3f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagS3 : Map.Agrees m2 S3.mem P.priv :=
    Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 32)) (hi := s.sp.toNat) hS3f
      (Outside.of_sub hout (by omega) (by omega))
  have hS3lr : (S3.regs 30).toNat % 4 = 0 ∧ (S3.regs 30).toNat < 2 ^ 48 := by
    rw [hS3]; simp [setReg]
  have hpre3 : PanicPre P 0 S3 := PanicPre.of_within hc hS3fW (hl.env_frame _ _ henv2 hagS3) (by omega) (by omega)
    (by rw [hS3spn]; omega) hS328 hS3lr.1 hS3lr.2
  have hsv3 : P.saved S3.mem (gOf S3) = none := by
    rw [hgS3, hl.saved_frame _ _ _ hagS3]; exact hsv2
  have hD3 : P.defers S3.mem (gOf S3) = { sp := s.sp.toNat - 32, fns := [fvA] } ::
      { sp := s.sp.toNat - 32, fns := [fvA] } :: P.defers s.mem (gOf s) := by
    rw [hgS3, hl.defers_frame _ _ _ hagS3, hd2]
  have hF : retFrame P S3 = ⟨s.sp.toNat - 32, s.sp.toNat - 32, 0, none⟩ := by
    simp only [retFrame, hsv3, hS3spn]
  have hds' : ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat - 32 < d.sp := fun d hd => by have := hds d hd; omega
  have hrA := recItems_above hds'
  have hI : frameItems S3.mem (retFrame P S3) (P.defers S3.mem (gOf S3)) =
      [{ fn := fvA, bits := none, chain := { sp := s.sp.toNat - 32, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] := by
    rw [hF, hD3]
    simp [frameItems, recItems, fnItems, hrA]
  have hfvacc : s.mem.accessible fvA 8 false = true := fv_acc _ hd
  have hfv3 : S3.mem.readLE fvA 8 = func1A := by
    rw [hS3fW.readLE _ _ hfo]; exact fv_read _ hd
  have hFO : FrameOK P S3.mem (retFrame P S3) (frameItems S3.mem (retFrame P S3) (P.defers S3.mem (gOf S3))) := by
    rw [hI, hF]
    simp only [outside_append, outside_cons, outside_nil, and_true] at hfo
    refine ⟨trivial, fun it hit => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl <;> dsimp only <;>
      exact ⟨by decide, by rw [hS3fW.accessible]; exact hfvacc, by rw [hfv3], by rw [hfv3]; decide,
        hfo.1, by omega⟩
  have hS3fv : ∀ e : State, MemFrame S3.mem e.mem (P.priv ++ rtWin P (retFrame P S3) ++ bitsWin (retFrame P S3)) →
      e.mem.readLE fvA 8 = func1A := by
    intro e hfr
    rw [hfr.readLE _ _ (by
      rw [hF]
      simp only [outside_append, rtWin, bitsWin, outside_cons, outside_nil, and_true] at hfo ⊢
      exact ⟨hfo.1, by omega⟩), hfv3]
  refine DeferreturnContract.apply (S := S3) hdr hS3pc ⟨hpre3, hFO⟩ ?_
  intro hE
  rw [hI, hF] at hE
  rw [Engine_cons] at hE
  obtain ⟨k1, e1, hst1, ⟨hpc1, h26_1, h28_1, h18_1, h29_1, hal1, hlo1, hhi1, h30a1, h30b1, henvE1⟩,
    hfrE1, -, -, hpn1, -, -, hcont1, -⟩ := hE
  dsimp only at hpc1 h26_1 hlo1 hhi1 hfrE1 hcont1
  have hfv1 : e1.mem.readLE fvA 8 = func1A := hS3fv e1 (by rw [hF]; exact hfrE1)
  rw [hfv1] at hpc1
  refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
  have hcl1 : ReachesRet (Extracted.program.link impl) (e1.regs 30) e1 (fun e' =>
      e'.pc = e1.regs 30 ∧ e'.sp = e1.sp ∧ e'.regs 28 = e1.regs 28 ∧ e'.regs 18 = e1.regs 18 ∧
      e'.mem = e1.mem) := by
    janus_run
  obtain ⟨j1', f1', hj1, -, hfpc1, hfsp1, hf281, hf181, hfm1⟩ := hcl1
  refine GoReturns.of_steps (hj1.withExit hret.fetch_none) ?_
  obtain ⟨hdr1, hpf1⟩ := DeferReturned.of_same hl hfpc1 hfsp1 (hf281.trans h28_1) (hf181.trans h18_1) hfm1 henvE1
  have hE1 := (hcont1 f1' hdr1).1 (hpf1.trans hpn1)
  rw [Engine_cons] at hE1
  obtain ⟨k2, e2, hst2, ⟨hpc2, h26_2, h28_2, h18_2, h29_2, hal2, hlo2, hhi2, h30a2, h30b2, henvE2⟩,
    hfrE2, -, -, hpn2, -, -, hcont2, -⟩ := hE1
  dsimp only at hpc2 h26_2 hlo2 hhi2 hfrE2 hcont2
  have hfrE2' := hfrE1.trans (by rw [← hfm1]; exact hfrE2) (fun a n h => ⟨h, h⟩)
  have hfv2 : e2.mem.readLE fvA 8 = func1A := hS3fv e2 (by rw [hF]; exact hfrE2')
  rw [hfv2] at hpc2
  refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
  have hcl2 : ReachesRet (Extracted.program.link impl) (e2.regs 30) e2 (fun e' =>
      e'.pc = e2.regs 30 ∧ e'.sp = e2.sp ∧ e'.regs 28 = e2.regs 28 ∧ e'.regs 18 = e2.regs 18 ∧
      e'.mem = e2.mem) := by
    janus_run
  obtain ⟨j2', f2', hj2, -, hfpc2, hfsp2, hf282, hf182, hfm2⟩ := hcl2
  refine GoReturns.of_steps (hj2.withExit hret.fetch_none) ?_
  obtain ⟨hdr2, hpf2⟩ := DeferReturned.of_same hl hfpc2 hfsp2 (hf282.trans h28_2) (hf182.trans h18_2) hfm2 henvE2
  have hE2 := (hcont2 f2' hdr2).1 (hpf2.trans hpn2)
  rw [Engine_nil] at hE2
  obtain ⟨k3, d, hst3, hdpc, hdsp, hd28, hd18, hd29, hfrD, henvD, -⟩ := hE2
  refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
  have hSD : MemFrame S3.mem d.mem (P.priv ++ rtWin P (retFrame P S3) ++ bitsWin (retFrame P S3)) := by
    have h1 : MemFrame S3.mem e1.mem (P.priv ++ rtWin P (retFrame P S3) ++ bitsWin (retFrame P S3)) := by
      rw [hF]; exact hfrE1
    have h2 : MemFrame S3.mem e2.mem (P.priv ++ rtWin P (retFrame P S3) ++ bitsWin (retFrame P S3)) := by
      rw [hF]; exact hfrE2'
    exact h2.trans (by rw [← hfm2]; exact hfrD) (fun a n h => ⟨h, h⟩)
  rw [hF] at hSD hfrD
  simp only [rtWin, bitsWin, List.append_nil, hS3spn] at hSD
  subst hS3
  have hdpc' : d.pc = (BitVec.ofNat 64 loc_DeferTwice_88) := by rw [hdpc] <;> rfl
  have hdsp' : d.sp = s.sp - 32#64 := by rw [hdsp] <;> rfl
  have hd29' : d.regs 29 = s.sp - 40#64 := by rw [hd29] <;> rfl
  have hd28' : d.regs 28 = s.regs 28 := by rw [hd28] <;> rfl
  have hd18' : d.regs 18 = s.regs 18 := by rw [hd18] <;> rfl
  have hdspn : d.sp.toNat = s.sp.toNat - 32 := by rw [hdsp']; exact h32
  have hdacc : d.mem.accessible (s.sp.toNat - (P.depth + 32)) (P.depth + 32 + 0) true = true := by
    rw [hSD.accessible, hS3fW.accessible]; exact hst
  have hdacc' : d.mem.accessible (s.sp.toNat - 40) 40 true = true :=
    Memory.accessible_mono _ hdacc (by omega) (by omega)
  have hdacc'' : d.mem.accessible (s.sp.toNat - 40) 8 false = true :=
    Memory.accessible_weaken _ (Memory.accessible_mono _ hdacc' (by omega) (by omega))
  clear hdpc hdsp hd29 hd28 hd18 hfrD hfrE2 hfrE2' hfrE1 hcont1 hcont2 hfm1 hfm2 hpn1 hpn2 hst1 hst2 hst3 hdr1 hdr2 hpf1 hpf2
  refine GoReturns.of_reaches ?_
  janus_run
  refine ⟨hS3fW.trans hSD (fun a n h => ⟨h, ?_⟩), henvD⟩
  simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, by omega⟩

/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSat` (code that
`Janus.Contracts.PanicSatRun` proves meets the `deferproc` and `deferreturn` contracts in every
program that contains it) linked into `DeferTwice`'s program with a branch to it at each of the
two contract addresses, and a call state satisfying the precondition: so `correctness` applies
(`nonvacuous`), and `DeferTwice` returns from that state (`returns`). -/

namespace Witness

open Janus.Contracts.PanicSat Janus.Contracts.PanicModel

abbrev T0 : List FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : PanicRuntime := P0 T0 RPa

def dpA : Nat := Extracted.program.contractAddr "runtime.deferproc"
def drA : Nat := Extracted.program.contractAddr "runtime.deferreturn"

/-- The code linked next to `DeferTwice`: the model engine and a branch to it at each contract
address. -/
def implW : List Segment :=
  panicImpl Extracted.program [("runtime.deferproc", eDeferproc), ("runtime.deferreturn", eDeferreturn)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

theorem stubDp : StubAt (Extracted.program.link implW) dpA eDeferproc :=
  StubAt.of_decode (w := stubWord dpA eDeferproc) (imm := (eDeferproc - dpA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem stubDr : StubAt (Extracted.program.link implW) drA eDeferreturn :=
  StubAt.of_decode (w := stubWord drA eDeferreturn) (imm := (eDeferreturn - drA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem hdp : DeferprocContract (Extracted.program.link implW) dpA PW :=
  deferproc_at stubDp (deferproc_contract engineAt T0)

theorem hdr : DeferreturnContract (Extracted.program.link implW) drA PW U0 :=
  deferreturn_at stubDr (deferreturn_run engineAt)

def wm : Memory := witMemD (tabWords T0) Extracted.data

abbrev wg : Nat := witG
abbrev wsp : Nat := witSP
abbrev ret : Nat := witRet

theorem env_w : Env0 T0 wm := by
  unfold Env0
  have hnd : ndef wm = 0 := by decide
  refine ⟨by decide, by decide, by decide, fun i hi => ?_, ?_⟩
  · omega
  · unfold TableOK
    exact ⟨by decide, by decide, by decide⟩

theorem hret : RetAddr (Extracted.program.link implW) ret := RetAddr.of_check (by decide)

theorem dataLoaded : Extracted.program.DataLoaded wm := by
  unfold Program.DataLoaded
  set_option maxRecDepth 100000 in decide

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret
      else if i = 29 then BitVec.ofNat 64 (wsp - 8) else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wm }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h⟩

theorem pre : PanicCallerOK PW s0 32 0 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside fvA 8 (PW.priv ++ [(s0.sp.toNat - (PW.depth + 32), s0.sp.toNat)]) ∧ 2 ≤ PW.room s0.mem (gOf s0) ∧
    PW.saved s0.mem (gOf s0) = none ∧ ∀ d ∈ PW.defers s0.mem (gOf s0), s0.sp.toNat ≤ d.sp := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_⟩, dataLoaded, ?_, ?_, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · simp only [P0_priv, outside_append, outside_cons, outside_nil, and_true]; decide
  · show 2 ≤ room0 wm
    rw [room0_eq]; decide
  · show saved0 wm = none
    rw [saved0_eq]; decide
  · intro d hd
    have hnd : ndef wm = 0 := by decide
    have : defers0 wm = [] := by rw [defers0_eq, hnd]; rfl
    exact absurd hd (by rw [show PW.defers s0.mem (gOf s0) = defers0 wm from rfl, this]; simp)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Segment) (P : PanicRuntime) (U : State → Nat → Nat → Prop) (ret : Nat)
    (s : State), P.Laws ∧
    DeferprocContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferproc") P ∧
    DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P U ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [] s ∧
    (PanicCallerOK P s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside fvA 8 (P.priv ++ [(s.sp.toNat - (P.depth + 32), s.sp.toNat)]) ∧ 2 ≤ P.room s.mem (gOf s) ∧
      P.saved s.mem (gOf s) = none ∧ ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp) :=
  ⟨implW, PW, U0, ret, s0, P0_laws T0 RPa, hdp, hdr, hret, setup, pre⟩

/-- So the guarantee is reached: `DeferTwice` returns from `s0`. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClass PW) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧
        (MemFrame s0.mem s'.mem (PW.priv ++ [(s0.sp.toNat - (PW.depth + 32), s0.sp.toNat)]) ∧ PW.Env s'.mem)
    | .panicked v s' => False
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U0 hdp hdr ret hret s0 setup pre

end Witness

end Proof
