import Janus
import Extracted

/-! `example.com/basic.DeferTwice()` on amd64: two heap defer records in a loop
(`runtime.deferproc`) run at the exit (`runtime.deferreturn`); with their contracts
(`Janus.Contracts.PanicAmd64`, pinned) the call returns obeying the ABI and never panics.
The funcval is a `.rodata` object, outside the runtime's memory and the stack window; the
closure (a `RET`) is the program's own code. Example 6 of docs/COVERAGE.md R6. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64
open Janus.Contracts.MapAmd64 (keepABI_apply)
open Janus.Contracts.Panic (Item recItems frameItems fnItems frameKeep bitsWin recItems_above)

local macro "fvA" : term => `(janus_eval% (Extracted.program.data.head!.base))
local macro "func1A" : term =>
  `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferTwice.func1"))

set_option maxRecDepth 100000 in
/-- `DeferTwice`'s funcval: the closure's entry, in `.rodata`. -/
theorem fv_read (m : Janus.Arm64.Memory) (hd : Extracted.program.DataLoaded m) : m.readLE fvA 8 = func1A :=
  readLE_of_dataRead hd (by decide)

set_option maxRecDepth 100000 in
theorem fv_acc (m : Janus.Arm64.Memory) (hd : Extracted.program.DataLoaded m) : m.accessible fvA 8 false = true :=
  Janus.Contracts.PanicSatAmd64.accessible_of_dataRead hd (by decide)

/-- The closure `DeferTwice.func1` is a `RET`. -/
theorem func1_ret (impl : List Janus.Amd64.Segment) (e : State) (hpc : e.rip = BitVec.ofNat 64 func1A)
    (hra : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 47)
    (hacc : e.mem.accessible (e.regs 4).toNat 8 false = true) :
    ReachesRet (Extracted.program.link impl) (retAddrOf e) e (fun e' =>
      e'.rip = retAddrOf e ∧ e'.regs 4 = e.regs 4 + 8 ∧ e'.regs 14 = e.regs 14 ∧ e'.regs 5 = e.regs 5 ∧
      e'.xmm 15 = e.xmm 15 ∧ e'.df = e.df ∧ e'.mem = e.mem) := by
  obtain ⟨cr, crip, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpc
  janus64_run

set_option maxHeartbeats 0 in
theorem correctness (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hdp : DeferprocContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferproc") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry []
      (fun s => PanicCallerOK P s 32 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside fvA 8 (P.priv ++ [((s.regs regSP).toNat - (P.depth + 32), (s.regs regSP).toNat + 8)]) ∧
        2 ≤ P.room s.mem (gOf s) ∧ P.saved s.mem (gOf s) = none ∧
        ∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp)
      (fun _ => goClass P)
      (fun s s' => MemFrame s.mem s'.mem
          (P.priv ++ [((s.regs regSP).toNat - (P.depth + 32), (s.regs regSP).toNat + 8)]) ∧
        P.Env s'.mem)
      (fun _ _ _ => False) := by
  intro ret hret s hs ⟨hc, hd, hfo, hroom, hsave, hds⟩
  have hc' := hc
  obtain ⟨henv, hg, hal, hd', hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd' hb hal hfo hds
  have h32 : (18446744073709551584 + (s.regs 4).toNat) % 18446744073709551616 = (s.regs 4).toNat - 32 := by
    omega
  have h32' : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hagw : ∀ m, MemFrame s.mem m [((s.regs 4).toNat - (P.depth + 32), (s.regs 4).toNat + 8)] →
      Spec.Map.Agrees s.mem m P.priv :=
    fun m hf => Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 32)) (hi := (s.regs 4).toNat + 8) hf
      (Outside.of_sub hout (by omega) (by omega))
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn"))
    hret.fetch_none ?_
  -- first iteration: deferproc
  janus64_run until [Extracted.program.contractAddr "runtime.deferproc"]
  refine ReachesRet.name fun S hS => ?_
  have hSsp : S.regs 4 = s.regs 4 - 32#64 := by rw [hS] <;> rfl
  have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 32 := by rw [hSsp]; exact h32'
  have hSf : MemFrame s.mem S.mem [((s.regs 4).toNat - (P.depth + 32), (s.regs 4).toNat + 8)] := by
    rw [hS]; janus_frame
  have hS0 : S.regs 0 = BitVec.ofNat 64 fvA := by rw [hS] <;> rfl
  have hS14 : S.regs 14 = s.regs 14 := by rw [hS] <;> rfl
  have hSx : S.xmm 15 = 0 := by rw [hS]; exact h_x15
  have hSdf : S.df = false := by rw [hS]
  have hSpc : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferproc") := by rw [hS] <;> rfl
  have hgS : gOf S = gOf s := by simp only [gOf, hS14]
  have hagS : Spec.Map.Agrees s.mem S.mem P.priv := hagw _ hSf
  have hSfW : MemFrame s.mem S.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 32), (s.regs 4).toNat + 8)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  have hSra : S.mem.readLE (S.regs 4).toNat 8 = 4746615 := by
    rw [hS]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h32', Janus.Arm64.Memory.readLE_writeLE_self]
  have hS_i : S.mem.readLE ((s.regs 4).toNat - 16) 8 = 0 := by
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  refine ReachesRet.call hdp hSpc ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
      (by omega) hS14 hSx hSdf (by rw [hSra]; decide),
    by rw [hgS, hl.room_frame _ _ _ hagS]; omega⟩ ?_
  intro s1 hpc1 hq1
  obtain ⟨⟨r1, x1, y1, f1, m1, hs1, hfr1, henv1⟩, hdef1, hkeep1⟩ := hq1
  have hm1 : s1.mem = m1 := by rw [hs1]
  have hS0n : (S.regs 0).toNat = fvA := by rw [hS0]; simp
  have hfsp : fspOf S = (s.regs 4).toNat - 24 := by simp only [fspOf, hSspn]; omega
  have hd1 : P.defers m1 (gOf s) = { sp := (s.regs 4).toNat - 24, fns := [fvA] } :: P.defers s.mem (gOf s) := by
    have := hdef1; rw [hm1, hgS, hfsp, hS0n, hl.defers_frame _ _ _ hagS] at this; exact this
  have hsv1 : P.saved m1 (gOf s) = none := by
    have := hkeep1.2.1; rw [hm1, hgS, hl.saved_frame _ _ _ hagS] at this; rw [this]; exact hsave
  have hrm1 : P.room s.mem (gOf s) ≤ P.room m1 (gOf s) + 1 := by
    have := hkeep1.2.2.2; rw [hm1, hgS, hl.room_frame _ _ _ hagS] at this; exact this
  simp only [MapAmd64.calleeStack, hSspn] at hfr1
  have hstep : ∀ (S : State) (m : Memory), MemFrame s.mem S.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 32), (s.regs 4).toNat + 8)]) →
      (S.regs 4).toNat = (s.regs 4).toNat - 32 →
      MemFrame S.mem m (P.priv ++ [((S.regs 4).toNat - P.depth, (S.regs 4).toNat), ((S.regs 4).toNat + 8, (S.regs 4).toNat + 8 + 8 * 1)]) →
      MemFrame s.mem m (P.priv ++ [((s.regs 4).toNat - (P.depth + 32), (s.regs 4).toNat + 8)]) := by
    intro S m h1 h2 h3
    refine h1.trans h3 fun a n h => ⟨h, ?_⟩
    simp only [outside_append, outside_cons, outside_nil, and_true, h2] at h ⊢
    obtain ⟨h4, h5⟩ := h
    refine ⟨h4, ?_, ?_⟩ <;> omega
  have hW1 := hstep S m1 hSfW hSspn (by simpa [MapAmd64.calleeStack, hSspn] using hfr1)
  have hi1 : m1.readLE ((s.regs 4).toNat - 16) 8 = 0 := by
    rw [hfr1.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    exact hS_i
  have hr8_1 : m1.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hfr1.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 5).isLt; omega)
  have hrr_1 : m1.readLE (s.regs 4).toNat 8 = ret := by
    rw [hfr1.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact h_ret
  clear hdef1 hkeep1 hSf hSfW hagS hS0 hS14 hSx hSdf hSpc hgS hSsp hSspn hS0n hm1 hpc1 hfr1 hS_i hSra hfsp
  subst hs1
  subst hS
  -- second iteration: deferproc
  janus64_run until [Extracted.program.contractAddr "runtime.deferproc"]
  refine ReachesRet.name fun S2 hS2 => ?_
  have hS2sp : S2.regs 4 = s.regs 4 - 32#64 := by rw [hS2] <;> simp [setRegF, MapAmd64.keepABI]
  have hS2spn : (S2.regs 4).toNat = (s.regs 4).toNat - 32 := by rw [hS2sp]; exact h32'
  have hS2f : MemFrame m1 S2.mem [((s.regs 4).toNat - (P.depth + 32), (s.regs 4).toNat + 8)] := by
    rw [hS2]; janus_frame
  have hS20 : S2.regs 0 = BitVec.ofNat 64 fvA := by rw [hS2] <;> simp [setRegF]
  have hS214 : S2.regs 14 = s.regs 14 := by rw [hS2] <;> simp [setRegF, MapAmd64.keepABI]
  have hS2x : S2.xmm 15 = 0 := by rw [hS2]; simpa [MapAmd64.keepX15] using h_x15
  have hS2df : S2.df = false := by rw [hS2]
  have hS2pc : S2.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferproc") := by rw [hS2] <;> rfl
  have hgS2 : gOf S2 = gOf s := by simp only [gOf, hS214]
  have hS2fW : MemFrame s.mem S2.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 32), (s.regs 4).toNat + 8)]) :=
    hW1.trans hS2f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagS2 : Spec.Map.Agrees m1 S2.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 32)) (hi := (s.regs 4).toNat + 8) hS2f
      (Outside.of_sub hout (by omega) (by omega))
  have hS2ra : S2.mem.readLE (S2.regs 4).toNat 8 = 4746615 := by
    rw [hS2]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h32', Janus.Arm64.Memory.readLE_writeLE_self]
  have hS2i : S2.mem.readLE ((s.regs 4).toNat - 16) 8 = 1 := by
    rw [hS2]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  refine ReachesRet.call hdp hS2pc ⟨PanicPre.of_within hc hS2fW (hl.env_frame _ _ henv1 hagS2) (by omega) (by omega)
      (by omega) hS214 hS2x hS2df (by rw [hS2ra]; decide),
    by rw [hgS2, hl.room_frame _ _ _ hagS2]; omega⟩ ?_
  intro s2 hpc2 hq2
  obtain ⟨⟨r2, x2, y2, f2, m2, hs2, hfr2, henv2⟩, hdef2, hkeep2⟩ := hq2
  have hm2 : s2.mem = m2 := by rw [hs2]
  have hS20n : (S2.regs 0).toNat = fvA := by rw [hS20]; simp
  have hfsp2 : fspOf S2 = (s.regs 4).toNat - 24 := by simp only [fspOf, hS2spn]; omega
  have hd2 : P.defers m2 (gOf s) = { sp := (s.regs 4).toNat - 24, fns := [fvA] } ::
      { sp := (s.regs 4).toNat - 24, fns := [fvA] } :: P.defers s.mem (gOf s) := by
    have := hdef2; rw [hm2, hgS2, hfsp2, hS20n, hl.defers_frame _ _ _ hagS2, hd1] at this; exact this
  have hsv2 : P.saved m2 (gOf s) = none := by
    have := hkeep2.2.1; rw [hm2, hgS2, hl.saved_frame _ _ _ hagS2] at this; rw [this]; exact hsv1
  simp only [MapAmd64.calleeStack, hS2spn] at hfr2
  have hW2 := hstep S2 m2 hS2fW hS2spn (by simpa [MapAmd64.calleeStack, hS2spn] using hfr2)
  have hr8_2 : m2.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hfr2.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    rw [hS2]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact hr8_1
  have hrr_2 : m2.readLE (s.regs 4).toNat 8 = ret := by
    rw [hfr2.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    rw [hS2]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact hrr_1
  have hi2 : m2.readLE ((s.regs 4).toNat - 16) 8 = 1 := by
    rw [hfr2.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    exact hS2i
  clear hdef2 hkeep2 hS2f hS2fW hagS2 hS20 hS214 hS2x hS2df hS2pc hgS2 hS2sp hS2spn hS20n hm2 hpc2 hd1 hrm1 hsv1 hW1 henv1 hfr2 hS2i hS2ra hfsp2 hi1
  subst hs2
  subst hS2
  -- the exit: deferreturn
  janus64_run until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun S3 hS3 => ?_
  have hS3sp : S3.regs 4 = s.regs 4 - 32#64 := by rw [hS3] <;> simp [setRegF]
  have hS3spn : (S3.regs 4).toNat = (s.regs 4).toNat - 32 := by rw [hS3sp]; exact h32'
  have hS3f : MemFrame m2 S3.mem [((s.regs 4).toNat - (P.depth + 32), (s.regs 4).toNat + 8)] := by
    rw [hS3]; janus_frame
  have hS314 : S3.regs 14 = s.regs 14 := by rw [hS3] <;> simp [setRegF, MapAmd64.keepABI]
  have hS35 : S3.regs 5 = s.regs 4 - 8#64 := by rw [hS3] <;> simp [setRegF, MapAmd64.keepABI]
  have hS3x : S3.xmm 15 = 0 := by rw [hS3]; simpa [MapAmd64.keepX15] using h_x15
  have hS3df : S3.df = false := by rw [hS3]
  have hS3pc : S3.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by rw [hS3] <;> rfl
  have hgS3 : gOf S3 = gOf s := by simp only [gOf, hS314]
  have hS3fW : MemFrame s.mem S3.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 32), (s.regs 4).toNat + 8)]) :=
    hW2.trans hS3f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagS3 : Spec.Map.Agrees m2 S3.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 32)) (hi := (s.regs 4).toNat + 8) hS3f
      (Outside.of_sub hout (by omega) (by omega))
  have hS3ra : S3.mem.readLE (S3.regs 4).toNat 8 = 4746633 := by
    rw [hS3]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h32', Janus.Arm64.Memory.readLE_writeLE_self]
  have hr8_3 : S3.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hS3]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact hr8_2
  have hrr_3 : S3.mem.readLE (s.regs 4).toNat 8 = ret := by
    rw [hS3]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact hrr_2
  have hpre3 : PanicPre P 0 S3 := PanicPre.of_within hc hS3fW (hl.env_frame _ _ henv2 hagS3) (by omega) (by omega)
    (by omega) hS314 hS3x hS3df (by rw [hS3ra]; decide)
  have hsv3 : P.saved S3.mem (gOf S3) = none := by
    rw [hgS3, hl.saved_frame _ _ _ hagS3]; exact hsv2
  have hD3 : P.defers S3.mem (gOf S3) = { sp := (s.regs 4).toNat - 24, fns := [fvA] } ::
      { sp := (s.regs 4).toNat - 24, fns := [fvA] } :: P.defers s.mem (gOf s) := by
    rw [hgS3, hl.defers_frame _ _ _ hagS3, hd2]
  have hfsp3 : fspOf S3 = (s.regs 4).toNat - 24 := by simp only [fspOf, hS3spn]; omega
  have hF : retFrame P S3 = ⟨(s.regs 4).toNat - 24, (s.regs 4).toNat - 24, 0, none⟩ := by
    simp only [retFrame, hsv3, hfsp3]
  have hds' : ∀ d ∈ P.defers s.mem (gOf s), (s.regs 4).toNat - 24 < d.sp := fun d hd => by have := hds d hd; omega
  have hrA := recItems_above hds'
  have hI : frameItems S3.mem (retFrame P S3) (P.defers S3.mem (gOf S3)) =
      [{ fn := fvA, bits := none, chain := { sp := (s.regs 4).toNat - 24, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] := by
    rw [hF, hD3]
    simp [frameItems, recItems, fnItems, hrA]
  have hfvacc : s.mem.accessible fvA 8 false = true := fv_acc _ hd
  have hfv3 : S3.mem.readLE fvA 8 = func1A := by
    rw [hS3fW.readLE _ _ hfo]; exact fv_read _ hd
  have hFO : FrameOK P S3.mem (retFrame P S3) (frameItems S3.mem (retFrame P S3) (P.defers S3.mem (gOf S3))) := by
    rw [hI, hF]
    simp only [outside_append, outside_cons, outside_nil, and_true] at hfo
    refine ⟨⟨trivial, fun it hit => ?_⟩, fun it hit => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl <;> dsimp only <;>
        exact ⟨by decide, by rw [hS3fW.accessible]; exact hfvacc, by rw [hfv3], by rw [hfv3]; decide,
          hfo.1, by omega⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl <;> dsimp only <;> (rw [hfv3]; decide)
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
  obtain ⟨k1, e1, hst1, ⟨hpc1, h2_1, h14_1, hx1, hdf1, hal1, hlo1, hhi1, hra1, henvE1⟩,
    hfrE1, -, -, hpn1, -, -, hcont1, -⟩ := hE
  dsimp only at hpc1 h2_1 hlo1 hhi1 hra1 hfrE1 hcont1
  have hfv1 : e1.mem.readLE fvA 8 = func1A := hS3fv e1 (by rw [hF]; exact hfrE1)
  rw [hfv1] at hpc1
  have hacc1 : e1.mem.accessible (e1.regs 4).toNat 8 false = true := by
    rw [hfrE1.accessible, hS3fW.accessible]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by simp only [hfsp3] at *; omega) (by simp only [hfsp3] at *; omega))
  refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
  obtain ⟨j1', f1', hj1, -, hfrip1, hfr4_1, hfr14_1, hfr5_1, hfx1, hfdf1, hfm1⟩ := func1_ret impl e1 hpc1 hra1 hacc1
  refine GoReturns.of_steps (hj1.withExit hret.fetch_none) ?_
  have hra64 : e1.mem.readLE (e1.regs 4).toNat 8 < 2 ^ 64 := by omega
  obtain ⟨hdr1, hpf1⟩ := DeferReturned.of_same hl (g := S3.regs 14) (fsp := (s.regs 4).toNat - 24)
    (keep := frameKeep S3.mem ⟨(s.regs 4).toNat - 24, (s.regs 4).toNat - 24, 0, none⟩ _)
    (e := e1) (e' := f1')
    (by rw [hfrip1, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hra64) hfr4_1
    (by rw [hfr14_1]; exact h14_1) hfr5_1 (by rw [hfx1]; exact hx1) (by rw [hfdf1]; exact hdf1) hfm1 henvE1
  have hE1 := (hcont1 f1' hdr1).1 (hpf1.trans hpn1)
  rw [Engine_cons] at hE1
  obtain ⟨k2, e2, hst2, ⟨hpc2, h2_2, h14_2, hx2, hdf2, hal2, hlo2, hhi2, hra2, henvE2⟩,
    hfrE2, -, -, hpn2, -, -, hcont2, -⟩ := hE1
  dsimp only at hpc2 h2_2 hlo2 hhi2 hra2 hfrE2 hcont2
  have hfrE2' : MemFrame S3.mem e2.mem (P.priv ++ rtWin P (retFrame P S3) ++ bitsWin (retFrame P S3)) := by
    rw [hF]
    exact hfrE1.trans (by rw [← hfm1]; exact hfrE2) (fun a n h => ⟨h, h⟩)
  have hfv2 : e2.mem.readLE fvA 8 = func1A := hS3fv e2 hfrE2'
  rw [hfv2] at hpc2
  have hacc2 : e2.mem.accessible (e2.regs 4).toNat 8 false = true := by
    rw [hfrE2'.accessible, hS3fW.accessible]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by simp only [hfsp3] at *; omega) (by simp only [hfsp3] at *; omega))
  refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
  obtain ⟨j2', f2', hj2, -, hfrip2, hfr4_2, hfr14_2, hfr5_2, hfx2, hfdf2, hfm2⟩ := func1_ret impl e2 hpc2 hra2 hacc2
  refine GoReturns.of_steps (hj2.withExit hret.fetch_none) ?_
  have hra64' : e2.mem.readLE (e2.regs 4).toNat 8 < 2 ^ 64 := by omega
  obtain ⟨hdr2, hpf2⟩ := DeferReturned.of_same hl (g := S3.regs 14) (fsp := (s.regs 4).toNat - 24)
    (keep := frameKeep S3.mem ⟨(s.regs 4).toNat - 24, (s.regs 4).toNat - 24, 0, none⟩ _)
    (e := e2) (e' := f2')
    (by rw [hfrip2, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hra64') hfr4_2
    (by rw [hfr14_2]; exact h14_2) hfr5_2 (by rw [hfx2]; exact hx2) (by rw [hfdf2]; exact hdf2) hfm2 henvE2
  have hE2 := (hcont2 f2' hdr2).1 (hpf2.trans hpn2)
  rw [Engine_nil] at hE2
  obtain ⟨k3, d, hst3, hdpc, hdsp, hd14, hd5, hdx, hddf, hfrD, henvD, -⟩ := hE2
  refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
  have hSD : MemFrame S3.mem d.mem (P.priv ++ rtWin P (retFrame P S3) ++ bitsWin (retFrame P S3)) := by
    rw [hF] at hfrE2' ⊢
    rw [hF] at hfrD
    exact hfrE2'.trans (by rw [← hfm2]; exact hfrD) (fun a n h => ⟨h, h⟩)
  rw [hF] at hSD hfrD
  simp only [rtWin, bitsWin, List.append_nil, hS3spn] at hSD
  have hdR8 : d.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hSD.readLE ((s.regs 4).toNat - 8) 8 (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩)]; exact hr8_3
  have hdR : d.mem.readLE (s.regs 4).toNat 8 = ret := by
    rw [hSD.readLE (s.regs 4).toNat 8 (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩)]; exact hrr_3
  have hdacc8 : d.mem.accessible ((s.regs 4).toNat - 8) 16 true = true := by
    rw [hSD.accessible, hS3fW.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
  have hdpc' : d.rip = BitVec.ofNat 64 4746633 := by
    apply BitVec.eq_of_toNat_eq
    rw [hdpc, hS3ra, BitVec.toNat_ofNat]
  have hd4 : d.regs 4 = s.regs 4 - 24#64 := by
    rw [hdsp, hS3sp]; apply BitVec.eq_of_toNat_eq
    have := (s.regs 4).isLt
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_sub]
    simp; omega
  have hd5' : d.regs 5 = s.regs 4 - 8#64 := by rw [hd5, hS35]
  have hd14' : d.regs 14 = s.regs 14 := by rw [hd14, hS314]
  clear hdpc hdsp hd14 hd5 hfrD hfrE2 hfrE2' hfrE1 hcont1 hcont2 hfm1 hfm2 hpn1 hpn2 hst1 hst2 hst3 hdr1 hdr2 hpf1 hpf2
  refine GoReturns.of_reaches ?_
  janus64_run
  refine ⟨by rfl, hS3fW.trans hSD (fun a n h => ⟨h, ?_⟩), henvD⟩
  simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, by omega⟩

/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSatAmd64` (code
that `Janus.Contracts.PanicSatAmd64Entry` proves meets the `deferproc` and `deferreturn` contracts
in every program that contains it) linked into `DeferTwice`'s program with a `jmp` to it at each of
the two contract addresses, and a call state satisfying the precondition: so `correctness` applies
(`nonvacuous`), and `DeferTwice` returns from that state (`returns`). -/

namespace Witness

open Janus.Contracts.PanicSat (tabWords witMemD)
open Janus.Contracts.PanicSatAmd64
open Janus.Contracts.PanicModel

abbrev T0 : List Spec.FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : Spec.PanicRuntime := P0 T0 RPa

def dpA : Nat := Extracted.program.contractAddr "runtime.deferproc"
def drA : Nat := Extracted.program.contractAddr "runtime.deferreturn"

/-- The code linked next to `DeferTwice`: the model engine and a `jmp` to it at each contract
address. -/
def implW : List Janus.Amd64.Segment :=
  panicImpl Extracted.program [("runtime.deferproc", eDeferproc), ("runtime.deferreturn", eDeferreturn)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

set_option maxRecDepth 100000 in
theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubDp : StubAt (Extracted.program.link implW) dpA eDeferproc :=
  StubAt.of_jmp (bs := stubCode dpA eDeferproc) (rel := (eDeferproc + 2 ^ 64 - (dpA + 5)) % 2 ^ 64) (len := 5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubDr : StubAt (Extracted.program.link implW) drA eDeferreturn :=
  StubAt.of_jmp (bs := stubCode drA eDeferreturn) (rel := (eDeferreturn + 2 ^ 64 - (drA + 5)) % 2 ^ 64) (len := 5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem hdp : DeferprocContract (Extracted.program.link implW) dpA PW :=
  deferproc_at stubDp (deferproc_contract engineAt T0)

theorem hdr : DeferreturnContract (Extracted.program.link implW) drA PW U1 :=
  deferreturn_at stubDr (deferreturn_run (T := T0) engineAt)

def ret : Nat := 0x200000

/-- Memory: the model's table and runtime range writable, a stack `[0x40000, 0x50000)` holding the
return address `ret` at `[wsp]`, the goroutine readable, the program's read-only data in place. -/
def wm : Janus.Arm64.Memory := witMemD (tabWords T0 ++ [(wsp, ret)]) Extracted.data

theorem env_w : Env0 T0 wm := by
  unfold Env0
  have hnd : ndef wm = 0 := by decide
  refine ⟨by decide, by decide, by decide, fun i hi => ?_, ?_⟩
  · omega
  · unfold TableOK
    exact ⟨by decide, by decide, by decide⟩

theorem hret : RetAddr (Extracted.program.link implW) ret := RetAddr.of_check (by decide)

theorem dataLoaded : Extracted.program.DataLoaded wm := by
  unfold Janus.Amd64.Program.DataLoaded
  set_option maxRecDepth 100000 in decide

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wm }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h, rfl⟩

theorem pre : PanicCallerOK PW s0 32 8 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside fvA 8 (PW.priv ++ [((s0.regs regSP).toNat - (PW.depth + 32), (s0.regs regSP).toNat + 8)]) ∧
    2 ≤ PW.room s0.mem (gOf s0) ∧ PW.saved s0.mem (gOf s0) = none ∧
    ∀ d ∈ PW.defers s0.mem (gOf s0), (s0.regs regSP).toNat ≤ d.sp := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩,
    dataLoaded, ?_, ?_, ?_, ?_⟩
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
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime)
    (U : Janus.Amd64.State → Nat → Nat → Prop) (ret : Nat) (s : Janus.Amd64.State), P.Laws ∧
    DeferprocContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferproc") P ∧
    DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P U ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [] s ∧
    (PanicCallerOK P s 32 8 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside fvA 8 (P.priv ++ [((s.regs regSP).toNat - (P.depth + 32), (s.regs regSP).toNat + 8)]) ∧
      2 ≤ P.room s.mem (gOf s) ∧ P.saved s.mem (gOf s) = none ∧
      ∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp) :=
  ⟨implW, PW, U1, ret, s0, P0_laws T0 RPa, hdp, hdr, hret, setup, pre⟩

/-- So the guarantee is reached: `DeferTwice` returns from that state. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClass PW) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧
        (MemFrame s0.mem s'.mem
          (PW.priv ++ [((s0.regs regSP).toNat - (PW.depth + 32), (s0.regs regSP).toNat + 8)]) ∧ PW.Env s'.mem)
    | .panicked v s' => False
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U1 hdp hdr ret hret s0 setup pre

end Witness

end Proof
