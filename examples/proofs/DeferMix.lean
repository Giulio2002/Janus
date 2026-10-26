import Extracted

/-!
# `DeferMix(x uint64, e any) uint64`: a stack defer and two heap defers, run in LIFO order (arm64)

`DeferMix` is `defer accAdd1(); for i := 0; i < 2; i++ { defer accAdd2() }; if x > 10 { panic(e) }; return x`.
A defer in a loop disables open-coding for the whole function, so the first defer is a stack
`_defer` record (`runtime.deferprocStack`) and the two in the loop are heap records
(`runtime.deferproc`). On return `runtime.deferreturn` runs them, on `panic(e)` `runtime.gopanic`
does, in LIFO order: the two heap records, then the stack record. `accAdd1` / `accAdd2` append the
digit 1 / 2 to the package variable `Acc` (`Acc = Acc*10 + d`).

**Guarantee (example 5 of docs/COVERAGE.md R6).** For every panic-runtime model `P` satisfying its
laws, every implementation of `runtime.deferprocStack`, `runtime.deferproc`, `runtime.gopanic` and
`runtime.deferreturn` meeting their contracts (`Janus.Contracts.Panic`, pinned to the Go 1.26
runtime's code), every admissible return address and every call state in which the runtime is
usable with room for four records, `Acc` is a writable word and the funcvals of the two deferred
functions are in memory (all outside the runtime's memory and the stack window):

* if `x ≤ 10` the call **returns `x`**;
* if `x > 10` the call **panics with `e`**;

and in both cases `Acc` ends as `((Acc*10+2)*10+2)*10+1` (mod `2^64`): the deferred calls ran in
LIFO order, the deferred code being the program's own (`accAdd1`, `accAdd2`).

`Acc` lives in `.noptrbss`, whose content the binary does not fix, so the extractor does not copy it
and the proof's precondition provides the word (`accA`, the address the compiled code accesses).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Proof

/-- The address of `example.com/basic.Acc` (`.noptrbss`; the extractor does not copy it). -/
local macro "accA" : term => `((1704656 : Nat))

local macro "fvA" : term => `(janus_eval% (Extracted.program.data.head!.base))
local macro "accAdd1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.accAdd1"))
local macro "accAdd2A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.accAdd2"))

def digit (k v : Nat) : Nat := (v * 10 + k) % 2 ^ 64

/-- `accAdd2` run from `e`: it appends the digit 2 to `Acc` and returns. -/
theorem call_acc2 (impl : List Segment) (e : State) (hpc : e.pc = BitVec.ofNat 64 accAdd2A)
    (hacc : e.mem.accessible accA 8 true = true) (hl4 : (e.regs 30).toNat % 4 = 0)
    (hl48 : (e.regs 30).toNat < 2 ^ 48) :
    ReachesRet (Extracted.program.link impl) (e.regs 30) e (fun e' =>
      e'.pc = e.regs 30 ∧ e'.sp = e.sp ∧ e'.regs 28 = e.regs 28 ∧ e'.regs 18 = e.regs 18 ∧
      MemFrame e.mem e'.mem [(accA, accA + 8)] ∧ e'.mem.readLE accA 8 = digit 2 (e.mem.readLE accA 8)) := by
  janus_run
  refine ⟨MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega), ?_⟩
  try rw [Memory.readLE_writeLE_self]
  simp only [digit]; omega

/-- `accAdd1` run from `e`: it appends the digit 1 to `Acc` and returns. -/
theorem call_acc1 (impl : List Segment) (e : State) (hpc : e.pc = BitVec.ofNat 64 accAdd1A)
    (hacc : e.mem.accessible accA 8 true = true) (hl4 : (e.regs 30).toNat % 4 = 0)
    (hl48 : (e.regs 30).toNat < 2 ^ 48) :
    ReachesRet (Extracted.program.link impl) (e.regs 30) e (fun e' =>
      e'.pc = e.regs 30 ∧ e'.sp = e.sp ∧ e'.regs 28 = e.regs 28 ∧ e'.regs 18 = e.regs 18 ∧
      MemFrame e.mem e'.mem [(accA, accA + 8)] ∧ e'.mem.readLE accA 8 = digit 1 (e.mem.readLE accA 8)) := by
  janus_run
  refine ⟨MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega), ?_⟩
  try rw [Memory.readLE_writeLE_self]
  simp only [digit]; omega

/-- The three deferred calls in LIFO order: the two heap records, then the stack record. -/
def mix (v : Nat) : Nat := digit 1 (digit 2 (digit 2 v))

set_option maxRecDepth 100000 in
theorem fv1_read (m : Memory) (hd : Extracted.program.DataLoaded m) : m.readLE fvA 8 = accAdd1A :=
  readLE_of_dataRead hd (by decide)
set_option maxRecDepth 100000 in
theorem fv2_read (m : Memory) (hd : Extracted.program.DataLoaded m) : m.readLE (fvA + 8) 8 = accAdd2A :=
  readLE_of_dataRead hd (by decide)
set_option maxRecDepth 100000 in
theorem fv_acc (m : Memory) (hd : Extracted.program.DataLoaded m) : m.accessible fvA 16 false = true :=
  accessible_of_dataRead hd (by decide)


/-- The slots a runtime call leaves alone: the arguments `x`, `e` in the caller's spill area, the
saved return address and frame pointer. -/
def Fx (s : State) (m : Memory) (x etyp edata : BitVec 64) (ret : Nat) : Prop :=
  m.readLE (s.sp.toNat + 8) 8 = x.toNat ∧ m.readLE (s.sp.toNat + 16) 8 = etyp.toNat ∧
    m.readLE (s.sp.toNat + 24) 8 = edata.toNat ∧ m.readLE (s.sp.toNat - 96) 8 = ret ∧
    m.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat

theorem Fx.step {P : PanicRuntime} {s S : State} {m m' : Memory} {ex : List (Nat × Nat)}
    {x etyp edata : BitVec 64} {ret : Nat} (h : Fx s m x etyp edata ret)
    (hsp : S.sp.toNat = s.sp.toNat - 96)
    (hout : Outside (s.sp.toNat - (P.depth + 96)) (P.depth + 96 + 32) P.priv) (hd : 8 ≤ P.depth) (hlo : P.depth + 96 ≤ s.sp.toNat)
    (hex : ex = [] ∨ ex = [(s.sp.toNat - 56, s.sp.toNat - 56 + 48)])
    (hfr : MemFrame m m' (P.priv ++ calleeStack S P.depth 1 ++ ex)) : Fx s m' x etyp edata ret := by
  have hO : ∀ a, s.sp.toNat - (P.depth + 96) ≤ a → a + 8 ≤ s.sp.toNat + 32 →
      (a + 8 ≤ s.sp.toNat - 96 - P.depth ∨ s.sp.toNat - 104 ≤ a) → (a + 8 ≤ s.sp.toNat - 88 ∨ s.sp.toNat - 80 ≤ a) →
      (a + 8 ≤ s.sp.toNat - 56 ∨ s.sp.toNat - 8 ≤ a) →
      Outside a 8 (P.priv ++ calleeStack S P.depth 1 ++ ex) := by
    intro a h1 h2 h3 h4 h5
    have hp : Outside a 8 P.priv := Outside.of_sub hout (by omega) (by omega)
    simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack, hsp]
    rcases hex with rfl | rfl
    · simp only [outside_nil, and_true]
      exact ⟨hp, by omega, by omega⟩
    · simp only [outside_cons, outside_nil, and_true]
      exact ⟨⟨hp, by omega, by omega⟩, by omega⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [hfr.readLE _ _ (hO _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact h1,
    by rw [hfr.readLE _ _ (hO _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact h2,
    by rw [hfr.readLE _ _ (hO _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact h3,
    by rw [hfr.readLE _ _ (hO _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact h4,
    by rw [hfr.readLE _ _ (hO _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact h5⟩

/-- The state at the loop exit (after the stack record and the two heap records are deferred). -/
def AfterDefers (P : PanicRuntime) (s S : State) (x etyp edata : BitVec 64) (ret : Nat) : Prop :=
  S.pc = BitVec.ofNat 64 (Extracted.entry + 0x7c) ∧ S.sp = s.sp - 96#64 ∧ S.regs 28 = s.regs 28 ∧
    S.regs 18 = s.regs 18 ∧
    MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) ∧ P.Env S.mem ∧
    P.defers S.mem (gOf s) =
      [{ sp := s.sp.toNat - 96, fns := [fvA + 8] }, { sp := s.sp.toNat - 96, fns := [fvA + 8] },
       { sp := s.sp.toNat - 96, fns := [fvA] }] ++ P.defers s.mem (gOf s) ∧
    P.saved S.mem (gOf s) = none ∧ P.panics S.mem (gOf s) = P.panics s.mem (gOf s) ∧
    P.room s.mem (gOf s) ≤ P.room S.mem (gOf s) + 3 ∧
    Fx s S.mem x etyp edata ret

/-- What the runtime and the deferred calls write: `P.priv`, the runtime's window below the frame,
and `Acc`. -/
abbrev winA (P : PanicRuntime) (s : State) : List (Nat × Nat) :=
  P.priv ++ [(s.sp.toNat - 96 - P.depth, s.sp.toNat - 96 - 8), (accA, accA + 8)]

set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hds : DeferprocStackContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferprocStack") P)
    (hdp : DeferprocContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferproc") P)
    (hpan : GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U)
    (x etyp edata : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [x, etyp, edata]
      (fun s => PanicCallerOK P s 96 32 ∧ Extracted.program.DataLoaded s.mem ∧
        s.mem.accessible accA 8 true = true ∧
        Outside accA 8 (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) ∧
        Outside fvA 16 (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) ∧
        etyp.toNat ≠ 0 ∧ 4 ≤ P.room s.mem (gOf s) ∧
        P.saved s.mem (gOf s) = none ∧ ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp)
      (goClassU P U)
      (fun s s' => x.toNat ≤ 10 ∧ (s'.regs 0).toNat = x.toNat ∧
        s'.mem.readLE accA 8 = mix (s.mem.readLE accA 8))
      (fun s v s' => 10 < x.toNat ∧ v = ⟨etyp.toNat, edata.toNat⟩ ∧
        s'.mem.readLE accA 8 = mix (s.mem.readLE accA 8)) := by
  intro ret hret s hs ⟨hc, hd, hacc, hao, hfo, hne, hroom, hsave, hdss⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd', hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd
  have h96 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := by rw [BitVec.toNat_sub]; simp; omega
  have hagw : ∀ m, MemFrame s.mem m [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)] → Map.Agrees s.mem m P.priv :=
    fun m hf => Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 96)) (hi := s.sp.toNat + 32) hf
      (Outside.of_sub hout (by omega) (by omega))
  have hprefix : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x7c)) s
      (fun S => AfterDefers P s S x etyp edata ret) := by
    -- the stack record
    janus_run until [Extracted.program.contractAddr "runtime.deferprocStack"]
    refine ReachesRet.name fun S hS => ?_
    have hSsp : S.sp = s.sp - 96#64 := by rw [hS] <;> rfl
    have hSspn : S.sp.toNat = s.sp.toNat - 96 := by rw [hSsp]; exact h96
    have hSf : MemFrame s.mem S.mem [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)] := by rw [hS]; janus_frame
    have hS0 : S.regs 0 = s.sp - 56#64 := by rw [hS] <;> rfl
    have hS0n : (S.regs 0).toNat = s.sp.toNat - 56 := by rw [hS0, BitVec.toNat_sub]; simp; omega
    have hS28 : S.regs 28 = s.regs 28 := by rw [hS] <;> rfl
    have hS18 : S.regs 18 = s.regs 18 := by rw [hS] <;> rfl
    have hS30 : S.regs 30 = BitVec.ofNat 64 597740 := by rw [hS] <;> rfl
    have hSpc : S.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferprocStack") := by rw [hS] <;> rfl
    have hgS : gOf S = gOf s := by simp only [gOf, hS28]
    have hagS : Map.Agrees s.mem S.mem P.priv := hagw _ hSf
    have hSfW : MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) :=
      hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
    have hr48 : ret < 2 ^ 48 := hret.user
    have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    have hFx0 : Fx s S.mem x etyp edata ret := by
      rw [hS]; unfold Fx
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      · rw [h64]; exact Nat.mod_eq_of_lt x.isLt
      · rw [h64]; exact Nat.mod_eq_of_lt etyp.isLt
      · rw [h64]; exact Nat.mod_eq_of_lt edata.isLt
      · rw [h64]; exact Nat.mod_eq_of_lt (by omega)
      · rw [h64]; exact Nat.mod_eq_of_lt (s.regs 29).isLt
    have hfn0 : S.mem.readLE ((S.regs 0).toNat + 24) 8 = fvA := by
      rw [hS0n, show s.sp.toNat - 56 + 24 = s.sp.toNat - 32 by omega, hS]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      try decide
    refine ReachesRet.call hds hSpc ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
        (by rw [hSspn]; omega) hS28 (by rw [hS30]; decide) (by rw [hS30]; decide),
      by rw [hgS, hl.room_frame _ _ _ hagS]; omega, by omega, ?_, ?_⟩ ?_
    · rw [hS0n, hSf.accessible]
      exact Memory.accessible_mono _ hst (by omega) (by omega)
    · rw [hS0n]; exact Outside.of_sub hout (by omega) (by omega)
    intro s1 hpc1 hq1
    obtain ⟨⟨j1, f1, v1, m1, hs1, hfr1, henv1⟩, hdef1, hpan1, hsav1, hrp1, hroom1⟩ := hq1
    have hm1 : s1.mem = m1 := by rw [hs1]; rfl
    have hd1 : P.defers m1 (gOf s) = { sp := s.sp.toNat - 96, fns := [fvA] } :: P.defers s.mem (gOf s) := by
      have := hdef1; rw [hm1, hgS, hSspn, hfn0, hl.defers_frame _ _ _ hagS] at this; exact this
    have hsv1 : P.saved m1 (gOf s) = none := by
      have := hsav1; rw [hm1, hgS, hl.saved_frame _ _ _ hagS] at this; rw [this]; exact hsave
    have hrm1 : P.room s.mem (gOf s) ≤ P.room m1 (gOf s) + 1 := by
      have := hroom1; rw [hm1, hgS, hl.room_frame _ _ _ hagS] at this; exact this
    have hstep : ∀ (S : State) (m : Memory) (ex : List (Nat × Nat)),
        MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) →
        S.sp.toNat = s.sp.toNat - 96 →
        (∀ a n, Outside a n [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)] → Outside a n ex) →
        MemFrame S.mem m (P.priv ++ calleeStack S P.depth 1 ++ ex) →
        MemFrame s.mem m (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) := by
      intro S m ex h1 h2 h3 h4
      refine h1.trans h4 fun a n h => ⟨h, ?_⟩
      have h' := h
      simp only [outside_append] at h' ⊢
      obtain ⟨h5, h6⟩ := h'
      refine ⟨⟨h5, ?_⟩, h3 a n h6⟩
      simp only [outside_cons, outside_nil, and_true, calleeStack, h2] at h6 ⊢
      omega
    rw [hS0n] at hfr1
    have hW1 := hstep S m1 [(s.sp.toNat - 56, s.sp.toNat - 56 + 48)] hSfW hSspn (fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega) hfr1
    have hfr1' : MemFrame S.mem m1 (P.priv ++ calleeStack S P.depth 1 ++ [(s.sp.toNat - 56, s.sp.toNat - 56 + 48)]) := hfr1
    have hFx1 : Fx s m1 x etyp edata ret := Fx.step (S := S) hFx0 hSspn hout hd8 hd' (Or.inr rfl) hfr1'
    have hpn1 : P.panics m1 (gOf s) = P.panics s.mem (gOf s) := by
      have := hpan1; rw [hm1, hgS, hl.panics_frame _ _ _ hagS] at this; exact this
    clear hdef1 hpan1 hsav1 hrp1 hroom1 hSf hSfW hagS hS0 hS0n hS28 hS18 hS30 hSpc hgS hSsp hSspn hm1 hpc1 hfn0 hfr1
    subst hs1
    subst hS
    -- first loop iteration: deferproc
    janus_run until [Extracted.program.contractAddr "runtime.deferproc"]
    refine ReachesRet.name fun S2 hS2 => ?_
    have hS2sp : S2.sp = s.sp - 96#64 := by rw [hS2] <;> rfl
    have hS2spn : S2.sp.toNat = s.sp.toNat - 96 := by rw [hS2sp]; exact h96
    have hS2f : MemFrame m1 S2.mem [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)] := by rw [hS2]; janus_frame
    have hS20 : S2.regs 0 = BitVec.ofNat 64 (fvA + 8) := by rw [hS2] <;> rfl
    have hS228 : S2.regs 28 = s.regs 28 := by rw [hS2] <;> rfl
    have hS218 : S2.regs 18 = s.regs 18 := by rw [hS2] <;> rfl
    have hS230 : S2.regs 30 = BitVec.ofNat 64 597800 := by rw [hS2] <;> rfl
    have hS2pc : S2.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferproc") := by rw [hS2] <;> rfl
    have hS2i : S2.mem.readLE (s.sp.toNat - 64) 8 = 0 := by
      rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    have hgS2 : gOf S2 = gOf s := by simp only [gOf, hS228]
    have hS2fW : MemFrame s.mem S2.mem (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) :=
      hW1.trans hS2f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
    have hagS2 : Map.Agrees m1 S2.mem P.priv :=
      Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 96)) (hi := s.sp.toNat + 32) hS2f
        (Outside.of_sub hout (by omega) (by omega))
    refine ReachesRet.call hdp hS2pc ⟨PanicPre.of_within hc hS2fW (hl.env_frame _ _ henv1 hagS2) (by omega) (by omega)
        (by rw [hS2spn]; omega) hS228 (by rw [hS230]; decide) (by rw [hS230]; decide),
      by rw [hgS2, hl.room_frame _ _ _ hagS2]; omega⟩ ?_
    intro s2 hpc2 hq2
    obtain ⟨⟨j2, f2, v2, m2, hs2, hfr2, henv2⟩, hdef2, hpan2, hsav2, hrp2, hroom2⟩ := hq2
    have hm2 : s2.mem = m2 := by rw [hs2]; rfl
    have hS20n : (S2.regs 0).toNat = fvA + 8 := by rw [hS20]; simp
    have hd2 : P.defers m2 (gOf s) = { sp := s.sp.toNat - 96, fns := [fvA + 8] } ::
        { sp := s.sp.toNat - 96, fns := [fvA] } :: P.defers s.mem (gOf s) := by
      have := hdef2; rw [hm2, hgS2, hS2spn, hS20n, hl.defers_frame _ _ _ hagS2, hd1] at this; exact this
    have hsv2 : P.saved m2 (gOf s) = none := by
      have := hsav2; rw [hm2, hgS2, hl.saved_frame _ _ _ hagS2] at this; rw [this]; exact hsv1
    have hpn2 : P.panics m2 (gOf s) = P.panics s.mem (gOf s) := by
      have := hpan2; rw [hm2, hgS2] at this; rw [this, hl.panics_frame _ _ _ hagS2, hpn1]
    have hrm2 : P.room s.mem (gOf s) ≤ P.room m2 (gOf s) + 2 := by
      have := hroom2; rw [hm2, hgS2, hl.room_frame _ _ _ hagS2] at this; omega
    have hW2 := hstep S2 m2 [] hS2fW hS2spn (fun a n h => by simp only [outside_nil]) (by simpa using hfr2)
    have hFx2' : Fx s S2.mem x etyp edata ret := by
      rw [hS2]; unfold Fx at hFx1 ⊢
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hFx1
    have hFx2 : Fx s m2 x etyp edata ret := Fx.step (S := S2) hFx2' hS2spn hout hd8 hd' (Or.inl rfl) (by rw [List.append_nil]; exact hfr2)
    have hi2 : m2.readLE (s.sp.toNat - 64) 8 = 0 := by
      rw [hfr2.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack, hS2spn]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
      exact hS2i
    clear hdef2 hpan2 hsav2 hrp2 hroom2 hS2f hS2fW hagS2 hS20 hS228 hS218 hS230 hS2pc hgS2 hS2sp hS2spn hS20n hm2 hpc2 hd1 hrm1 hsv1 hpn1 hW1 henv1 hfr2 hS2i hFx1
    subst hs2
    subst hS2
    -- second loop iteration: deferproc
    janus_run [hi2] until [Extracted.program.contractAddr "runtime.deferproc"]
    refine ReachesRet.name fun S3 hS3 => ?_
    have hS3sp : S3.sp = s.sp - 96#64 := by rw [hS3] <;> rfl
    have hS3spn : S3.sp.toNat = s.sp.toNat - 96 := by rw [hS3sp]; exact h96
    have hS3f : MemFrame m2 S3.mem [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)] := by rw [hS3]; janus_frame
    have hS30 : S3.regs 0 = BitVec.ofNat 64 (fvA + 8) := by rw [hS3] <;> rfl
    have hS328 : S3.regs 28 = s.regs 28 := by rw [hS3] <;> rfl
    have hS318 : S3.regs 18 = s.regs 18 := by rw [hS3] <;> rfl
    have hS330 : S3.regs 30 = BitVec.ofNat 64 597800 := by rw [hS3] <;> rfl
    have hS3pc : S3.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferproc") := by rw [hS3] <;> rfl
    have hS3i : S3.mem.readLE (s.sp.toNat - 64) 8 = 1 := by
      rw [hS3]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    have hgS3 : gOf S3 = gOf s := by simp only [gOf, hS328]
    have hS3fW : MemFrame s.mem S3.mem (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) :=
      hW2.trans hS3f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
    have hagS3 : Map.Agrees m2 S3.mem P.priv :=
      Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 96)) (hi := s.sp.toNat + 32) hS3f
        (Outside.of_sub hout (by omega) (by omega))
    refine ReachesRet.call hdp hS3pc ⟨PanicPre.of_within hc hS3fW (hl.env_frame _ _ henv2 hagS3) (by omega) (by omega)
        (by rw [hS3spn]; omega) hS328 (by rw [hS330]; decide) (by rw [hS330]; decide),
      by rw [hgS3, hl.room_frame _ _ _ hagS3]; omega⟩ ?_
    intro s3 hpc3 hq3
    obtain ⟨⟨j3, f3, v3, m3, hs3, hfr3, henv3⟩, hdef3, hpan3, hsav3, hrp3, hroom3⟩ := hq3
    have hm3 : s3.mem = m3 := by rw [hs3]; rfl
    have hS30n : (S3.regs 0).toNat = fvA + 8 := by rw [hS30]; simp
    have hd3 : P.defers m3 (gOf s) = { sp := s.sp.toNat - 96, fns := [fvA + 8] } :: { sp := s.sp.toNat - 96, fns := [fvA + 8] } ::
        { sp := s.sp.toNat - 96, fns := [fvA] } :: P.defers s.mem (gOf s) := by
      have := hdef3; rw [hm3, hgS3, hS3spn, hS30n, hl.defers_frame _ _ _ hagS3, hd2] at this; exact this
    have hsv3 : P.saved m3 (gOf s) = none := by
      have := hsav3; rw [hm3, hgS3, hl.saved_frame _ _ _ hagS3] at this; rw [this]; exact hsv2
    have hpn3 : P.panics m3 (gOf s) = P.panics s.mem (gOf s) := by
      have := hpan3; rw [hm3, hgS3] at this; rw [this, hl.panics_frame _ _ _ hagS3, hpn2]
    have hrm3 : P.room s.mem (gOf s) ≤ P.room m3 (gOf s) + 3 := by
      have := hroom3; rw [hm3, hgS3, hl.room_frame _ _ _ hagS3] at this; omega
    have hW3 := hstep S3 m3 [] hS3fW hS3spn (fun a n h => by simp only [outside_nil]) (by simpa using hfr3)
    have hFx3' : Fx s S3.mem x etyp edata ret := by
      rw [hS3]; unfold Fx at hFx2 ⊢
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hFx2
    have hFx3 : Fx s m3 x etyp edata ret := Fx.step (S := S3) hFx3' hS3spn hout hd8 hd' (Or.inl rfl) (by rw [List.append_nil]; exact hfr3)
    have hi3 : m3.readLE (s.sp.toNat - 64) 8 = 1 := by
      rw [hfr3.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack, hS3spn]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
      exact hS3i
    clear hdef3 hpan3 hsav3 hrp3 hroom3 hS3f hS3fW hagS3 hS30 hS328 hS318 hS330 hS3pc hgS3 hS3sp hS3spn hS30n hm3 hpc3 hd2 hrm2 hsv2 hpn2 hW2 henv2 hfr3 hS3i hFx2 hi2 hstep
    subst hs3
    subst hS3
    janus_run [hi3] until [Extracted.entry + 0x7c]
    refine ReachesRet.done rfl ?_
    exact ⟨rfl, rfl, rfl, rfl, hW3, henv3, hd3, hsv3, hpn3, hrm3, hFx3⟩
  obtain ⟨k0, S, hst0, hpc0, hQ⟩ := hprefix
  obtain ⟨-, hSsp, hS28, hS18, hW, henvS, hdefS, hsvS, hpnS, hrmS, hFx⟩ := hQ
  refine GoReturns.of_steps (hst0.withExit hret.fetch_none) ?_
  have hSspn : S.sp.toNat = s.sp.toNat - 96 := by rw [hSsp]; exact h96
  have hx0 : S.mem.readLE (s.sp.toNat + 8) 8 = x.toNat := hFx.1
  have hx1 : S.mem.readLE (s.sp.toNat + 16) 8 = etyp.toNat := hFx.2.1
  have hx2 : S.mem.readLE (s.sp.toNat + 24) 8 = edata.toNat := hFx.2.2.1
  have hxl : S.mem.readLE (s.sp.toNat - 96) 8 = ret := hFx.2.2.2.1
  have hxf : S.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat := hFx.2.2.2.2
  have hSacc : S.mem.accessible (s.sp.toNat - (P.depth + 96)) (P.depth + 96 + 32) true = true := by
    rw [hW.accessible]; exact hst
  have hr48 : ret < 2 ^ 48 := hret.user
  have hra : ret % 4 = 0 := hret.aligned
  have hxlt := x.isLt
  have hao2 : accA + 8 ≤ s.sp.toNat - (P.depth + 96) ∨ s.sp.toNat + 32 ≤ accA := by
    have h := hao
    simp only [outside_append, outside_cons, outside_nil, and_true] at h
    exact h.2
  by_cases hx : x.toNat ≤ 10
  · refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn"))
      hret.fetch_none ?_
    janus_run [hx0, hx] until [Extracted.program.contractAddr "runtime.deferreturn"]
    refine ReachesRet.done rfl ?_
    refine GoReturns.name fun D hD => ?_
    have hDsp : D.sp = s.sp - 96#64 := by rw [hD]
    have hDspn : D.sp.toNat = s.sp.toNat - 96 := by rw [hDsp]; exact h96
    have hDf : MemFrame S.mem D.mem [(s.sp.toNat - 72, s.sp.toNat - 72 + 8)] := by rw [hD]; janus_frame
    have hD28 : D.regs 28 = s.regs 28 := by rw [hD]; simp [setReg]; exact hS28
    have hD18 : D.regs 18 = s.regs 18 := by rw [hD]; simp [setReg]; exact hS18
    have hD30 : D.regs 30 = BitVec.ofNat 64 597824 := by rw [hD]; simp [setReg]
    have hDpc : D.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by rw [hD] <;> rfl
    have hgD : gOf D = gOf s := by simp only [gOf, hD28]
    have hDfW : MemFrame s.mem D.mem (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) :=
      hW.trans hDf fun a n h => ⟨h, by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
        omega⟩
    have hagD : Map.Agrees S.mem D.mem P.priv :=
      Map.Agrees.of_window (lo := s.sp.toNat - 72) (hi := s.sp.toNat - 72 + 8) hDf
        (Outside.of_sub hout (by omega) (by omega))
    have hlr : (D.regs 30).toNat % 4 = 0 ∧ (D.regs 30).toNat < 2 ^ 48 := by rw [hD30]; decide
    have hpre : PanicPre P 0 D := PanicPre.of_within hc hDfW (hl.env_frame _ _ henvS hagD) (by omega) (by omega)
      (by rw [hDspn]; omega) hD28 hlr.1 hlr.2
    have hsvD : P.saved D.mem (gOf D) = none := by rw [hgD, hl.saved_frame _ _ _ hagD]; exact hsvS
    have hdD : P.defers D.mem (gOf D) = [{ sp := s.sp.toNat - 96, fns := [fvA + 8] },
        { sp := s.sp.toNat - 96, fns := [fvA + 8] }, { sp := s.sp.toNat - 96, fns := [fvA] }] ++
        P.defers s.mem (gOf s) := by
      rw [hgD, hl.defers_frame _ _ _ hagD]; exact hdefS
    have hF : retFrame P D = ⟨s.sp.toNat - 96, s.sp.toNat - 96, 0, none⟩ := by
      simp only [retFrame, hsvD, hDspn]
    have hds' : ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat - 96 < d.sp := fun d hd => by have := hdss d hd; omega
    have hrA := recItems_above hds'
    have hI : frameItems D.mem (retFrame P D) (P.defers D.mem (gOf D)) =
        [{ fn := fvA + 8, bits := none, chain := { sp := s.sp.toNat - 96, fns := [fvA + 8] } ::
            { sp := s.sp.toNat - 96, fns := [fvA] } :: P.defers s.mem (gOf s) },
         { fn := fvA + 8, bits := none, chain := { sp := s.sp.toNat - 96, fns := [fvA] } :: P.defers s.mem (gOf s) },
         { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] := by
      rw [hF, hdD]
      simp [frameItems, recItems, fnItems, hrA]
    have hfo1 : Outside fvA 8 (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) :=
      Outside.of_sub hfo (by omega) (by omega)
    have hfo2 : Outside (fvA + 8) 8 (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) :=
      Outside.of_sub hfo (by omega) (by omega)
    have hfv1 : D.mem.readLE fvA 8 = accAdd1A := by rw [hDfW.readLE _ _ hfo1]; exact fv1_read _ hd
    have hfv2 : D.mem.readLE (fvA + 8) 8 = accAdd2A := by rw [hDfW.readLE _ _ hfo2]; exact fv2_read _ hd
    have hfa1 : D.mem.accessible fvA 8 false = true := by
      rw [hDfW.accessible]; exact Memory.accessible_mono _ (fv_acc _ hd) (by omega) (by omega)
    have hfa2 : D.mem.accessible (fvA + 8) 8 false = true := by
      rw [hDfW.accessible]; exact Memory.accessible_mono _ (fv_acc _ hd) (by omega) (by omega)
    have hFO : FrameOK P D.mem (retFrame P D) (frameItems D.mem (retFrame P D) (P.defers D.mem (gOf D))) := by
      rw [hI, hF]
      simp only [outside_append, outside_cons, outside_nil, and_true] at hfo
      refine ⟨trivial, fun it hit => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl | rfl <;> dsimp only
      · exact ⟨by omega, hfa2, by rw [hfv2] <;> decide, by rw [hfv2] <;> decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
      · exact ⟨by omega, hfa2, by rw [hfv2] <;> decide, by rw [hfv2] <;> decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
      · exact ⟨by omega, hfa1, by rw [hfv1] <;> decide, by rw [hfv1] <;> decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
    have hpaD : D.mem.accessible accA 8 true = true := by rw [hDfW.accessible]; exact hacc
    have hv0 : D.mem.readLE accA 8 = s.mem.readLE accA 8 := hDfW.readLE _ _ hao
    have hKp : frameKeep D.mem ⟨s.sp.toNat - 96, s.sp.toNat - 96, 0, none⟩
        [{ fn := fvA + 8, bits := none, chain := { sp := s.sp.toNat - 96, fns := [fvA + 8] } ::
            { sp := s.sp.toNat - 96, fns := [fvA] } :: P.defers s.mem (gOf s) },
         { fn := fvA + 8, bits := none, chain := { sp := s.sp.toNat - 96, fns := [fvA] } :: P.defers s.mem (gOf s) },
         { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] =
        [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)] := by
      simp [frameKeep, Frame.openAt]
    have hsubR : ∀ a n, Outside a n (winA P s) →
        Outside a n (P.priv ++ rtWin P ⟨s.sp.toNat - 96, s.sp.toNat - 96, 0, none⟩ ++
          bitsWin ⟨s.sp.toNat - 96, s.sp.toNat - 96, 0, none⟩) := by
      intro a n h
      simp only [winA, rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at h ⊢
      exact ⟨h.1, h.2.1⟩
    have hoT : Outside accA 8 (P.priv ++ rtWin P ⟨s.sp.toNat - 96, s.sp.toNat - 96, 0, none⟩ ++
        bitsWin ⟨s.sp.toNat - 96, s.sp.toNat - 96, 0, none⟩) := by
      have hao' := hao
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at hao' ⊢
      exact ⟨hao'.1, by omega⟩
    have hsubA : ∀ a n, Outside a n (winA P s) → Outside a n [(accA, accA + 8)] := by
      intro a n h
      simp only [winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact h.2.2
    have hoA : ∀ (e : State), P.depth ≥ 0 → (s.sp.toNat - 96 - P.depth ≤ e.sp.toNat) →
        Outside accA (accA + 8 - accA) (P.priv ++ (e.sp.toNat, s.sp.toNat - 96) ::
          [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) := by
      intro e _ hlo
      have hao' := hao
      simp only [outside_append, outside_cons, outside_nil, and_true] at hao' ⊢
      simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hao'.1, by omega, by omega, by omega, by omega⟩
    refine DeferreturnContract.apply (S := D) hdr hDpc ⟨hpre, hFO⟩ ?_
    intro hE
    rw [hI, hF] at hE
    rw [hKp] at hE
    -- the first deferred call (the last heap record): `Acc = Acc*10 + 2`
    rw [Engine_cons] at hE
    obtain ⟨k1, e1, hst1, ⟨hpc1, h26_1, h28_1, h18_1, h29_1, hal1, hlo1, hhi1, h30a1, h30b1, henvE1⟩,
      hfrE1, -, -, hpn1, -, -, hcont1, -⟩ := hE
    dsimp only at hpc1 h26_1 hlo1 hhi1 hfrE1 hcont1
    refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
    have hae1 : MemFrame D.mem e1.mem (winA P s) := hfrE1.mono hsubR
    have hm1 : e1.mem.readLE (fvA + 8) 8 = accAdd2A := by
      rw [hae1.readLE _ _ (by
        simp only [winA, outside_append, outside_cons, outside_nil, and_true]
        have h2 := hfo2
        simp only [outside_append, outside_cons, outside_nil, and_true] at h2
        exact ⟨h2.1, by omega, by omega⟩)]
      exact hfv2
    have hv1 : e1.mem.readLE accA 8 = s.mem.readLE accA 8 := by rw [hfrE1.readLE _ _ hoT]; exact hv0
    rw [hm1] at hpc1
    have hpa1 : e1.mem.accessible accA 8 true = true := by rw [hae1.accessible]; exact hpaD
    have hcl1 := call_acc2 impl e1 hpc1 hpa1 h30a1 h30b1
    obtain ⟨j1, f1, hj1, -, hfpc1, hfsp1, hf281, hf181, hff1, hpv1⟩ := hcl1
    refine GoReturns.of_steps (hj1.withExit hret.fetch_none) ?_
    have hw1 : f1.mem.readLE accA 8 = digit 2 (s.mem.readLE accA 8) := by rw [hpv1, hv1]
    have hacc1 : MemFrame D.mem f1.mem (winA P s) := hae1.trans hff1 fun a n h => ⟨h, hsubA a n h⟩
    obtain ⟨hdr1, hpf1⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 96)
      (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl hfpc1 hfsp1
      (hf281.trans h28_1) (hf181.trans h18_1) henvE1 hff1 (hoA e1 (Nat.zero_le _) (by omega))
    have hE1 := (hcont1 f1 hdr1).1 (hpf1.trans hpn1)
    rw [Engine_cons] at hE1
    obtain ⟨k2, e2, hst2, ⟨hpc2, h26_2, h28_2, h18_2, h29_2, hal2, hlo2, hhi2, h30a2, h30b2, henvE2⟩,
      hfrE2, -, -, hpn2, -, -, hcont2, -⟩ := hE1
    dsimp only at hpc2 h26_2 hlo2 hhi2 hfrE2 hcont2
    refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
    have hae2 : MemFrame D.mem e2.mem (winA P s) := hacc1.trans hfrE2 fun a n h => ⟨h, hsubR a n h⟩
    have hm2 : e2.mem.readLE (fvA + 8) 8 = accAdd2A := by
      rw [hae2.readLE _ _ (by
        have h2 := hfo2
        simp only [outside_append, outside_cons, outside_nil, and_true] at h2
        simp only [winA, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨h2.1, by omega, by omega⟩)]
      exact hfv2
    have hv2 : e2.mem.readLE accA 8 = digit 2 (s.mem.readLE accA 8) := by
      rw [hfrE2.readLE _ _ hoT]; exact hw1
    rw [hm2] at hpc2
    have hpa2 : e2.mem.accessible accA 8 true = true := by rw [hae2.accessible]; exact hpaD
    have hcl2 := call_acc2 impl e2 hpc2 hpa2 h30a2 h30b2
    obtain ⟨j2, f2, hj2, -, hfpc2, hfsp2, hf282, hf182, hff2, hpv2⟩ := hcl2
    refine GoReturns.of_steps (hj2.withExit hret.fetch_none) ?_
    have hw2 : f2.mem.readLE accA 8 = digit 2 (digit 2 (s.mem.readLE accA 8)) := by rw [hpv2, hv2]
    have hacc2 : MemFrame D.mem f2.mem (winA P s) := hae2.trans hff2 fun a n h => ⟨h, hsubA a n h⟩
    obtain ⟨hdr2, hpf2⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 96)
      (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl hfpc2 hfsp2
      (hf282.trans h28_2) (hf182.trans h18_2) henvE2 hff2 (hoA e2 (Nat.zero_le _) (by omega))
    have hE2 := (hcont2 f2 hdr2).1 (hpf2.trans hpn2)
    rw [Engine_cons] at hE2
    obtain ⟨k3, e3, hst3, ⟨hpc3, h26_3, h28_3, h18_3, h29_3, hal3, hlo3, hhi3, h30a3, h30b3, henvE3⟩,
      hfrE3, -, -, hpn3, -, -, hcont3, -⟩ := hE2
    dsimp only at hpc3 h26_3 hlo3 hhi3 hfrE3 hcont3
    refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
    have hae3 : MemFrame D.mem e3.mem (winA P s) := hacc2.trans hfrE3 fun a n h => ⟨h, hsubR a n h⟩
    have hm3 : e3.mem.readLE fvA 8 = accAdd1A := by
      rw [hae3.readLE _ _ (by
        have h2 := hfo1
        simp only [outside_append, outside_cons, outside_nil, and_true] at h2
        simp only [winA, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨h2.1, by omega, by omega⟩)]
      exact hfv1
    have hv3 : e3.mem.readLE accA 8 = digit 2 (digit 2 (s.mem.readLE accA 8)) := by
      rw [hfrE3.readLE _ _ hoT]; exact hw2
    rw [hm3] at hpc3
    have hpa3 : e3.mem.accessible accA 8 true = true := by rw [hae3.accessible]; exact hpaD
    have hcl3 := call_acc1 impl e3 hpc3 hpa3 h30a3 h30b3
    obtain ⟨j3, f3, hj3, -, hfpc3, hfsp3, hf283, hf183, hff3, hpv3⟩ := hcl3
    refine GoReturns.of_steps (hj3.withExit hret.fetch_none) ?_
    have hw3 : f3.mem.readLE accA 8 = digit 1 (digit 2 (digit 2 (s.mem.readLE accA 8))) := by rw [hpv3, hv3]
    have hacc3 : MemFrame D.mem f3.mem (winA P s) := hae3.trans hff3 fun a n h => ⟨h, hsubA a n h⟩
    obtain ⟨hdr3, hpf3⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 96)
      (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl hfpc3 hfsp3
      (hf283.trans h28_3) (hf183.trans h18_3) henvE3 hff3 (hoA e3 (Nat.zero_le _) (by omega))
    have hE3 := (hcont3 f3 hdr3).1 (hpf3.trans hpn3)
    rw [Engine_nil] at hE3
    obtain ⟨k4, d, hst4, hdpc, hdsp, hd28, hd18, hd29, hfrD, henvD, -⟩ := hE3
    refine GoReturns.of_steps (hst4.withExit hret.fetch_none) ?_
    rw [hF] at hfrD
    have hdpc' : d.pc = BitVec.ofNat 64 597824 := by rw [hdpc, hD30]
    have hdsp' : d.sp = s.sp - 96#64 := by rw [hdsp, hDsp]
    have hd28' : d.regs 28 = s.regs 28 := by rw [hd28, hD28]
    have hd18' : d.regs 18 = s.regs 18 := by rw [hd18, hD18]
    have hdspn : d.sp.toNat = s.sp.toNat - 96 := by rw [hdsp']; exact h96
    have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    have hDx : D.mem.readLE (s.sp.toNat - 72) 8 = x.toNat := by
      rw [hD]; simp only [Memory.readLE_writeLE_self]
      rw [h64]; exact Nat.mod_eq_of_lt x.isLt
    have hDl : D.mem.readLE (s.sp.toNat - 96) 8 = ret := by
      rw [hD]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hxl
    have hDf8 : D.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat := by
      rw [hD]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hxf
    have hoX : ∀ a, (a + 8 ≤ s.sp.toNat - 96 - P.depth ∨ s.sp.toNat - 96 - 8 ≤ a) → (a + 8 ≤ accA ∨ accA + 8 ≤ a) →
        Outside a 8 P.priv → Outside a 8 (winA P s) := by
      intro a h1 h2 h3
      simp only [winA, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h3, h1, h2⟩
    have hdx : d.mem.readLE (s.sp.toNat - 72) 8 = x.toNat := by
      rw [hfrD.readLE _ _ (by
        simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩),
        hacc3.readLE _ _ (hoX _ (by omega) (by omega) (Outside.of_sub hout (by omega) (by omega)))]
      exact hDx
    have hdl : d.mem.readLE (s.sp.toNat - 96) 8 = ret := by
      rw [hfrD.readLE _ _ (by
        simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩),
        hacc3.readLE _ _ (hoX _ (by omega) (by omega) (Outside.of_sub hout (by omega) (by omega)))]
      exact hDl
    have hdf8 : d.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat := by
      rw [hfrD.readLE _ _ (by
        simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩),
        hacc3.readLE _ _ (hoX _ (by omega) (by omega) (Outside.of_sub hout (by omega) (by omega)))]
      exact hDf8
    have hdA : d.mem.readLE accA 8 = mix (s.mem.readLE accA 8) := by
      rw [hfrD.readLE _ _ hoT]; exact hw3
    have hdacc : d.mem.accessible (s.sp.toNat - (P.depth + 96)) (P.depth + 96 + 32) true = true := by
      rw [hfrD.accessible, hacc3.accessible, hDfW.accessible]; exact hst
    clear hst1 hst2 hst3 hst4 hj1 hj2 hj3 hfrD hfrE1 hfrE2 hfrE3 hcont1 hcont2 hcont3
    refine GoReturns.of_reaches ?_
    janus_run [hdl]
    exact ⟨by rw [hdf8]; exact BitVec.ofNat_toNat _ _, hx, hdx, hdA⟩
  · have hx' : 10 < x.toNat := by omega
    refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
      hret.fetch_none ?_
    janus_run [hx0, hx1, hx2, hx'] until [Extracted.program.contractAddr "runtime.gopanic"]
    refine ReachesRet.done rfl ?_
    refine GoReturns.name fun G hG => ?_
    have hGsp : G.sp = s.sp - 96#64 := by rw [hG]
    have hGspn : G.sp.toNat = s.sp.toNat - 96 := by rw [hGsp]; exact h96
    have hG0 : G.regs 0 = etyp := by rw [hG]; simp [setReg]
    have hG1 : G.regs 1 = edata := by rw [hG]; simp [setReg]
    have hG28 : G.regs 28 = s.regs 28 := by rw [hG]; simp [setReg]; exact hS28
    have hG18 : G.regs 18 = s.regs 18 := by rw [hG]; simp [setReg]; exact hS18
    have hG30 : G.regs 30 = BitVec.ofNat 64 597852 := by rw [hG]; simp [setReg]
    have hGpc : G.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by rw [hG] <;> rfl
    have hGm : G.mem = S.mem := by rw [hG]
    have hgG : gOf G = gOf s := by simp only [gOf, hG28]
    have hGfW : MemFrame s.mem G.mem (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) := by
      rw [hGm]; exact hW
    obtain ⟨fi, hfi⟩ : ∃ fi : FuncInfo, fi = FuncInfo.named Extracted.funcs "example.com/basic.DeferMix" := ⟨_, rfl⟩
    have f_frame : fi.frame = 96 := by rw [hfi]; rfl
    have f_od : fi.openDefer = none := by rw [hfi]; rfl
    have f_res : fi.resume = Extracted.entry + 0x44 := by rw [hfi]; rfl
    have hdG : P.defers G.mem (gOf G) = [{ sp := s.sp.toNat - 96, fns := [fvA + 8] },
        { sp := s.sp.toNat - 96, fns := [fvA + 8] }, { sp := s.sp.toNat - 96, fns := [fvA] }] ++
        P.defers s.mem (gOf s) := by rw [hGm, hgG]; exact hdefS
    have hF : frameOf fi G.sp.toNat G.mem =
        ⟨s.sp.toNat - 96, s.sp.toNat, Extracted.entry + 0x44, none⟩ := by
      simp only [frameOf, FuncInfo.bound, f_frame, f_od, hGspn, Option.map_none, f_res]
      have e3 : s.sp.toNat - 96 + 96 = s.sp.toNat := by omega
      rw [e3]
    have hds' : ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat - 96 < d.sp := fun d hd => by have := hdss d hd; omega
    have hrA := recItems_above hds'
    have hI : frameItems G.mem (frameOf fi G.sp.toNat G.mem) (P.defers G.mem (gOf G)) =
        [{ fn := fvA + 8, bits := none, chain := { sp := s.sp.toNat - 96, fns := [fvA + 8] } ::
            { sp := s.sp.toNat - 96, fns := [fvA] } :: P.defers s.mem (gOf s) },
         { fn := fvA + 8, bits := none, chain := { sp := s.sp.toNat - 96, fns := [fvA] } :: P.defers s.mem (gOf s) },
         { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] := by
      rw [hF, hdG]
      simp [frameItems, recItems, fnItems, hrA]
    have hfo1 : Outside fvA 8 (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) :=
      Outside.of_sub hfo (by omega) (by omega)
    have hfo2 : Outside (fvA + 8) 8 (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) :=
      Outside.of_sub hfo (by omega) (by omega)
    have hfv1 : G.mem.readLE fvA 8 = accAdd1A := by rw [hGfW.readLE _ _ hfo1]; exact fv1_read _ hd
    have hfv2 : G.mem.readLE (fvA + 8) 8 = accAdd2A := by rw [hGfW.readLE _ _ hfo2]; exact fv2_read _ hd
    have hfa1 : G.mem.accessible fvA 8 false = true := by
      rw [hGfW.accessible]; exact Memory.accessible_mono _ (fv_acc _ hd) (by omega) (by omega)
    have hfa2 : G.mem.accessible (fvA + 8) 8 false = true := by
      rw [hGfW.accessible]; exact Memory.accessible_mono _ (fv_acc _ hd) (by omega) (by omega)
    have hpaD : G.mem.accessible accA 8 true = true := by rw [hGfW.accessible]; exact hacc
    have hv0 : G.mem.readLE accA 8 = s.mem.readLE accA 8 := hGfW.readLE _ _ hao
    have hKp : frameKeep G.mem ⟨s.sp.toNat - 96, s.sp.toNat, Extracted.entry + 0x44, none⟩
        [{ fn := fvA + 8, bits := none, chain := { sp := s.sp.toNat - 96, fns := [fvA + 8] } ::
            { sp := s.sp.toNat - 96, fns := [fvA] } :: P.defers s.mem (gOf s) },
         { fn := fvA + 8, bits := none, chain := { sp := s.sp.toNat - 96, fns := [fvA] } :: P.defers s.mem (gOf s) },
         { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] =
        [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)] := by
      simp [frameKeep, Frame.openAt]
    have hsubR : ∀ a n, Outside a n (winA P s) →
        Outside a n (P.priv ++ rtWin P ⟨s.sp.toNat - 96, s.sp.toNat, Extracted.entry + 0x44, none⟩ ++
          bitsWin ⟨s.sp.toNat - 96, s.sp.toNat, Extracted.entry + 0x44, none⟩) := by
      intro a n h
      simp only [winA, rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at h ⊢
      exact ⟨h.1, h.2.1⟩
    have hoT : Outside accA 8 (P.priv ++ rtWin P ⟨s.sp.toNat - 96, s.sp.toNat, Extracted.entry + 0x44, none⟩ ++
        bitsWin ⟨s.sp.toNat - 96, s.sp.toNat, Extracted.entry + 0x44, none⟩) := by
      have hao' := hao
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at hao' ⊢
      exact ⟨hao'.1, by omega⟩
    have hsubA : ∀ a n, Outside a n (winA P s) → Outside a n [(accA, accA + 8)] := by
      intro a n h
      simp only [winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact h.2.2
    have hoA : ∀ (e : State), P.depth ≥ 0 → (s.sp.toNat - 96 - P.depth ≤ e.sp.toNat) →
        Outside accA (accA + 8 - accA) (P.priv ++ (e.sp.toNat, s.sp.toNat - 96) ::
          [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) := by
      intro e _ hlo
      have hao' := hao
      simp only [outside_append, outside_cons, outside_nil, and_true] at hao' ⊢
      simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hao'.1, by omega, by omega, by omega, by omega⟩
    refine GopanicContract.apply (fi := fi) hpan hGpc (by rw [hG30, hfi]; rfl) ?_ ?_
    · refine ⟨PanicPre.of_within hc hGfW (by rw [hGm]; exact henvS) (by omega) (by omega)
          (by rw [hGspn]; omega) hG28 (by rw [hG30]; decide) (by rw [hG30]; decide),
        by rw [hG0]; exact hne, ?_, ?_, ?_⟩
      · rw [hGm, hgG]; omega
      · intro h; rw [f_od] at h; cases h
      · rw [hI, hF]
        simp only [outside_append, outside_cons, outside_nil, and_true] at hfo
        refine ⟨trivial, fun it hit => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl | rfl <;> dsimp only
        · exact ⟨by omega, hfa2, by rw [hfv2] <;> decide, by rw [hfv2] <;> decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
        · exact ⟨by omega, hfa2, by rw [hfv2] <;> decide, by rw [hfv2] <;> decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
        · exact ⟨by omega, hfa1, by rw [hfv1] <;> decide, by rw [hfv1] <;> decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
    intro hE
    rw [hI, hF] at hE
    rw [hKp] at hE
    -- the first deferred call (the last heap record): `Acc = Acc*10 + 2`
    rw [Engine_cons] at hE
    obtain ⟨k1, e1, hst1, ⟨hpc1, h26_1, h28_1, h18_1, h29_1, hal1, hlo1, hhi1, h30a1, h30b1, henvE1⟩,
      hfrE1, -, -, hpn1, -, -, hcont1, -⟩ := hE
    dsimp only at hpc1 h26_1 hlo1 hhi1 hfrE1 hcont1
    refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
    have hae1 : MemFrame G.mem e1.mem (winA P s) := hfrE1.mono hsubR
    have hm1 : e1.mem.readLE (fvA + 8) 8 = accAdd2A := by
      rw [hae1.readLE _ _ (by
        simp only [winA, outside_append, outside_cons, outside_nil, and_true]
        have h2 := hfo2
        simp only [outside_append, outside_cons, outside_nil, and_true] at h2
        exact ⟨h2.1, by omega, by omega⟩)]
      exact hfv2
    have hv1 : e1.mem.readLE accA 8 = s.mem.readLE accA 8 := by rw [hfrE1.readLE _ _ hoT]; exact hv0
    rw [hm1] at hpc1
    have hpa1 : e1.mem.accessible accA 8 true = true := by rw [hae1.accessible]; exact hpaD
    have hcl1 := call_acc2 impl e1 hpc1 hpa1 h30a1 h30b1
    obtain ⟨j1, f1, hj1, -, hfpc1, hfsp1, hf281, hf181, hff1, hpv1⟩ := hcl1
    refine GoReturns.of_steps (hj1.withExit hret.fetch_none) ?_
    have hw1 : f1.mem.readLE accA 8 = digit 2 (s.mem.readLE accA 8) := by rw [hpv1, hv1]
    have hacc1 : MemFrame G.mem f1.mem (winA P s) := hae1.trans hff1 fun a n h => ⟨h, hsubA a n h⟩
    obtain ⟨hdr1, hpf1⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 96)
      (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl hfpc1 hfsp1
      (hf281.trans h28_1) (hf181.trans h18_1) henvE1 hff1 (hoA e1 (Nat.zero_le _) (by omega))
    have hE1 := (hcont1 f1 hdr1).1 (hpf1.trans hpn1)
    rw [Engine_cons] at hE1
    obtain ⟨k2, e2, hst2, ⟨hpc2, h26_2, h28_2, h18_2, h29_2, hal2, hlo2, hhi2, h30a2, h30b2, henvE2⟩,
      hfrE2, -, -, hpn2, -, -, hcont2, -⟩ := hE1
    dsimp only at hpc2 h26_2 hlo2 hhi2 hfrE2 hcont2
    refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
    have hae2 : MemFrame G.mem e2.mem (winA P s) := hacc1.trans hfrE2 fun a n h => ⟨h, hsubR a n h⟩
    have hm2 : e2.mem.readLE (fvA + 8) 8 = accAdd2A := by
      rw [hae2.readLE _ _ (by
        have h2 := hfo2
        simp only [outside_append, outside_cons, outside_nil, and_true] at h2
        simp only [winA, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨h2.1, by omega, by omega⟩)]
      exact hfv2
    have hv2 : e2.mem.readLE accA 8 = digit 2 (s.mem.readLE accA 8) := by
      rw [hfrE2.readLE _ _ hoT]; exact hw1
    rw [hm2] at hpc2
    have hpa2 : e2.mem.accessible accA 8 true = true := by rw [hae2.accessible]; exact hpaD
    have hcl2 := call_acc2 impl e2 hpc2 hpa2 h30a2 h30b2
    obtain ⟨j2, f2, hj2, -, hfpc2, hfsp2, hf282, hf182, hff2, hpv2⟩ := hcl2
    refine GoReturns.of_steps (hj2.withExit hret.fetch_none) ?_
    have hw2 : f2.mem.readLE accA 8 = digit 2 (digit 2 (s.mem.readLE accA 8)) := by rw [hpv2, hv2]
    have hacc2 : MemFrame G.mem f2.mem (winA P s) := hae2.trans hff2 fun a n h => ⟨h, hsubA a n h⟩
    obtain ⟨hdr2, hpf2⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 96)
      (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl hfpc2 hfsp2
      (hf282.trans h28_2) (hf182.trans h18_2) henvE2 hff2 (hoA e2 (Nat.zero_le _) (by omega))
    have hE2 := (hcont2 f2 hdr2).1 (hpf2.trans hpn2)
    rw [Engine_cons] at hE2
    obtain ⟨k3, e3, hst3, ⟨hpc3, h26_3, h28_3, h18_3, h29_3, hal3, hlo3, hhi3, h30a3, h30b3, henvE3⟩,
      hfrE3, -, -, hpn3, -, -, hcont3, -⟩ := hE2
    dsimp only at hpc3 h26_3 hlo3 hhi3 hfrE3 hcont3
    refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
    have hae3 : MemFrame G.mem e3.mem (winA P s) := hacc2.trans hfrE3 fun a n h => ⟨h, hsubR a n h⟩
    have hm3 : e3.mem.readLE fvA 8 = accAdd1A := by
      rw [hae3.readLE _ _ (by
        have h2 := hfo1
        simp only [outside_append, outside_cons, outside_nil, and_true] at h2
        simp only [winA, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨h2.1, by omega, by omega⟩)]
      exact hfv1
    have hv3 : e3.mem.readLE accA 8 = digit 2 (digit 2 (s.mem.readLE accA 8)) := by
      rw [hfrE3.readLE _ _ hoT]; exact hw2
    rw [hm3] at hpc3
    have hpa3 : e3.mem.accessible accA 8 true = true := by rw [hae3.accessible]; exact hpaD
    have hcl3 := call_acc1 impl e3 hpc3 hpa3 h30a3 h30b3
    obtain ⟨j3, f3, hj3, -, hfpc3, hfsp3, hf283, hf183, hff3, hpv3⟩ := hcl3
    refine GoReturns.of_steps (hj3.withExit hret.fetch_none) ?_
    have hw3 : f3.mem.readLE accA 8 = digit 1 (digit 2 (digit 2 (s.mem.readLE accA 8))) := by rw [hpv3, hv3]
    have hacc3 : MemFrame G.mem f3.mem (winA P s) := hae3.trans hff3 fun a n h => ⟨h, hsubA a n h⟩
    obtain ⟨hdr3, hpf3⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 96)
      (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl hfpc3 hfsp3
      (hf283.trans h28_3) (hf183.trans h18_3) henvE3 hff3 (hoA e3 (Nat.zero_le _) (by omega))
    have hE3 := (hcont3 f3 hdr3).1 (hpf3.trans hpn3)
    rw [Engine_nil] at hE3
    obtain ⟨k4, d, hst4, hU, hpd, -, hfrd, -, -, -⟩ := hE3
    refine GoReturns.leave (v := ⟨etyp.toNat, edata.toNat⟩) (hst4.withExit hret.fetch_none) ?_ ?_
    · have hg' : gOf s = (G.regs 28).toNat := by simp only [gOf, hG28]
      have hU' := hU; rw [← hg'] at hU'
      have hpd' := hpd; rw [show (G.regs 28).toNat = gOf s from hg'.symm] at hpd'
      refine ⟨hU', _, _, hpd', ?_, rfl⟩
      simp only [hG0, hG1]
    · refine ⟨hx', rfl, ?_⟩
      rw [hfrd.readLE _ _ hoT]; exact hw3

/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSat` (code that
`Janus.Contracts.PanicSatRun` proves meets the four contracts in every program that contains it)
linked into `DeferMix`'s program with a branch to it at each contract address, and a call state
satisfying the precondition (an `any` of type word `1`, `x = 11`): so `correctness` applies
(`nonvacuous`), and `DeferMix` panics from that state (`returns`). -/

namespace Witness

open Janus.Contracts.PanicSat Janus.Contracts.PanicModel

abbrev T0 : List FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : PanicRuntime := P0 T0 RPa

def dsA : Nat := Extracted.program.contractAddr "runtime.deferprocStack"
def dpA : Nat := Extracted.program.contractAddr "runtime.deferproc"
def gA : Nat := Extracted.program.contractAddr "runtime.gopanic"
def drA : Nat := Extracted.program.contractAddr "runtime.deferreturn"

/-- The code linked next to `DeferMix`: the model engine and a branch to it at each contract
address. -/
def implW : List Segment :=
  panicImpl Extracted.program [("runtime.deferprocStack", eDeferprocStack), ("runtime.deferproc", eDeferproc),
    ("runtime.gopanic", eGopanic), ("runtime.deferreturn", eDeferreturn)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

theorem stubDs : StubAt (Extracted.program.link implW) dsA eDeferprocStack :=
  StubAt.of_decode (w := stubWord dsA eDeferprocStack) (imm := (eDeferprocStack - dsA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem stubDp : StubAt (Extracted.program.link implW) dpA eDeferproc :=
  StubAt.of_decode (w := stubWord dpA eDeferproc) (imm := (eDeferproc - dpA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem stubG : StubAt (Extracted.program.link implW) gA eGopanic :=
  StubAt.of_decode (w := stubWord gA eGopanic) (imm := (eGopanic - gA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem stubDr : StubAt (Extracted.program.link implW) drA eDeferreturn :=
  StubAt.of_decode (w := stubWord drA eDeferreturn) (imm := (eDeferreturn - drA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem hds : DeferprocStackContract (Extracted.program.link implW) dsA PW :=
  deferprocStack_at stubDs (deferprocStack_contract engineAt T0)

theorem hdp : DeferprocContract (Extracted.program.link implW) dpA PW :=
  deferproc_at stubDp (deferproc_contract engineAt T0)

theorem hpan : GopanicContract (Extracted.program.link implW) gA PW U0 T0 :=
  gopanic_at stubG (gopanic_run engineAt T0 tok)

theorem hdr : DeferreturnContract (Extracted.program.link implW) drA PW U0 :=
  deferreturn_at stubDr (deferreturn_run engineAt)

/-- The witness memory, with `Acc` a writable word. -/
def wm : Memory :=
  ⟨(witMemD (tabWords T0) Extracted.data).bytes,
    (witMemD (tabWords T0) Extracted.data).regions ++ [⟨accA, 8, true⟩]⟩

def wg : Nat := 0x50000
def wsp : Nat := 0x48000
def ret : Nat := 0x200000

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
      else if i = 29 then BitVec.ofNat 64 (wsp - 8) else if i = 0 then 11#64
      else if i = 1 then 1#64 else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wm }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [11#64, 1#64, 0#64] s0 := by
  refine ⟨rfl, rfl, fun i h => ?_⟩
  simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
theorem pre : PanicCallerOK PW s0 96 32 ∧ Extracted.program.DataLoaded s0.mem ∧
    s0.mem.accessible accA 8 true = true ∧
    Outside accA 8 (PW.priv ++ [(s0.sp.toNat - (PW.depth + 96), s0.sp.toNat + 32)]) ∧
    Outside fvA 16 (PW.priv ++ [(s0.sp.toNat - (PW.depth + 96), s0.sp.toNat + 32)]) ∧
    (1#64 : BitVec 64).toNat ≠ 0 ∧ 4 ≤ PW.room s0.mem (gOf s0) ∧
    PW.saved s0.mem (gOf s0) = none ∧ ∀ d ∈ PW.defers s0.mem (gOf s0), s0.sp.toNat ≤ d.sp := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_⟩, dataLoaded, by decide, ?_, ?_, by decide, ?_, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · simp only [P0_priv, outside_append, outside_cons, outside_nil, and_true]; decide
  · simp only [P0_priv, outside_append, outside_cons, outside_nil, and_true]; decide
  · show 4 ≤ room0 wm
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
    DeferprocStackContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferprocStack") P ∧
    DeferprocContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferproc") P ∧
    GopanicContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gopanic") P U
      Extracted.funcs ∧
    DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P U ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [11#64, 1#64, 0#64] s ∧
    (PanicCallerOK P s 96 32 ∧ Extracted.program.DataLoaded s.mem ∧ s.mem.accessible accA 8 true = true ∧
      Outside accA 8 (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) ∧
      Outside fvA 16 (P.priv ++ [(s.sp.toNat - (P.depth + 96), s.sp.toNat + 32)]) ∧
      (1#64 : BitVec 64).toNat ≠ 0 ∧ 4 ≤ P.room s.mem (gOf s) ∧
      P.saved s.mem (gOf s) = none ∧ ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp) :=
  ⟨implW, PW, U0, ret, s0, P0_laws T0 RPa, hds, hdp, hpan, hdr, hret, setup, pre⟩

/-- So the guarantee is reached: with `x = 11` `DeferMix` panics with `e`, after the deferred
calls ran in LIFO order. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClassU PW U0 s0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ ((11#64 : BitVec 64).toNat ≤ 10 ∧ (s'.regs 0).toNat = (11#64 : BitVec 64).toNat ∧
        s'.mem.readLE accA 8 = mix (s0.mem.readLE accA 8))
    | .panicked v s' => 10 < (11#64 : BitVec 64).toNat ∧ v = ⟨(1#64 : BitVec 64).toNat, (0#64 : BitVec 64).toNat⟩ ∧
        s'.mem.readLE accA 8 = mix (s0.mem.readLE accA 8)
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U0 hds hdp hpan hdr 11#64 1#64 0#64 ret hret s0 setup pre

end Witness

end Proof
