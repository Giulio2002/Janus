import Janus
import Extracted

/-!
# `DeferMix(x uint64, e any) uint64`: a stack defer and two heap defers, run in LIFO order (amd64)

`DeferMix` is `defer accAdd1(); for i := 0; i < 2; i++ { defer accAdd2() }; if x > 10 { panic(e) }; return x`.
A defer in a loop disables open-coding for the whole function, so the first defer is a stack
`_defer` record (`runtime.deferprocStack`) and the two in the loop are heap records
(`runtime.deferproc`). On return `runtime.deferreturn` runs them, on `panic(e)` `runtime.gopanic`
does, in LIFO order: the two heap records, then the stack record. `accAdd1` / `accAdd2` append the
digit 1 / 2 to the package variable `Acc` (`Acc = Acc*10 + d`).

**Guarantee (example 5 of docs/COVERAGE.md R6).** For every panic-runtime model `P` satisfying its
laws, every implementation of `runtime.deferprocStack`, `runtime.deferproc`, `runtime.gopanic` and
`runtime.deferreturn` meeting their contracts (`Janus.Contracts.PanicAmd64`, pinned to the Go 1.26
runtime's code), every admissible return address and every call state in which the runtime is
usable with room for four records, `Acc` is a writable word and the funcvals of the two deferred
functions are in memory (all outside the runtime's memory and the stack window):

* if `x ≤ 10` the call **returns `x`**;
* if `x > 10` the call **panics with `e`**;

and in both cases `Acc` ends as `((Acc*10+2)*10+2)*10+1` (mod `2^64`): the deferred calls ran in
LIFO order, the deferred code being the program's own (`accAdd1`, `accAdd2`).

`Acc` lives in `.noptrbss`, whose content the binary does not fix, so the extractor does not copy it
and the proof's precondition provides the word (`accA`, the address the compiled code accesses).

The proof is split into one theorem per phase (`prefix_run`: the three defers; `ret_run`: the
return; `panic_run`: the panic), each of which compiles on its own.
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64
open Janus.Contracts.MapAmd64 (keepABI_apply)
open Janus.Contracts.Panic (Item recItems frameItems fnItems frameKeep bitsWin recItems_above Frame
  frameRecs_above)
open Janus.Spec (openBits)

/-! Code addresses are read off the extraction (`janus_eval%`), never copied: a relinked
binary needs no edit. -/
local macro "loc_DeferMix_69" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferMix" + 69))
local macro "loc_DeferMix_120" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferMix" + 120))
local macro "loc_DeferMix_122" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferMix" + 122))
local macro "loc_DeferMix_144" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferMix" + 144))
local macro "loc_DeferMix_170" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferMix" + 170))

/-- The address of `example.com/basic.Acc` (`.noptrbss`; the extractor does not copy it). -/
local macro "accA" : term => `(janus_eval% (ripTarget Extracted.program (segAddr Extracted.program "example.com/basic.accAdd2")))

local macro "fvA" : term => `(janus_eval% (Extracted.program.data.head!.base))
local macro "accAdd1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.accAdd1"))
local macro "accAdd2A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.accAdd2"))

def digit (k v : Nat) : Nat := (v * 10 + k) % 2 ^ 64

/-- The three deferred calls in LIFO order: the two heap records, then the stack record. -/
def mix (v : Nat) : Nat := digit 1 (digit 2 (digit 2 v))

set_option maxHeartbeats 0 in
/-- `accAdd2` run from `e`: it appends the digit 2 to `Acc` and returns. -/
theorem call_acc2 (impl : List Janus.Amd64.Segment) (e : State) (hpe : e.rip = BitVec.ofNat 64 accAdd2A)
    (hacc : e.mem.accessible accA 8 true = true) (hra : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 47)
    (hrac : e.mem.accessible (e.regs 4).toNat 8 false = true)
    (hdj : accA + 8 ≤ (e.regs 4).toNat ∨ (e.regs 4).toNat + 8 ≤ accA) :
    ReachesRet (Extracted.program.link impl) (retAddrOf e) e (fun e' =>
      e'.rip = retAddrOf e ∧ e'.regs 4 = e.regs 4 + 8 ∧ e'.regs 14 = e.regs 14 ∧ e'.regs 5 = e.regs 5 ∧
      e'.xmm 15 = e.xmm 15 ∧ e'.df = e.df ∧ MemFrame e.mem e'.mem [(accA, accA + 8)] ∧
      e'.mem.readLE accA 8 = digit 2 (e.mem.readLE accA 8)) := by
  have hacc' : e.mem.accessible accA 8 false = true := Janus.Arm64.Memory.accessible_weaken _ hacc
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpe
  janus64_run
  refine ⟨MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega), ?_⟩
  simp only [digit]; omega

set_option maxHeartbeats 0 in
/-- `accAdd1` run from `e`: it appends the digit 1 to `Acc` and returns. -/
theorem call_acc1 (impl : List Janus.Amd64.Segment) (e : State) (hpe : e.rip = BitVec.ofNat 64 accAdd1A)
    (hacc : e.mem.accessible accA 8 true = true) (hra : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 47)
    (hrac : e.mem.accessible (e.regs 4).toNat 8 false = true)
    (hdj : accA + 8 ≤ (e.regs 4).toNat ∨ (e.regs 4).toNat + 8 ≤ accA) :
    ReachesRet (Extracted.program.link impl) (retAddrOf e) e (fun e' =>
      e'.rip = retAddrOf e ∧ e'.regs 4 = e.regs 4 + 8 ∧ e'.regs 14 = e.regs 14 ∧ e'.regs 5 = e.regs 5 ∧
      e'.xmm 15 = e.xmm 15 ∧ e'.df = e.df ∧ MemFrame e.mem e'.mem [(accA, accA + 8)] ∧
      e'.mem.readLE accA 8 = digit 1 (e.mem.readLE accA 8)) := by
  have hacc' : e.mem.accessible accA 8 false = true := Janus.Arm64.Memory.accessible_weaken _ hacc
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpe
  janus64_run
  refine ⟨MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega), ?_⟩
  simp only [digit]; omega

set_option maxRecDepth 100000 in
theorem fv1_read (m : Janus.Arm64.Memory) (hd : Extracted.program.DataLoaded m) : m.readLE fvA 8 = accAdd1A :=
  readLE_of_dataRead hd (by decide)
set_option maxRecDepth 100000 in
theorem fv2_read (m : Janus.Arm64.Memory) (hd : Extracted.program.DataLoaded m) : m.readLE (fvA + 8) 8 = accAdd2A :=
  readLE_of_dataRead hd (by decide)
set_option maxRecDepth 100000 in
theorem fv_acc (m : Janus.Arm64.Memory) (hd : Extracted.program.DataLoaded m) : m.accessible fvA 16 false = true :=
  Janus.Contracts.PanicSatAmd64.accessible_of_dataRead hd (by decide)

/-- The slots a runtime call leaves alone: the arguments `x`, `e` in the caller's spill area, the
saved return address and frame pointer. -/
def Fx (s : State) (m : Janus.Arm64.Memory) (x etyp edata : BitVec 64) (ret : Nat) : Prop :=
  m.readLE ((s.regs 4).toNat + 8) 8 = x.toNat ∧ m.readLE ((s.regs 4).toNat + 16) 8 = etyp.toNat ∧
    m.readLE ((s.regs 4).toNat + 24) 8 = edata.toNat ∧ m.readLE (s.regs 4).toNat 8 = ret ∧
    m.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat

theorem Fx.step {P : Spec.PanicRuntime} {s S : State} {m m' : Janus.Arm64.Memory} {ex : List (Nat × Nat)}
    {x etyp edata : BitVec 64} {ret : Nat} (h : Fx s m x etyp edata ret)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 96)
    (hout : Outside ((s.regs 4).toNat - (P.depth + 96)) (P.depth + 96 + 32) P.priv)
    (hex : ex = [] ∨ ex = [((s.regs 4).toNat - 56, (s.regs 4).toNat - 56 + 48)])
    (hlo : P.depth + 96 ≤ (s.regs 4).toNat)
    (hfr : MemFrame m m' (P.priv ++ MapAmd64.calleeStack S P.depth 1 ++ ex)) : Fx s m' x etyp edata ret := by
  have hO : ∀ a, (s.regs 4).toNat - (P.depth + 96) ≤ a → a + 8 ≤ (s.regs 4).toNat + 32 →
      (a + 8 ≤ (s.regs 4).toNat - 96 - P.depth ∨ (s.regs 4).toNat - 96 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 88 ∨ (s.regs 4).toNat - 80 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 56 ∨ (s.regs 4).toNat - 8 ≤ a) →
      Outside a 8 (P.priv ++ MapAmd64.calleeStack S P.depth 1 ++ ex) := by
    intro a h1 h2 h3 h4 h5
    have hp : Outside a 8 P.priv := Outside.of_sub hout (by omega) (by omega)
    simp only [outside_append, outside_cons, outside_nil, and_true, MapAmd64.calleeStack, hsp]
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

/-- The precondition of `correctness`, as one proposition. -/
def Pre (P : Spec.PanicRuntime) (s : State) (etyp : BitVec 64) : Prop :=
  PanicCallerOK P s 96 32 ∧ Extracted.program.DataLoaded s.mem ∧ s.mem.accessible accA 8 true = true ∧
    Outside accA 8 (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) ∧
    Outside fvA 16 (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) ∧
    etyp.toNat ≠ 0 ∧ 4 ≤ P.room s.mem (gOf s) ∧ P.saved s.mem (gOf s) = none ∧
    ∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp

/-- The state at the loop exit (after the stack record and the two heap records are deferred). -/
def AfterDefers (P : Spec.PanicRuntime) (s S : State) (x etyp edata : BitVec 64) (ret : Nat) : Prop :=
  S.rip = BitVec.ofNat 64 (Extracted.entry + 0x7a) ∧ S.regs 4 = s.regs 4 - 88#64 ∧
    S.regs 14 = s.regs 14 ∧ S.regs 5 = s.regs 4 - 8#64 ∧ S.xmm 15 = 0 ∧ S.df = false ∧
    MemFrame s.mem S.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) ∧
    P.Env S.mem ∧
    P.defers S.mem (gOf s) =
      [{ sp := (s.regs 4).toNat - 88, fns := [fvA + 8] }, { sp := (s.regs 4).toNat - 88, fns := [fvA + 8] },
       { sp := (s.regs 4).toNat - 88, fns := [fvA] }] ++ P.defers s.mem (gOf s) ∧
    P.saved S.mem (gOf s) = none ∧ P.panics S.mem (gOf s) = P.panics s.mem (gOf s) ∧
    P.room s.mem (gOf s) ≤ P.room S.mem (gOf s) + 3 ∧
    Fx s S.mem x etyp edata ret

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
/-- The prefix of `DeferMix`: the stack record and the two heap records are deferred. -/
theorem prefix_run (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (hds : DeferprocStackContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferprocStack") P)
    (hdp : DeferprocContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferproc") P)
    (x etyp edata : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (s : State) (hs : CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x, etyp, edata] s)
    (hpre : Pre P s etyp) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x7a)) s
      (fun S => AfterDefers P s S x etyp edata ret) := by
  obtain ⟨hc, hd, hacc, hao, hfo, hne, hroom, hsave, hdss⟩ := hpre
  have hc' := hc
  obtain ⟨henv, hg, hal, hd', hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd' hb hal hdss
  have h96 : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hagw : ∀ m, MemFrame s.mem m [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)] →
      Spec.Map.Agrees s.mem m P.priv :=
    fun m hf => Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 96)) (hi := (s.regs 4).toNat + 32) hf
      (Outside.of_sub hout (by omega) (by omega))
  -- the stack record
  janus64_run until [Extracted.program.contractAddr "runtime.deferprocStack"]
  refine ReachesRet.name fun S hS => ?_
  have hSsp : S.regs 4 = s.regs 4 - 96#64 := by rw [hS] <;> rfl
  have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hSsp]; exact h96
  have hSf : MemFrame s.mem S.mem [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)] := by
    rw [hS]; janus_frame
  have hS0 : S.regs 0 = s.regs 4 - 56#64 := by rw [hS] <;> simp [setRegF]
  have hS0n : (S.regs 0).toNat = (s.regs 4).toNat - 56 := by
    rw [hS0, BitVec.toNat_sub]; simp; omega
  have hS14 : S.regs 14 = s.regs 14 := by rw [hS] <;> simp [setRegF]
  have hSx : S.xmm 15 = 0 := by rw [hS]; exact h_x15
  have hSdf : S.df = false := by rw [hS]
  have hSpc : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferprocStack") := by
    rw [hS] <;> rfl
  have hSra : S.mem.readLE (S.regs 4).toNat 8 = loc_DeferMix_69 := by
    rw [hS]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h96, Janus.Arm64.Memory.readLE_writeLE_self]
  have hgS : gOf S = gOf s := by simp only [gOf, hS14]
  have hagS : Spec.Map.Agrees s.mem S.mem P.priv := hagw _ hSf
  have hSfW : MemFrame s.mem S.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  have hr48 : ret < 2 ^ 47 := hret.user
  have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have hFx0 : Fx s S.mem x etyp edata ret := by
    rw [hS]; unfold Fx
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
    · rw [h64]; exact Nat.mod_eq_of_lt x.isLt
    · rw [h64]; exact Nat.mod_eq_of_lt etyp.isLt
    · rw [h64]; exact Nat.mod_eq_of_lt edata.isLt
    · exact h_ret
    · rw [h64]; exact Nat.mod_eq_of_lt (s.regs 5).isLt
  have hfn0 : S.mem.readLE ((S.regs 0).toNat + 24) 8 = fvA := by
    rw [hS0n, show (s.regs 4).toNat - 56 + 24 = (s.regs 4).toNat - 32 by omega, hS]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    try decide
  refine ReachesRet.call hds hSpc ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
      (by omega) hS14 hSx hSdf (by rw [hSra]; decide),
    by rw [hgS, hl.room_frame _ _ _ hagS]; omega, by omega, ?_, ?_⟩ ?_
  · rw [hS0n, hSf.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
  · rw [hS0n]; exact Outside.of_sub hout (by omega) (by omega)
  intro s1 hpc1 hq1
  obtain ⟨⟨r1, x1, y1, f1, m1, zhm1, krm1, hs1, hfr1, henv1⟩, hdef1, hkeep1⟩ := hq1
  have hm1 : s1.mem = m1 := by rw [hs1]
  have hfsp : fspOf S = (s.regs 4).toNat - 88 := by simp only [fspOf, hSspn]; omega
  have hd1 : P.defers m1 (gOf s) = { sp := (s.regs 4).toNat - 88, fns := [fvA] } :: P.defers s.mem (gOf s) := by
    have := hdef1; rw [hm1, hgS, hfsp, hfn0, hl.defers_frame _ _ _ hagS] at this; exact this
  have hsv1 : P.saved m1 (gOf s) = none := by
    have := hkeep1.2.1; rw [hm1, hgS, hl.saved_frame _ _ _ hagS] at this; rw [this]; exact hsave
  have hpn1 : P.panics m1 (gOf s) = P.panics s.mem (gOf s) := by
    have := hkeep1.1; rw [hm1, hgS, hl.panics_frame _ _ _ hagS] at this; exact this
  have hrm1 : P.room s.mem (gOf s) ≤ P.room m1 (gOf s) + 1 := by
    have := hkeep1.2.2.2; rw [hm1, hgS, hl.room_frame _ _ _ hagS] at this; exact this
  have hfr1' : MemFrame S.mem m1 (P.priv ++ MapAmd64.calleeStack S P.depth 1 ++
      [((s.regs 4).toNat - 56, (s.regs 4).toNat - 56 + 48)]) := by
    rw [hS0n] at hfr1; exact hfr1
  have hFx1 : Fx s m1 x etyp edata ret :=
    Fx.step (S := S) hFx0 hSspn hout (Or.inr rfl) hd' hfr1'
  have hstep : ∀ (S : State) (m : Janus.Arm64.Memory) (ex : List (Nat × Nat)),
      MemFrame s.mem S.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) →
      (S.regs 4).toNat = (s.regs 4).toNat - 96 →
      (∀ a n, Outside a n [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)] → Outside a n ex) →
      MemFrame S.mem m (P.priv ++ MapAmd64.calleeStack S P.depth 1 ++ ex) →
      MemFrame s.mem m (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) := by
    intro S m ex h1 h2 h3 h4
    refine h1.trans h4 fun a n h => ⟨h, ?_⟩
    have h' := h
    simp only [outside_append] at h' ⊢
    obtain ⟨h5, h6⟩ := h'
    refine ⟨⟨h5, ?_⟩, h3 a n h6⟩
    simp only [outside_cons, outside_nil, and_true, MapAmd64.calleeStack, h2] at h6 ⊢
    omega
  have hW1 := hstep S m1 [((s.regs 4).toNat - 56, (s.regs 4).toNat - 56 + 48)] hSfW hSspn (fun a n h => by
    simp only [outside_cons, outside_nil, and_true] at h ⊢; omega) hfr1'
  clear hdef1 hkeep1 hSf hSfW hagS hS0 hS0n hS14 hSx hSdf hSpc hgS hSsp hSspn hm1 hpc1 hfn0 hfr1 hSra hfsp
  subst hs1
  subst hS
  -- first loop iteration: deferproc
  janus64_run until [Extracted.program.contractAddr "runtime.deferproc"]
  refine ReachesRet.name fun S2 hS2 => ?_
  have hS2sp : S2.regs 4 = s.regs 4 - 96#64 := by rw [hS2] <;> simp [setRegF, MapAmd64.keepABI]
  have hS2spn : (S2.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hS2sp]; exact h96
  have hS2f : MemFrame m1 S2.mem [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)] := by
    rw [hS2]; janus_frame
  have hS20 : S2.regs 0 = BitVec.ofNat 64 (fvA + 8) := by rw [hS2] <;> simp [setRegF]
  have hS214 : S2.regs 14 = s.regs 14 := by rw [hS2] <;> simp [setRegF, MapAmd64.keepABI]
  have hS2x : S2.xmm 15 = 0 := by rw [hS2]; simpa [MapAmd64.keepX15] using h_x15
  have hS2df : S2.df = false := by rw [hS2]
  have hS2pc : S2.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferproc") := by
    rw [hS2] <;> rfl
  have hgS2 : gOf S2 = gOf s := by simp only [gOf, hS214]
  have hS2fW : MemFrame s.mem S2.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) :=
    hW1.trans hS2f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagS2 : Spec.Map.Agrees m1 S2.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 96)) (hi := (s.regs 4).toNat + 32) hS2f
      (Outside.of_sub hout (by omega) (by omega))
  have hS2ra : S2.mem.readLE (S2.regs 4).toNat 8 = loc_DeferMix_120 := by
    rw [hS2]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h96, Janus.Arm64.Memory.readLE_writeLE_self]
  have hS2i : S2.mem.readLE ((s.regs 4).toNat - 64) 8 = 0 := by
    rw [hS2]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  refine ReachesRet.call hdp hS2pc ⟨PanicPre.of_within hc hS2fW (hl.env_frame _ _ henv1 hagS2) (by omega) (by omega)
      (by omega) hS214 hS2x hS2df (by rw [hS2ra]; decide),
    by rw [hgS2, hl.room_frame _ _ _ hagS2]; omega⟩ ?_
  intro s2 hpc2 hq2
  obtain ⟨⟨r2, x2, y2, f2, m2, zhm2, krm2, hs2, hfr2, henv2⟩, hdef2, hkeep2⟩ := hq2
  have hm2 : s2.mem = m2 := by rw [hs2]
  have hS20n : (S2.regs 0).toNat = fvA + 8 := by rw [hS20]; simp
  have hfsp2 : fspOf S2 = (s.regs 4).toNat - 88 := by simp only [fspOf, hS2spn]; omega
  have hd2 : P.defers m2 (gOf s) = { sp := (s.regs 4).toNat - 88, fns := [fvA + 8] } ::
      { sp := (s.regs 4).toNat - 88, fns := [fvA] } :: P.defers s.mem (gOf s) := by
    have := hdef2; rw [hm2, hgS2, hfsp2, hS20n, hl.defers_frame _ _ _ hagS2, hd1] at this; exact this
  have hsv2 : P.saved m2 (gOf s) = none := by
    have := hkeep2.2.1; rw [hm2, hgS2, hl.saved_frame _ _ _ hagS2] at this; rw [this]; exact hsv1
  have hpn2 : P.panics m2 (gOf s) = P.panics s.mem (gOf s) := by
    have := hkeep2.1; rw [hm2, hgS2, hl.panics_frame _ _ _ hagS2] at this; rw [this, hpn1]
  have hrm2 : P.room s.mem (gOf s) ≤ P.room m2 (gOf s) + 2 := by
    have := hkeep2.2.2.2; rw [hm2, hgS2, hl.room_frame _ _ _ hagS2] at this; omega
  simp only [MapAmd64.calleeStack, hS2spn] at hfr2
  have hfr2' : MemFrame S2.mem m2 (P.priv ++ MapAmd64.calleeStack S2 P.depth 1 ++ []) := by
    simpa [MapAmd64.calleeStack, hS2spn] using hfr2
  have hW2 := hstep S2 m2 [] hS2fW hS2spn (fun a n h => by simp only [outside_nil]) hfr2'
  have hFx2' : Fx s S2.mem x etyp edata ret := by
    rw [hS2]; unfold Fx at hFx1 ⊢
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hFx1
  have hFx2 : Fx s m2 x etyp edata ret :=
    Fx.step (S := S2) hFx2' hS2spn hout (Or.inl rfl) hd' hfr2'
  have hi2 : m2.readLE ((s.regs 4).toNat - 64) 8 = 0 := by
    rw [hfr2'.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true, MapAmd64.calleeStack, hS2spn]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    exact hS2i
  clear hdef2 hkeep2 hS2f hS2fW hagS2 hS20 hS214 hS2x hS2df hS2pc hgS2 hS2sp hS2spn hS20n hm2 hpc2 hd1 hrm1 hsv1 hpn1 hW1 henv1 hfr2 hS2i hS2ra hfsp2 hFx1 hfr2'
  subst hs2
  subst hS2
  -- second loop iteration: deferproc
  janus64_run [hi2] until [Extracted.program.contractAddr "runtime.deferproc"]
  refine ReachesRet.name fun S3 hS3 => ?_
  have hS3sp : S3.regs 4 = s.regs 4 - 96#64 := by rw [hS3] <;> simp [setRegF, MapAmd64.keepABI]
  have hS3spn : (S3.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hS3sp]; exact h96
  have hS3f : MemFrame m2 S3.mem [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)] := by
    rw [hS3]; janus_frame
  have hS30 : S3.regs 0 = BitVec.ofNat 64 (fvA + 8) := by rw [hS3] <;> simp [setRegF]
  have hS314 : S3.regs 14 = s.regs 14 := by rw [hS3] <;> simp [setRegF, MapAmd64.keepABI]
  have hS3x : S3.xmm 15 = 0 := by rw [hS3]; simpa [MapAmd64.keepX15] using h_x15
  have hS3df : S3.df = false := by rw [hS3]
  have hS3pc : S3.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferproc") := by
    rw [hS3] <;> rfl
  have hgS3 : gOf S3 = gOf s := by simp only [gOf, hS314]
  have hS3fW : MemFrame s.mem S3.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) :=
    hW2.trans hS3f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagS3 : Spec.Map.Agrees m2 S3.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 96)) (hi := (s.regs 4).toNat + 32) hS3f
      (Outside.of_sub hout (by omega) (by omega))
  have hS3ra : S3.mem.readLE (S3.regs 4).toNat 8 = loc_DeferMix_120 := by
    rw [hS3]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h96, Janus.Arm64.Memory.readLE_writeLE_self]
  have hS3i : S3.mem.readLE ((s.regs 4).toNat - 64) 8 = 1 := by
    rw [hS3]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  refine ReachesRet.call hdp hS3pc ⟨PanicPre.of_within hc hS3fW (hl.env_frame _ _ henv2 hagS3) (by omega) (by omega)
      (by omega) hS314 hS3x hS3df (by rw [hS3ra]; decide),
    by rw [hgS3, hl.room_frame _ _ _ hagS3]; omega⟩ ?_
  intro s3 hpc3 hq3
  obtain ⟨⟨r3, x3, y3, f3, m3, zhm3, krm3, hs3, hfr3, henv3⟩, hdef3, hkeep3⟩ := hq3
  have hm3 : s3.mem = m3 := by rw [hs3]
  have hS30n : (S3.regs 0).toNat = fvA + 8 := by rw [hS30]; simp
  have hfsp3 : fspOf S3 = (s.regs 4).toNat - 88 := by simp only [fspOf, hS3spn]; omega
  have hd3 : P.defers m3 (gOf s) = { sp := (s.regs 4).toNat - 88, fns := [fvA + 8] } ::
      { sp := (s.regs 4).toNat - 88, fns := [fvA + 8] } ::
      { sp := (s.regs 4).toNat - 88, fns := [fvA] } :: P.defers s.mem (gOf s) := by
    have := hdef3; rw [hm3, hgS3, hfsp3, hS30n, hl.defers_frame _ _ _ hagS3, hd2] at this; exact this
  have hsv3 : P.saved m3 (gOf s) = none := by
    have := hkeep3.2.1; rw [hm3, hgS3, hl.saved_frame _ _ _ hagS3] at this; rw [this]; exact hsv2
  have hpn3 : P.panics m3 (gOf s) = P.panics s.mem (gOf s) := by
    have := hkeep3.1; rw [hm3, hgS3, hl.panics_frame _ _ _ hagS3] at this; rw [this, hpn2]
  have hrm3 : P.room s.mem (gOf s) ≤ P.room m3 (gOf s) + 3 := by
    have := hkeep3.2.2.2; rw [hm3, hgS3, hl.room_frame _ _ _ hagS3] at this; omega
  simp only [MapAmd64.calleeStack, hS3spn] at hfr3
  have hfr3' : MemFrame S3.mem m3 (P.priv ++ MapAmd64.calleeStack S3 P.depth 1 ++ []) := by
    simpa [MapAmd64.calleeStack, hS3spn] using hfr3
  have hW3 := hstep S3 m3 [] hS3fW hS3spn (fun a n h => by simp only [outside_nil]) hfr3'
  have hFx3' : Fx s S3.mem x etyp edata ret := by
    rw [hS3]; unfold Fx at hFx2 ⊢
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hFx2
  have hFx3 : Fx s m3 x etyp edata ret :=
    Fx.step (S := S3) hFx3' hS3spn hout (Or.inl rfl) hd' hfr3'
  have hi3 : m3.readLE ((s.regs 4).toNat - 64) 8 = 1 := by
    rw [hfr3'.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true, MapAmd64.calleeStack, hS3spn]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    exact hS3i
  clear hdef3 hkeep3 hS3f hS3fW hagS3 hS30 hS314 hS3x hS3df hS3pc hgS3 hS3sp hS3spn hS30n hm3 hpc3 hd2 hrm2 hsv2 hpn2 hW2 henv2 hfr3 hS3i hS3ra hfsp3 hFx2 hfr3' hi2 hstep
  subst hs3
  subst hS3
  janus64_run [hi3] until [Extracted.entry + 0x7a]
  refine ReachesRet.done rfl ?_
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, hW3, henv3, ?_, hsv3, hpn3, hrm3, hFx3⟩
  · simp [setRegF, MapAmd64.keepABI]; bv_omega
  · simp [setRegF, MapAmd64.keepABI]
  · simp [setRegF, MapAmd64.keepABI]
  · simpa [MapAmd64.keepX15] using h_x15
  · rfl
  · simpa using hd3

/-- The guarantee, as a predicate on outcomes. -/
def Post (s : State) (x etyp edata : BitVec 64) : GoOutcome → Prop := fun o =>
  match o with
  | .returned s' => ABIReturn s s' ∧ (x.toNat ≤ 10 ∧ (s'.regs 0).toNat = x.toNat ∧
      s'.mem.readLE accA 8 = mix (s.mem.readLE accA 8))
  | .panicked v s' => 10 < x.toNat ∧ v = ⟨etyp.toNat, edata.toNat⟩ ∧
      s'.mem.readLE accA 8 = mix (s.mem.readLE accA 8)
  | .goexited _ => False

/-- What the runtime and the deferred calls write: `P.priv`, the runtime's window below the frame,
and `Acc`. -/
abbrev winA (P : Spec.PanicRuntime) (s : State) : List (Nat × Nat) :=
  P.priv ++ [((s.regs 4).toNat - 88 - P.depth, (s.regs 4).toNat - 96), (accA, accA + 8)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
/-- `x ≤ 10`: the deferred calls run at the return (`runtime.deferreturn`) and `DeferMix` returns `x`. -/
theorem ret_run (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U)
    (x etyp edata : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (s : State) (hs : CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x, etyp, edata] s)
    (hpre : Pre P s etyp) (S : State) (hQ : AfterDefers P s S x etyp edata ret) (hx : x.toNat ≤ 10) :
    GoReturns ((Extracted.program.link impl).withExit ret) (goClassU P U s) S (Post s x etyp edata) := by
  obtain ⟨hc, hd, hacc, hao, hfo, hne, hroom, hsave, hdss⟩ := hpre
  have hc' := hc
  obtain ⟨henv, hg, hal, hd', hb, hst, hout, hgd, hgo⟩ := hc'
  obtain ⟨hSpc, hSsp, hS14, hS5, hSx, hSdf, hW, henvS, hdefS, hsvS, hpnS, hrmS, hFx⟩ := hQ
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd' hb hal hdss
  have h96 : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
    rw [BitVec.toNat_sub]; simp; omega
  have h88 : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 88 := by rw [hSsp]; exact h88
  have hr47 : ret < 2 ^ 47 := hret.user
  have hx0 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = x.toNat := hFx.1
  have hxl : S.mem.readLE (s.regs 4).toNat 8 = ret := hFx.2.2.2.1
  have hxf : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := hFx.2.2.2.2
  have hao2 : accA + 8 ≤ (s.regs 4).toNat - (P.depth + 96) ∨ (s.regs 4).toNat + 32 ≤ accA := by
    have h := hao
    simp only [outside_append, outside_cons, outside_nil, and_true] at h
    exact h.2
  have hxlt := x.isLt
  obtain ⟨dr, drip, dfl, dxm, dm, dyh, dfs, ddf, dmx⟩ := S
  dsimp only at *
  have hSpc' : drip = BitVec.ofNat 64 loc_DeferMix_122 := hSpc
  subst hSpc' hSdf
  have hdr' : dr = setRegF (setRegF (setRegF dr 4 (s.regs 4 - 88#64)) 5 (s.regs 4 - 8#64)) 14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact hS14
    · rw [if_neg h14]
      by_cases h5 : i = 5
      · rw [if_pos h5, h5]; exact hS5
      · rw [if_neg h5]
        by_cases h4 : i = 4
        · rw [if_pos h4, h4]; exact hSsp
        · rw [if_neg h4]
  rw [hdr']
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn"))
    hret.fetch_none ?_
  janus64_run [hx0, hx] until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun D hD => ?_
  have hDsp : D.regs 4 = s.regs 4 - 96#64 := by rw [hD] <;> simp [setRegF]
  have hDspn : (D.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hDsp]; exact h96
  have hDf : MemFrame dm D.mem [((s.regs 4).toNat - 96, (s.regs 4).toNat - 72 + 8)] := by
    rw [hD]; janus_frame
  have hD14 : D.regs 14 = s.regs 14 := by rw [hD] <;> simp [setRegF]
  have hD5 : D.regs 5 = s.regs 4 - 8#64 := by rw [hD] <;> simp [setRegF]
  have hDx : D.xmm 15 = 0 := by rw [hD]; exact hSx
  have hDdf : D.df = false := by rw [hD]
  have hDpc : D.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by
    rw [hD] <;> rfl
  have hgD : gOf D = gOf s := by simp only [gOf, hD14]
  have hDra : D.mem.readLE (D.regs 4).toNat 8 = loc_DeferMix_144 := by
    rw [hD]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h96, Janus.Arm64.Memory.readLE_writeLE_self]
  have hDfW : MemFrame s.mem D.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) :=
    hW.trans hDf fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      omega⟩
  have hagD : Spec.Map.Agrees dm D.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - 96) (hi := (s.regs 4).toNat - 72 + 8) hDf
      (Outside.of_sub hout (by omega) (by omega))
  have hpre : PanicPre P 0 D := PanicPre.of_within hc hDfW (hl.env_frame _ _ henvS hagD) (by omega) (by omega)
    (by omega) hD14 hDx hDdf (by rw [hDra]; decide)
  have hsvD : P.saved D.mem (gOf D) = none := by rw [hgD, hl.saved_frame _ _ _ hagD]; exact hsvS
  have hdD : P.defers D.mem (gOf D) = [{ sp := (s.regs 4).toNat - 88, fns := [fvA + 8] },
      { sp := (s.regs 4).toNat - 88, fns := [fvA + 8] }, { sp := (s.regs 4).toNat - 88, fns := [fvA] }] ++
      P.defers s.mem (gOf s) := by
    rw [hgD, hl.defers_frame _ _ _ hagD]; exact hdefS
  have hfspD : fspOf D = (s.regs 4).toNat - 88 := by simp only [fspOf, hDspn]; omega
  have hF : retFrame P D = ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat - 88, 0, none⟩ := by
    simp only [retFrame, hsvD, hfspD]
  have hds' : ∀ d ∈ P.defers s.mem (gOf s), (s.regs 4).toNat - 88 < d.sp := fun d hd => by
    have := hdss d hd; omega
  have hrA := recItems_above hds'
  have hI : frameItems D.mem (retFrame P D) (P.defers D.mem (gOf D)) =
      [{ fn := fvA + 8, bits := none, chain := { sp := (s.regs 4).toNat - 88, fns := [fvA + 8] } ::
          { sp := (s.regs 4).toNat - 88, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA + 8, bits := none,
         chain := { sp := (s.regs 4).toNat - 88, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] := by
    rw [hF, hdD]
    simp [frameItems, recItems, fnItems, hrA]
  have hfo1 : Outside fvA 8 (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) :=
    Outside.of_sub hfo (by omega) (by omega)
  have hfo2 : Outside (fvA + 8) 8 (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) :=
    Outside.of_sub hfo (by omega) (by omega)
  have hfv1 : D.mem.readLE fvA 8 = accAdd1A := by rw [hDfW.readLE _ _ hfo1]; exact fv1_read _ hd
  have hfv2 : D.mem.readLE (fvA + 8) 8 = accAdd2A := by rw [hDfW.readLE _ _ hfo2]; exact fv2_read _ hd
  have hfa1 : D.mem.accessible fvA 8 false = true := by
    rw [hDfW.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ (fv_acc _ hd) (by omega) (by omega)
  have hfa2 : D.mem.accessible (fvA + 8) 8 false = true := by
    rw [hDfW.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ (fv_acc _ hd) (by omega) (by omega)
  have hFO : FrameOK P D.mem (retFrame P D) (frameItems D.mem (retFrame P D) (P.defers D.mem (gOf D))) := by
    rw [hI, hF]
    simp only [outside_append, outside_cons, outside_nil, and_true] at hfo
    refine ⟨⟨trivial, fun it hit => ?_⟩, fun it hit => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl | rfl <;> dsimp only
      · exact ⟨by omega, hfa2, by rw [hfv2], by rw [hfv2]; decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
      · exact ⟨by omega, hfa2, by rw [hfv2], by rw [hfv2]; decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
      · exact ⟨by omega, hfa1, by rw [hfv1], by rw [hfv1]; decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl | rfl <;> dsimp only
      · rw [hfv2]; decide
      · rw [hfv2]; decide
      · rw [hfv1]; decide
  have hpaD : D.mem.accessible accA 8 true = true := by rw [hDfW.accessible]; exact hacc
  have hv0 : D.mem.readLE accA 8 = s.mem.readLE accA 8 := hDfW.readLE _ _ hao
  have hKp : frameKeep D.mem ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat - 88, 0, none⟩
      [{ fn := fvA + 8, bits := none, chain := { sp := (s.regs 4).toNat - 88, fns := [fvA + 8] } ::
          { sp := (s.regs 4).toNat - 88, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA + 8, bits := none,
         chain := { sp := (s.regs 4).toNat - 88, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] =
      [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)] := by
    simp [frameKeep, Frame.openAt]
  have hsubR : ∀ a n, Outside a n (winA P s) →
      Outside a n (P.priv ++ rtWin P ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat - 88, 0, none⟩ ++
        bitsWin ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat - 88, 0, none⟩) := by
    intro a n h
    simp only [winA, rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at h ⊢
    exact ⟨h.1, h.2.1⟩
  have hoT : Outside accA 8 (P.priv ++ rtWin P ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat - 88, 0, none⟩ ++
      bitsWin ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat - 88, 0, none⟩) := by
    have hao' := hao
    simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at hao' ⊢
    exact ⟨hao'.1, by omega⟩
  have hsubA : ∀ a n, Outside a n (winA P s) → Outside a n [(accA, accA + 8)] := by
    intro a n h
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact h.2.2
  have hoA : ∀ (e : State), (s.regs 4).toNat - 88 - P.depth ≤ (e.regs 4).toNat →
      Outside accA (accA + 8 - accA) (P.priv ++ ((e.regs 4).toNat + 8, (s.regs 4).toNat - 88) ::
        [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) := by
    intro e hlo
    have hao' := hao
    simp only [outside_append, outside_cons, outside_nil, and_true] at hao' ⊢
    simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hao'.1, by omega, by omega, by omega, by omega⟩
  have hacD : ∀ (e : State), (s.regs 4).toNat - 88 - P.depth ≤ (e.regs 4).toNat →
      (e.regs 4).toNat + 16 ≤ (s.regs 4).toNat - 88 →
      ∀ m : Janus.Arm64.Memory, (∀ a n w, m.accessible a n w = D.mem.accessible a n w) →
      m.accessible (e.regs 4).toNat 8 false = true := by
    intro e h1 h2 m hm
    rw [hm, hDfW.accessible]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
  refine DeferreturnContract.apply (S := D) hdr hDpc ⟨hpre, hFO⟩ ?_
  intro hE
  rw [hI, hF] at hE
  rw [hKp] at hE
  -- the first deferred call (the last heap record): `Acc = Acc*10 + 2`
  rw [Engine_cons] at hE
  obtain ⟨k1, e1, hst1, ⟨hpc1, h2_1, h14_1, hx1, hdf1, hal1, hlo1, hhi1, hra1, henvE1⟩,
    hfrE1, -, -, hpn1, -, -, hcont1, -⟩ := hE
  dsimp only at hpc1 h2_1 hlo1 hhi1 hra1 hfrE1 hcont1
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
  have hrac1 : e1.mem.accessible (e1.regs 4).toNat 8 false = true :=
    hacD e1 hlo1 hhi1 e1.mem (fun a n w => by rw [hae1.accessible])
  have hcl1 := call_acc2 impl e1 hpc1 hpa1 hra1 hrac1 (by omega)
  obtain ⟨j1, f1, hj1, -, hfpc1, hfsp1, hf141, hf51, hfx1, hfdf1, hff1, hpv1⟩ := hcl1
  refine GoReturns.of_steps (hj1.withExit hret.fetch_none) ?_
  have hw1 : f1.mem.readLE accA 8 = digit 2 (s.mem.readLE accA 8) := by rw [hpv1, hv1]
  have hacc1 : MemFrame D.mem f1.mem (winA P s) := hae1.trans hff1 fun a n h => ⟨h, hsubA a n h⟩
  obtain ⟨hdr1, hpf1⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 88)
    (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl
    (by rw [hfpc1, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)) hfsp1
    (hf141.trans h14_1) hf51 (by rw [hfx1]; exact hx1) (by rw [hfdf1]; exact hdf1) henvE1 hff1
    (hoA e1 hlo1)
  have hE1 := (hcont1 f1 hdr1).1 (hpf1.trans hpn1)
  -- the second deferred call (the first heap record): `Acc = Acc*10 + 2`
  rw [Engine_cons] at hE1
  obtain ⟨k2, e2, hst2, ⟨hpc2, h2_2, h14_2, hx2, hdf2, hal2, hlo2, hhi2, hra2, henvE2⟩,
    hfrE2, -, -, hpn2, -, -, hcont2, -⟩ := hE1
  dsimp only at hpc2 h2_2 hlo2 hhi2 hra2 hfrE2 hcont2
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
  have hrac2 : e2.mem.accessible (e2.regs 4).toNat 8 false = true :=
    hacD e2 hlo2 hhi2 e2.mem (fun a n w => by rw [hae2.accessible])
  have hcl2 := call_acc2 impl e2 hpc2 hpa2 hra2 hrac2 (by omega)
  obtain ⟨j2, f2, hj2, -, hfpc2, hfsp2, hf142, hf52, hfx2, hfdf2, hff2, hpv2⟩ := hcl2
  refine GoReturns.of_steps (hj2.withExit hret.fetch_none) ?_
  have hw2 : f2.mem.readLE accA 8 = digit 2 (digit 2 (s.mem.readLE accA 8)) := by rw [hpv2, hv2]
  have hacc2 : MemFrame D.mem f2.mem (winA P s) := hae2.trans hff2 fun a n h => ⟨h, hsubA a n h⟩
  obtain ⟨hdr2, hpf2⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 88)
    (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl
    (by rw [hfpc2, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)) hfsp2
    (hf142.trans h14_2) hf52 (by rw [hfx2]; exact hx2) (by rw [hfdf2]; exact hdf2) henvE2 hff2
    (hoA e2 hlo2)
  have hE2 := (hcont2 f2 hdr2).1 (hpf2.trans hpn2)
  -- the third deferred call (the stack record): `Acc = Acc*10 + 1`
  rw [Engine_cons] at hE2
  obtain ⟨k3, e3, hst3, ⟨hpc3, h2_3, h14_3, hx3, hdf3, hal3, hlo3, hhi3, hra3, henvE3⟩,
    hfrE3, -, -, hpn3, -, -, hcont3, -⟩ := hE2
  dsimp only at hpc3 h2_3 hlo3 hhi3 hra3 hfrE3 hcont3
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
  have hrac3 : e3.mem.accessible (e3.regs 4).toNat 8 false = true :=
    hacD e3 hlo3 hhi3 e3.mem (fun a n w => by rw [hae3.accessible])
  have hcl3 := call_acc1 impl e3 hpc3 hpa3 hra3 hrac3 (by omega)
  obtain ⟨j3, f3, hj3, -, hfpc3, hfsp3, hf143, hf53, hfx3, hfdf3, hff3, hpv3⟩ := hcl3
  refine GoReturns.of_steps (hj3.withExit hret.fetch_none) ?_
  have hw3 : f3.mem.readLE accA 8 = digit 1 (digit 2 (digit 2 (s.mem.readLE accA 8))) := by
    rw [hpv3, hv3]
  have hacc3 : MemFrame D.mem f3.mem (winA P s) := hae3.trans hff3 fun a n h => ⟨h, hsubA a n h⟩
  obtain ⟨hdr3, hpf3⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 88)
    (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl
    (by rw [hfpc3, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)) hfsp3
    (hf143.trans h14_3) hf53 (by rw [hfx3]; exact hx3) (by rw [hfdf3]; exact hdf3) henvE3 hff3
    (hoA e3 hlo3)
  have hE3 := (hcont3 f3 hdr3).1 (hpf3.trans hpn3)
  rw [Engine_nil] at hE3
  obtain ⟨k4, d, hst4, hfin⟩ := hE3
  obtain ⟨hfpc, hfsp, hf14, hf5, hfx, hfdf, hfmf, hfenv, -⟩ := hfin
  refine GoReturns.of_steps (hst4.withExit hret.fetch_none) ?_
  obtain ⟨er, erip, efl, exm, em, eyh, efs, edf, emx⟩ := d
  dsimp only at hfpc hfsp hf14 hf5 hfx hfdf hfmf hfenv
  rw [hDra] at hfpc
  have hepc : erip = BitVec.ofNat 64 loc_DeferMix_144 := by
    apply BitVec.eq_of_toNat_eq; rw [hfpc, BitVec.toNat_ofNat]
  subst hepc hfdf
  have he4 : er 4 = s.regs 4 - 88#64 := by
    rw [hfsp, hDsp]; apply BitVec.eq_of_toNat_eq
    have := (s.regs 4).isLt
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_sub]
    simp; omega
  have he5 : er 5 = s.regs 4 - 8#64 := by rw [hf5, hD5]
  have he14 : er 14 = s.regs 14 := by rw [hf14, hD14]
  have her : er = setRegF (setRegF (setRegF er 4 (s.regs 4 - 88#64)) 5 (s.regs 4 - 8#64)) 14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact he14
    · rw [if_neg h14]
      by_cases h5 : i = 5
      · rw [if_pos h5, h5]; exact he5
      · rw [if_neg h5]
        by_cases h4 : i = 4
        · rw [if_pos h4, h4]; exact he4
        · rw [if_neg h4]
  rw [her]
  simp only [rtWin, bitsWin, hF, List.append_nil] at hfmf
  have hDx7 : D.mem.readLE ((s.regs 4).toNat - 72) 8 = x.toNat := by
    rw [hD]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                               omega)
  have hDl : D.mem.readLE (s.regs 4).toNat 8 = ret := by
    rw [hD]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hxl
  have hDf8 : D.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hD]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hxf
  have hxfer : ∀ a n v, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - 88 - P.depth ∨ (s.regs 4).toNat - 96 ≤ a) →
      (a + n ≤ accA ∨ accA + 8 ≤ a) → D.mem.readLE a n = v → em.readLE a n = v := by
    intro a n v hpr h1 h2 hv
    rw [hfmf.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpr, h1⟩),
      hacc3.readLE _ _ (by
      simp only [winA, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpr, h1, h2⟩)]
    exact hv
  have hdx : em.readLE ((s.regs 4).toNat - 72) 8 = x.toNat :=
    hxfer _ _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) hDx7
  have hdl : em.readLE (s.regs 4).toNat 8 = ret :=
    hxfer _ _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) hDl
  have hdf8 : em.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat :=
    hxfer _ _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) hDf8
  have hdA : em.readLE accA 8 = mix (s.mem.readLE accA 8) := by
    rw [hfmf.readLE _ _ (by
      have hao' := hao
      simp only [outside_append, outside_cons, outside_nil, and_true] at hao' ⊢
      exact ⟨hao'.1, by omega⟩)]
    exact hw3
  have hdacc : em.accessible ((s.regs 4).toNat - 96) 104 true = true := by
    rw [hfmf.accessible, hacc3.accessible, hDfW.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
  clear hst1 hst2 hst3 hst4 hj1 hj2 hj3 hfmf hfrE1 hfrE2 hfrE3 hcont1 hcont2 hcont3
  refine GoReturns.of_reaches ?_
  janus64_run [hdl, hdf8, hdx, hx]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hx, ?_, hdA⟩
  · simp [setRegF, regSP]
  · simp [setRegF, regFP]
  · simp [setRegF, regG]
  · simp only [regSP, regG, regFP, xmmZero]; rw [hfx, h_x15]
  · simp [setRegF]


set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
/-- `x > 10`: `panic(e)` runs the deferred calls (`runtime.gopanic`) and `DeferMix` panics with `e`. -/
theorem panic_run (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hpan : GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs)
    (x etyp edata : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (s : State) (hs : CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x, etyp, edata] s)
    (hpre : Pre P s etyp) (S : State) (hQ : AfterDefers P s S x etyp edata ret) (hx : ¬ x.toNat ≤ 10) :
    GoReturns ((Extracted.program.link impl).withExit ret) (goClassU P U s) S (Post s x etyp edata) := by
  obtain ⟨hc, hd, hacc, hao, hfo, hne, hroom, hsave, hdss⟩ := hpre
  have hc' := hc
  obtain ⟨henv, hg, hal, hd', hb, hst, hout, hgd, hgo⟩ := hc'
  obtain ⟨hSpc, hSsp, hS14, hS5, hSx, hSdf, hW, henvS, hdefS, hsvS, hpnS, hrmS, hFx⟩ := hQ
  have hx' : 10 < x.toNat := by omega
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd' hb hal hdss
  have h96 : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
    rw [BitVec.toNat_sub]; simp; omega
  have h88 : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 88 := by rw [hSsp]; exact h88
  have hr47 : ret < 2 ^ 47 := hret.user
  have hx0 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = x.toNat := hFx.1
  have hx1 : S.mem.readLE ((s.regs 4).toNat + 16) 8 = etyp.toNat := hFx.2.1
  have hx2 : S.mem.readLE ((s.regs 4).toNat + 24) 8 = edata.toNat := hFx.2.2.1
  have hxl : S.mem.readLE (s.regs 4).toNat 8 = ret := hFx.2.2.2.1
  have hxf : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := hFx.2.2.2.2
  have hao2 : accA + 8 ≤ (s.regs 4).toNat - (P.depth + 96) ∨ (s.regs 4).toNat + 32 ≤ accA := by
    have h := hao
    simp only [outside_append, outside_cons, outside_nil, and_true] at h
    exact h.2
  have hxlt := x.isLt
  obtain ⟨dr, drip, dfl, dxm, dm, dyh, dfs, ddf, dmx⟩ := S
  dsimp only at *
  have hSpc' : drip = BitVec.ofNat 64 loc_DeferMix_122 := hSpc
  subst hSpc' hSdf
  have hdr' : dr = setRegF (setRegF (setRegF dr 4 (s.regs 4 - 88#64)) 5 (s.regs 4 - 8#64)) 14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact hS14
    · rw [if_neg h14]
      by_cases h5 : i = 5
      · rw [if_pos h5, h5]; exact hS5
      · rw [if_neg h5]
        by_cases h4 : i = 4
        · rw [if_pos h4, h4]; exact hSsp
        · rw [if_neg h4]
  rw [hdr']
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
    hret.fetch_none ?_
  janus64_run [hx0, hx1, hx2, hx'] until [Extracted.program.contractAddr "runtime.gopanic"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun G hG => ?_
  have hGsp : G.regs 4 = s.regs 4 - 96#64 := by rw [hG] <;> simp [setRegF]
  have hGspn : (G.regs 4).toNat = (s.regs 4).toNat - 96 := by rw [hGsp]; exact h96
  have hG0 : G.regs 0 = etyp := by rw [hG] <;> simp [setRegF]
  have hG3 : G.regs 3 = edata := by rw [hG] <;> simp [setRegF]
  have hG14 : G.regs 14 = s.regs 14 := by rw [hG] <;> simp [setRegF]
  have hGx : G.xmm 15 = 0 := by rw [hG]; exact hSx
  have hGdf : G.df = false := by rw [hG]
  have hGpc : G.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by
    rw [hG] <;> rfl
  have hGf : MemFrame dm G.mem [((s.regs 4).toNat - 96, (s.regs 4).toNat - 96 + 8)] := by
    rw [hG]; janus_frame
  have hGra : G.mem.readLE (G.regs 4).toNat 8 = loc_DeferMix_170 := by
    rw [hG]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h96, Janus.Arm64.Memory.readLE_writeLE_self]
  have hgG : gOf G = gOf s := by simp only [gOf, hG14]
  have hGfW : MemFrame s.mem G.mem
      (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) :=
    hW.trans hGf fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      omega⟩
  have hagG : Spec.Map.Agrees dm G.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - 96) (hi := (s.regs 4).toNat - 96 + 8) hGf
      (Outside.of_sub hout (by omega) (by omega))
  obtain ⟨fi, hfi⟩ : ∃ fi : Spec.FuncInfo, fi = Spec.FuncInfo.named Extracted.funcs "example.com/basic.DeferMix" :=
    ⟨_, rfl⟩
  have f_frame : fi.frame = 88 := by rw [hfi]; rfl
  have f_od : fi.openDefer = none := by rw [hfi]; rfl
  have f_res : fi.resume = Extracted.entry + 0x49 := by rw [hfi]; rfl
  have hdG : P.defers G.mem (gOf G) = [{ sp := (s.regs 4).toNat - 88, fns := [fvA + 8] },
      { sp := (s.regs 4).toNat - 88, fns := [fvA + 8] }, { sp := (s.regs 4).toNat - 88, fns := [fvA] }] ++
      P.defers s.mem (gOf s) := by
    rw [hgG, hl.defers_frame _ _ _ hagG]; exact hdefS
  have hfspG : fspOf G = (s.regs 4).toNat - 88 := by simp only [fspOf, hGspn]; omega
  have hF : frameOf fi (fspOf G) G.mem =
      ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat, Extracted.entry + 0x49, none⟩ := by
    simp only [frameOf, Panic.frameOf, Spec.FuncInfo.bound, f_frame, f_od, hfspG, Option.map_none, f_res]
    have e3 : (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat := by omega
    rw [e3]
  have hds' : ∀ d ∈ P.defers s.mem (gOf s), (s.regs 4).toNat - 88 < d.sp := fun d hd => by
    have := hdss d hd; omega
  have hrA := recItems_above hds'
  have hI : frameItems G.mem (frameOf fi (fspOf G) G.mem) (P.defers G.mem (gOf G)) =
      [{ fn := fvA + 8, bits := none, chain := { sp := (s.regs 4).toNat - 88, fns := [fvA + 8] } ::
          { sp := (s.regs 4).toNat - 88, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA + 8, bits := none,
         chain := { sp := (s.regs 4).toNat - 88, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] := by
    rw [hF, hdG]
    simp [frameItems, recItems, fnItems, hrA]
  have hfo1 : Outside fvA 8 (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) :=
    Outside.of_sub hfo (by omega) (by omega)
  have hfo2 : Outside (fvA + 8) 8 (P.priv ++ [((s.regs 4).toNat - (P.depth + 96), (s.regs 4).toNat + 32)]) :=
    Outside.of_sub hfo (by omega) (by omega)
  have hfv1 : G.mem.readLE fvA 8 = accAdd1A := by rw [hGfW.readLE _ _ hfo1]; exact fv1_read _ hd
  have hfv2 : G.mem.readLE (fvA + 8) 8 = accAdd2A := by rw [hGfW.readLE _ _ hfo2]; exact fv2_read _ hd
  have hfa1 : G.mem.accessible fvA 8 false = true := by
    rw [hGfW.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ (fv_acc _ hd) (by omega) (by omega)
  have hfa2 : G.mem.accessible (fvA + 8) 8 false = true := by
    rw [hGfW.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ (fv_acc _ hd) (by omega) (by omega)
  have hpaD : G.mem.accessible accA 8 true = true := by rw [hGfW.accessible]; exact hacc
  have hv0 : G.mem.readLE accA 8 = s.mem.readLE accA 8 := hGfW.readLE _ _ hao
  have hKp : frameKeep G.mem ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat, Extracted.entry + 0x49, none⟩
      [{ fn := fvA + 8, bits := none, chain := { sp := (s.regs 4).toNat - 88, fns := [fvA + 8] } ::
          { sp := (s.regs 4).toNat - 88, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA + 8, bits := none,
         chain := { sp := (s.regs 4).toNat - 88, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] =
      [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)] := by
    simp [frameKeep, Frame.openAt]
  have hsubR : ∀ a n, Outside a n (winA P s) →
      Outside a n (P.priv ++ rtWin P ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat, Extracted.entry + 0x49, none⟩ ++
        bitsWin ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat, Extracted.entry + 0x49, none⟩) := by
    intro a n h
    simp only [winA, rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at h ⊢
    exact ⟨h.1, h.2.1⟩
  have hoT : Outside accA 8 (P.priv ++ rtWin P ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat, Extracted.entry + 0x49, none⟩ ++
      bitsWin ⟨(s.regs 4).toNat - 88, (s.regs 4).toNat, Extracted.entry + 0x49, none⟩) := by
    have hao' := hao
    simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at hao' ⊢
    exact ⟨hao'.1, by omega⟩
  have hsubA : ∀ a n, Outside a n (winA P s) → Outside a n [(accA, accA + 8)] := by
    intro a n h
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact h.2.2
  have hoA : ∀ (e : State), (s.regs 4).toNat - 88 - P.depth ≤ (e.regs 4).toNat →
      Outside accA (accA + 8 - accA) (P.priv ++ ((e.regs 4).toNat + 8, (s.regs 4).toNat - 88) ::
        [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) := by
    intro e hlo
    have hao' := hao
    simp only [outside_append, outside_cons, outside_nil, and_true] at hao' ⊢
    simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hao'.1, by omega, by omega, by omega, by omega⟩
  have hacD : ∀ (e : State), (s.regs 4).toNat - 88 - P.depth ≤ (e.regs 4).toNat →
      (e.regs 4).toNat + 16 ≤ (s.regs 4).toNat - 88 →
      ∀ m : Janus.Arm64.Memory, (∀ a n w, m.accessible a n w = G.mem.accessible a n w) →
      m.accessible (e.regs 4).toNat 8 false = true := by
    intro e h1 h2 m hm
    rw [hm, hGfW.accessible]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
  refine GopanicContract.apply (fi := fi) hpan hGpc (by rw [hGra, hfi]; rfl) ?_ ?_
  · refine ⟨PanicPre.of_within hc hGfW (hl.env_frame _ _ henvS hagG) (by omega) (by omega)
        (by omega) hG14 hGx hGdf (by rw [hGra]; decide),
      by rw [hG0]; exact hne, ?_, ?_, ?_⟩
    · rw [hgG, hl.room_frame _ _ _ hagG]; omega
    · intro h; rw [f_od] at h; cases h
    · rw [hI, hF]
      simp only [outside_append, outside_cons, outside_nil, and_true] at hfo
      refine ⟨⟨trivial, fun it hit => ?_⟩, fun it hit => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl | rfl <;> dsimp only
        · exact ⟨by omega, hfa2, by rw [hfv2], by rw [hfv2]; decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
        · exact ⟨by omega, hfa2, by rw [hfv2], by rw [hfv2]; decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
        · exact ⟨by omega, hfa1, by rw [hfv1], by rw [hfv1]; decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl | rfl <;> dsimp only
        · rw [hfv2]; decide
        · rw [hfv2]; decide
        · rw [hfv1]; decide
  intro hE
  rw [hI, hF] at hE
  rw [hKp] at hE
  -- the first deferred call (the last heap record): `Acc = Acc*10 + 2`
  rw [Engine_cons] at hE
  obtain ⟨k1, e1, hst1, ⟨hpc1, h2_1, h14_1, hx1, hdf1, hal1, hlo1, hhi1, hra1, henvE1⟩,
    hfrE1, -, -, hpn1, -, -, hcont1, -⟩ := hE
  dsimp only at hpc1 h2_1 hlo1 hhi1 hra1 hfrE1 hcont1
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
  have hrac1 : e1.mem.accessible (e1.regs 4).toNat 8 false = true :=
    hacD e1 hlo1 hhi1 e1.mem (fun a n w => by rw [hae1.accessible])
  have hcl1 := call_acc2 impl e1 hpc1 hpa1 hra1 hrac1 (by omega)
  obtain ⟨j1, f1, hj1, -, hfpc1, hfsp1, hf141, hf51, hfx1, hfdf1, hff1, hpv1⟩ := hcl1
  refine GoReturns.of_steps (hj1.withExit hret.fetch_none) ?_
  have hw1 : f1.mem.readLE accA 8 = digit 2 (s.mem.readLE accA 8) := by rw [hpv1, hv1]
  have hacc1 : MemFrame G.mem f1.mem (winA P s) := hae1.trans hff1 fun a n h => ⟨h, hsubA a n h⟩
  obtain ⟨hdr1, hpf1⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 88)
    (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl
    (by rw [hfpc1, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)) hfsp1
    (hf141.trans h14_1) hf51 (by rw [hfx1]; exact hx1) (by rw [hfdf1]; exact hdf1) henvE1 hff1
    (hoA e1 hlo1)
  have hE1 := (hcont1 f1 hdr1).1 (hpf1.trans hpn1)
  -- the second deferred call (the first heap record): `Acc = Acc*10 + 2`
  rw [Engine_cons] at hE1
  obtain ⟨k2, e2, hst2, ⟨hpc2, h2_2, h14_2, hx2, hdf2, hal2, hlo2, hhi2, hra2, henvE2⟩,
    hfrE2, -, -, hpn2, -, -, hcont2, -⟩ := hE1
  dsimp only at hpc2 h2_2 hlo2 hhi2 hra2 hfrE2 hcont2
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
  have hrac2 : e2.mem.accessible (e2.regs 4).toNat 8 false = true :=
    hacD e2 hlo2 hhi2 e2.mem (fun a n w => by rw [hae2.accessible])
  have hcl2 := call_acc2 impl e2 hpc2 hpa2 hra2 hrac2 (by omega)
  obtain ⟨j2, f2, hj2, -, hfpc2, hfsp2, hf142, hf52, hfx2, hfdf2, hff2, hpv2⟩ := hcl2
  refine GoReturns.of_steps (hj2.withExit hret.fetch_none) ?_
  have hw2 : f2.mem.readLE accA 8 = digit 2 (digit 2 (s.mem.readLE accA 8)) := by rw [hpv2, hv2]
  have hacc2 : MemFrame G.mem f2.mem (winA P s) := hae2.trans hff2 fun a n h => ⟨h, hsubA a n h⟩
  obtain ⟨hdr2, hpf2⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 88)
    (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl
    (by rw [hfpc2, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)) hfsp2
    (hf142.trans h14_2) hf52 (by rw [hfx2]; exact hx2) (by rw [hfdf2]; exact hdf2) henvE2 hff2
    (hoA e2 hlo2)
  have hE2 := (hcont2 f2 hdr2).1 (hpf2.trans hpn2)
  -- the third deferred call (the stack record): `Acc = Acc*10 + 1`
  rw [Engine_cons] at hE2
  obtain ⟨k3, e3, hst3, ⟨hpc3, h2_3, h14_3, hx3, hdf3, hal3, hlo3, hhi3, hra3, henvE3⟩,
    hfrE3, -, -, hpn3, -, -, hcont3, -⟩ := hE2
  dsimp only at hpc3 h2_3 hlo3 hhi3 hra3 hfrE3 hcont3
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
  have hrac3 : e3.mem.accessible (e3.regs 4).toNat 8 false = true :=
    hacD e3 hlo3 hhi3 e3.mem (fun a n w => by rw [hae3.accessible])
  have hcl3 := call_acc1 impl e3 hpc3 hpa3 hra3 hrac3 (by omega)
  obtain ⟨j3, f3, hj3, -, hfpc3, hfsp3, hf143, hf53, hfx3, hfdf3, hff3, hpv3⟩ := hcl3
  refine GoReturns.of_steps (hj3.withExit hret.fetch_none) ?_
  have hw3 : f3.mem.readLE accA 8 = digit 1 (digit 2 (digit 2 (s.mem.readLE accA 8))) := by
    rw [hpv3, hv3]
  have hacc3 : MemFrame G.mem f3.mem (winA P s) := hae3.trans hff3 fun a n h => ⟨h, hsubA a n h⟩
  obtain ⟨hdr3, hpf3⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 88)
    (keep := [(fvA + 8, fvA + 8 + 8), (fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl
    (by rw [hfpc3, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)) hfsp3
    (hf143.trans h14_3) hf53 (by rw [hfx3]; exact hx3) (by rw [hfdf3]; exact hdf3) henvE3 hff3
    (hoA e3 hlo3)
  have hE3 := (hcont3 f3 hdr3).1 (hpf3.trans hpn3)
  rw [Engine_nil] at hE3
  obtain ⟨k4, d, hst4, hU, hpd, -, hfrd, -, -, -⟩ := hE3
  refine GoReturns.leave (v := ⟨etyp.toNat, edata.toNat⟩) (hst4.withExit hret.fetch_none) ?_ ?_
  · have hg' : gOf s = (G.regs 14).toNat := by simp only [gOf, hG14]
    have hU' := hU; rw [← hg'] at hU'
    have hpd' := hpd; rw [show (G.regs 14).toNat = gOf s from hg'.symm] at hpd'
    refine ⟨hU', _, _, hpd', ?_, rfl⟩
    simp only [hG0, hG3]
  · refine ⟨hx', rfl, ?_⟩
    rw [hfrd.readLE _ _ hoT]; exact hw3


set_option maxHeartbeats 0 in
theorem correctness (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
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
      (fun s => Pre P s etyp)
      (goClassU P U)
      (fun s s' => x.toNat ≤ 10 ∧ (s'.regs 0).toNat = x.toNat ∧
        s'.mem.readLE accA 8 = mix (s.mem.readLE accA 8))
      (fun s v s' => 10 < x.toNat ∧ v = ⟨etyp.toNat, edata.toNat⟩ ∧
        s'.mem.readLE accA 8 = mix (s.mem.readLE accA 8)) := by
  intro ret hret s hs hpre
  obtain ⟨k0, S, hst0, hpc0, hQ⟩ := prefix_run impl P hl hds hdp x etyp edata ret hret s hs hpre
  refine GoReturns.of_steps (hst0.withExit hret.fetch_none) ?_
  by_cases hx : x.toNat ≤ 10
  · exact ret_run impl P hl U hdr x etyp edata ret hret s hs hpre S hQ hx
  · exact panic_run impl P hl U hpan x etyp edata ret hret s hs hpre S hQ hx

/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSatAmd64` (code that
`PanicSatAmd64Run`/`PanicSatAmd64Entry` prove meets the four contracts in every program that contains
it) linked into `DeferMix`'s program with a `jmp` to it at each contract address, and a call state
satisfying the precondition (an `any` of type word `1`, `x = 11`): so `correctness` applies
(`nonvacuous`), and `DeferMix` panics from that state (`returns`). -/

namespace Witness

open Janus.Contracts.PanicSat (tabWords witMemD witRet witArg)
open Janus.Contracts.PanicSatAmd64
open Janus.Contracts.PanicModel

abbrev T0 : List Spec.FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : Spec.PanicRuntime := P0 T0 RPa

def dsA : Nat := Extracted.program.contractAddr "runtime.deferprocStack"
def dpA : Nat := Extracted.program.contractAddr "runtime.deferproc"
def gA : Nat := Extracted.program.contractAddr "runtime.gopanic"
def drA : Nat := Extracted.program.contractAddr "runtime.deferreturn"

/-- The code linked next to `DeferMix`: the model engine and a `jmp` to it at each contract address. -/
def implW : List Janus.Amd64.Segment :=
  panicImpl Extracted.program [("runtime.deferprocStack", eDeferprocStack), ("runtime.deferproc", eDeferproc),
    ("runtime.gopanic", eGopanic), ("runtime.deferreturn", eDeferreturn)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

set_option maxRecDepth 100000 in
theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubDs : StubAt (Extracted.program.link implW) dsA eDeferprocStack :=
  StubAt.of_jmp (bs := stubCode dsA eDeferprocStack) (rel := (eDeferprocStack + 2 ^ 64 - (dsA + 5)) % 2 ^ 64)
    (len := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubDp : StubAt (Extracted.program.link implW) dpA eDeferproc :=
  StubAt.of_jmp (bs := stubCode dpA eDeferproc) (rel := (eDeferproc + 2 ^ 64 - (dpA + 5)) % 2 ^ 64) (len := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubG : StubAt (Extracted.program.link implW) gA eGopanic :=
  StubAt.of_jmp (bs := stubCode gA eGopanic) (rel := (eGopanic + 2 ^ 64 - (gA + 5)) % 2 ^ 64) (len := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubDr : StubAt (Extracted.program.link implW) drA eDeferreturn :=
  StubAt.of_jmp (bs := stubCode drA eDeferreturn) (rel := (eDeferreturn + 2 ^ 64 - (drA + 5)) % 2 ^ 64)
    (len := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem hds : DeferprocStackContract (Extracted.program.link implW) dsA PW :=
  deferprocStack_at stubDs (deferprocStack_contract engineAt T0)

theorem hdp : DeferprocContract (Extracted.program.link implW) dpA PW :=
  deferproc_at stubDp (deferproc_contract engineAt T0)

theorem hpan : GopanicContract (Extracted.program.link implW) gA PW U1 T0 :=
  gopanic_at stubG (gopanic_run engineAt T0 tok)

theorem hdr : DeferreturnContract (Extracted.program.link implW) drA PW U1 :=
  deferreturn_at stubDr (deferreturn_run (T := T0) engineAt)

abbrev ret : Nat := witRet

/-- The witness memory, with `Acc` a writable word and the return address `ret` at `[wsp]`. -/
def wm : Janus.Arm64.Memory :=
  ⟨(witMemD (tabWords T0 ++ [(wsp, ret)]) Extracted.data).bytes,
    (witMemD (tabWords T0 ++ [(wsp, ret)]) Extracted.data).regions ++ [⟨accA, 8, true⟩]⟩

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
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg
      else if i = 0 then 11#64 else if i = 3 then 1#64 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wm }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [11#64, 1#64, 0#64] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, fun i h => ?_, rfl⟩
  simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
theorem pre : Pre PW s0 1#64 := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩,
    dataLoaded, by decide, ?_, ?_, by decide, ?_, ?_, ?_⟩
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
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime)
    (U : Janus.Amd64.State → Nat → Nat → Prop) (ret : Nat) (s : Janus.Amd64.State), P.Laws ∧
    DeferprocStackContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferprocStack") P ∧
    DeferprocContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferproc") P ∧
    GopanicContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gopanic") P U
      Extracted.funcs ∧
    DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P U ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [11#64, 1#64, 0#64] s ∧
    Pre P s 1#64 :=
  ⟨implW, PW, U1, ret, s0, P0_laws T0 RPa, hds, hdp, hpan, hdr, hret, setup, pre⟩

/-- So the guarantee is reached: with `x = 11` `DeferMix` panics with `e`, after the deferred
calls ran in LIFO order. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClassU PW U1 s0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ ((11#64 : BitVec 64).toNat ≤ 10 ∧
        (s'.regs 0).toNat = (11#64 : BitVec 64).toNat ∧ s'.mem.readLE accA 8 = mix (s0.mem.readLE accA 8))
    | .panicked v s' => 10 < (11#64 : BitVec 64).toNat ∧
        v = ⟨(1#64 : BitVec 64).toNat, (0#64 : BitVec 64).toNat⟩ ∧
        s'.mem.readLE accA 8 = mix (s0.mem.readLE accA 8)
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U1 hds hdp hpan hdr 11#64 1#64 0#64 ret hret s0 setup pre

end Witness

end Proof
