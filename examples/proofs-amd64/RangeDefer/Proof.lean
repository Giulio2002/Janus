import Janus
import Extracted

/-!
# `RangeDefer()`: defers in a range-over-func loop body run in LIFO order (amd64)

`RangeDefer` is `for x := range count2 { if x == 1 { defer accAdd1() } else { defer accAdd2() } }`
over the iterator `count2` (which yields 1 and 2). The defers belong to `RangeDefer`'s frame, not
the loop body closure's: `RangeDefer` gets a token from `runtime.deferrangefunc`, each iteration
of the body records its deferred call on it with `runtime.deferprocat`, the body itself calls
`runtime.deferreturn` (a no-op for its own frame), and `RangeDefer`'s exit (`runtime.deferreturn`)
runs the recorded calls in LIFO order. `accAdd1` / `accAdd2` append the digit 1 / 2 to the package
variable `Acc`.

**Guarantee (example 7 of docs/COVERAGE.md R6).** For every panic-runtime model `P` satisfying its
laws, every implementation of `runtime.deferrangefunc`, `runtime.deferprocat` and
`runtime.deferreturn` meeting their contracts (`Janus.Contracts.PanicAmd64`, pinned to the Go 1.26
runtime's code), every admissible return address and every call state in which the runtime is
usable (with the stack for `RangeDefer`, `count2` and the body below), `Acc` is a writable word and
the two deferred functions' funcvals are in memory, with room for three records: the call
**returns** (obeying the ABI) and `Acc` ends as `(Acc*10+2)*10+1` (mod `2^64`).

The iterator `count2` and the loop body are the program's own code, run by the proof, one summary
theorem each (`body1`, `body2`: the two iterations of the body; `count2_run`: the iterator), so
that every theorem compiles on its own. `Acc` lives in `.noptrbss`, whose content the binary does
not fix, so the extractor does not copy it and the precondition provides the word (`accA`).
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64
open Janus.Contracts.MapAmd64 (keepABI_apply)
open Janus.Contracts.Panic (Item recItems frameItems fnItems frameKeep bitsWin recItems_above Frame
  frameRecs_above)
open Janus.Spec (openBits)

/-- The address of `example.com/basic.Acc` (`.noptrbss`; the extractor does not copy it). -/
local macro "accA" : term => `((5799072 : Nat))
local macro "bodyA" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RangeDefer-range1"))
local macro "count2A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.count2"))

local macro "fvA" : term => `(janus_eval% (Extracted.program.data.head!.base))
local macro "accAdd1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.accAdd1"))
local macro "accAdd2A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.accAdd2"))

theorem ReachesRet.of_steps' {p : Janus.Amd64.Program} {tgt : W64} {S : State} {Q : State → Prop} {R : State → Prop}
    (h : ∃ k d, Janus.Amd64.Program.Steps p S k d ∧ R d) (hcont : ∀ d, R d → ReachesRet p tgt d Q) :
    ReachesRet p tgt S Q := by
  obtain ⟨k, d, hst, hr⟩ := h
  obtain ⟨k', e, hst', he, hq⟩ := hcont d hr
  exact ⟨k + k', e, hst.trans hst', he, hq⟩

def digit (k v : Nat) : Nat := (v * 10 + k) % 2 ^ 64

/-- The two deferred calls in LIFO order. -/
def mix (v : Nat) : Nat := digit 1 (digit 2 v)

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

/-- The state of an iteration's body call (it is entered with `RSP = R - 88`, `R` being the entry
`RSP` of `RangeDefer`): the closure of the loop body at `R - 40` (code, `&state`, the token `any`),
the state `1`, the deferred calls recorded so far. -/
def BodyPre (P : Spec.PanicRuntime) (s e : State) (ra k tt td : Nat) (fns0 : List Nat)
    (rest : List Spec.DeferRec) : Prop :=
  e.regs 0 = BitVec.ofNat 64 k ∧ e.regs 2 = BitVec.ofNat 64 ((s.regs 4).toNat - 40) ∧
    e.regs 14 = s.regs 14 ∧ e.xmm 15 = 0 ∧ e.df = false ∧
    e.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) ∧ e.mem.readLE ((s.regs 4).toNat - 88) 8 = ra ∧
    MemFrame s.mem e.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) ∧
    P.Env e.mem ∧ e.mem.readLE ((s.regs 4).toNat - 32) 8 = (s.regs 4).toNat - 48 ∧
    e.mem.readLE ((s.regs 4).toNat - 24) 8 = tt ∧ e.mem.readLE ((s.regs 4).toNat - 16) 8 = td ∧
    e.mem.readLE ((s.regs 4).toNat - 48) 8 = 1 ∧
    P.defers e.mem (gOf s) = { sp := (s.regs 4).toNat - 56, fns := fns0, token := some td } :: rest ∧
    P.saved e.mem (gOf s) = none ∧ (∀ d ∈ rest, (s.regs 4).toNat ≤ d.sp) ∧ 1 ≤ P.room e.mem (gOf s)

/-- What the body call leaves: it records its deferred call (`fv`) on the token, restores the state
`1` and returns `true`. -/
def BodyPost (P : Spec.PanicRuntime) (s e e' : State) (fv td : Nat) (fns0 : List Nat)
    (rest : List Spec.DeferRec) : Prop :=
  e'.rip = retAddrOf e ∧ e'.regs 4 = e.regs 4 + 8 ∧ e'.regs 14 = e.regs 14 ∧ e'.regs 5 = e.regs 5 ∧
    e'.xmm 15 = 0 ∧ e'.df = false ∧ e'.regs 0 = 1#64 ∧
    MemFrame e.mem e'.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)]) ∧
    P.Env e'.mem ∧
    P.defers e'.mem (gOf s) = { sp := (s.regs 4).toNat - 56, fns := fv :: fns0, token := some td } :: rest ∧
    P.saved e'.mem (gOf s) = none ∧ P.panics e'.mem (gOf s) = P.panics e.mem (gOf s) ∧
    P.room e.mem (gOf s) ≤ P.room e'.mem (gOf s) + 1 ∧ e'.mem.readLE ((s.regs 4).toNat - 48) 8 = 1

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
/-- The loop body, first iteration (`x = 1`, defers `accAdd1`). -/
theorem body1 (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hat : DeferprocatContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferprocat") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U)
    (s : State) (hc : PanicCallerOK P s 144 8) (ra : Nat) (hra : ra < 2 ^ 47) (tt td : Nat) (htt : tt < 2 ^ 64) (htd : td < 2 ^ 64) (fns0 : List Nat) (rest : List Spec.DeferRec) :
    Summary (Extracted.program.link impl) bodyA (fun e => BodyPre P s e ra 1 tt td fns0 rest)
      (fun e e' => BodyPost P s e e' fvA td fns0 rest) := by
  intro e hpc hpre
  obtain ⟨hr0, hr2, hr14, hx15, hdf, hr4, hret, hW, henv, hc32, hc24, hc16, hst1, hdef, hsv, hrest, hroom⟩ := hpre
  have hc' := hc
  obtain ⟨henv0, hg, hal0, hd0, hb0, hst0, hout, hgd, hgo⟩ := hc'
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst0 hout hd0 hb0 hal0
  have hgv : e.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hW.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hgo, by omega⟩)
  have hga : e.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hW.accessible]; exact hgr
  have hwin : e.mem.accessible ((s.regs 4).toNat - (P.depth + 144)) (P.depth + 144 + 8) true = true := by
    rw [hW.accessible]; exact hst0
  have h88 : ((s.regs 4).toNat - 88) < 2 ^ 64 := by have := (s.regs 4).isLt; omega
  have hc32' : e.mem.readLE ((s.regs 4).toNat - 40 + 8) 8 = (s.regs 4).toNat - 48 := by
    rw [show (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 by omega]; exact hc32
  have hc24' : e.mem.readLE ((s.regs 4).toNat - 40 + 16) 8 = tt := by
    rw [show (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 by omega]; exact hc24
  have hc16' : e.mem.readLE ((s.regs 4).toNat - 40 + 24) 8 = td := by
    rw [show (s.regs 4).toNat - 40 + 24 = (s.regs 4).toNat - 16 by omega]; exact hc16
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpc hdf
  have hcr : cr = setRegF (setRegF (setRegF (setRegF cr 0 (BitVec.ofNat 64 1))
      2 (BitVec.ofNat 64 ((s.regs 4).toNat - 40))) 4 (BitVec.ofNat 64 ((s.regs 4).toNat - 88))) 14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact hr14
    · rw [if_neg h14]
      by_cases h4 : i = 4
      · rw [if_pos h4, h4]; exact hr4
      · rw [if_neg h4]
        by_cases h2 : i = 2
        · rw [if_pos h2, h2]; exact hr2
        · rw [if_neg h2]
          by_cases h0 : i = 0
          · rw [if_pos h0, h0]; exact hr0
          · rw [if_neg h0]
  rw [hcr]
  janus64_run [hc32', hc24', hc16', hst1] until [Extracted.program.contractAddr "runtime.deferprocat"]
  refine ReachesRet.name fun S hS => ?_
  have h144 : (BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 56#64).toNat = (s.regs 4).toNat - 144 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
  have hSsp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 56#64 := by rw [hS] <;> simp [setRegF]
  have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [hSsp]; exact h144
  have hS5 : S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 8#64 := by rw [hS] <;> simp [setRegF]
  have hS0 : S.regs 0 = 4969480#64 := by rw [hS] <;> simp [setRegF]
  have hS1 : S.regs 1 = BitVec.ofNat 64 td := by rw [hS] <;> simp [setRegF]
  have hS14 : S.regs 14 = s.regs 14 := by rw [hS] <;> simp [setRegF]
  have hSx : S.xmm 15 = 0 := by rw [hS]; exact hx15
  have hSdf : S.df = false := by rw [hS]
  have hSpc : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferprocat") := by
    rw [hS] <;> rfl
  have hSf : MemFrame cm S.mem [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)] := by
    rw [hS]; janus_frame
  have hSmem : S.mem = (((((Janus.Arm64.Memory.writeLE cm ((s.regs 4).toNat - 96) 8 (cr 5).toNat).writeLE
      ((s.regs 4).toNat - 105) 1 0).writeLE ((s.regs 4).toNat - 48) 8 2).writeLE
      ((s.regs 4).toNat - 104) 8 ((s.regs 4).toNat - 48)).writeLE ((s.regs 4).toNat - 144) 8 4748330) := by
    rw [hS]
    simp only [show (s.regs 4).toNat - 88 - 8 = (s.regs 4).toNat - 96 by omega,
      show (s.regs 4).toNat - 88 - 17 = (s.regs 4).toNat - 105 by omega,
      show (s.regs 4).toNat - 88 - 16 = (s.regs 4).toNat - 104 by omega,
      show (s.regs 4).toNat - 88 - 56 = (s.regs 4).toNat - 144 by omega]
  have hSra : S.mem.readLE (S.regs 4).toNat 8 = 4748330 := by
    rw [hSmem, hSspn, Janus.Arm64.Memory.readLE_writeLE_self]
  have hgS : gOf S = gOf s := by simp only [gOf, hS14]
  have hSf1 : MemFrame cm S.mem [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)] :=
    hSf.mono fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hagS : Spec.Map.Agrees cm S.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 144)) (hi := (s.regs 4).toNat + 8) hSf1
      (Outside.of_sub hout (by omega) (by omega))
  have hSfW : MemFrame s.mem S.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hW.trans hSf1 fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hdefS : P.defers S.mem (gOf S) = { sp := (s.regs 4).toNat - 56, fns := fns0, token := some td } :: rest := by
    rw [hgS, hl.defers_frame _ _ _ hagS]; exact hdef
  have hslot : S.mem.readLE ((s.regs 4).toNat - 104) 8 = (s.regs 4).toNat - 48 := by
    rw [hSmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 4).isLt; omega)
  have hflag : S.mem.readLE ((s.regs 4).toNat - 105) 1 = 0 := by
    rw [hSmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  have hrbp : S.mem.readLE ((s.regs 4).toNat - 96) 8 = (cr 5).toNat := by
    rw [hSmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (cr 5).isLt
  have hret' : S.mem.readLE ((s.regs 4).toNat - 88) 8 = ra := by
    rw [hSmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hret
  have hstS : S.mem.readLE ((s.regs 4).toNat - 48) 8 = 2 := by
    rw [hSmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  refine ReachesRet.call hat hSpc ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
      (by rw [hSspn]; omega) hS14 hSx hSdf (by rw [hSra]; decide),
    by rw [hgS, hl.room_frame _ _ _ hagS]; omega, ?_⟩ ?_
  · rw [hdefS]; exact ⟨_, _, rfl, by rw [hS1]; simp [Nat.mod_eq_of_lt htd]⟩
  intro s1 hpc1 hq1
  obtain ⟨⟨r1, x1, y1, f1, m1, hs1, hfr1, henv1⟩, hdef1, hkeep1⟩ := hq1
  have hm1 : s1.mem = m1 := by rw [hs1]
  have hd1 : P.defers m1 (gOf s) = { sp := (s.regs 4).toNat - 56, fns := fvA :: fns0, token := some td } :: rest := by
    have hh := hdef1 _ _ hdefS
    rw [hm1, hgS, hS0] at hh
    exact hh
  simp only [MapAmd64.calleeStack, hSspn] at hfr1
  have hkeep : ∀ a n, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - 144 - P.depth ∨ (s.regs 4).toNat - 144 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 144 + 8 ∨ (s.regs 4).toNat - 144 + 8 + 8 * 2 ≤ a) → m1.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    exact hfr1.readLE a n (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3⟩)
  have hslot1 : m1.readLE ((s.regs 4).toNat - 104) 8 = (s.regs 4).toNat - 48 := by
    rw [hkeep _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hslot
  have hflag1 : m1.readLE ((s.regs 4).toNat - 105) 1 = 0 := by
    rw [hkeep _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hflag
  have hrbp1 : m1.readLE ((s.regs 4).toNat - 96) 8 = (cr 5).toNat := by
    rw [hkeep _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hrbp
  have hret1 : m1.readLE ((s.regs 4).toNat - 88) 8 = ra := by
    rw [hkeep _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hret'
  have hst1' : m1.readLE ((s.regs 4).toNat - 48) 8 = 2 := by
    rw [hkeep _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hstS
  have hW1 : MemFrame s.mem m1 (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hSfW.trans hfr1 fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega⟩⟩
  have hpn1 : P.panics m1 (gOf s) = P.panics cm (gOf s) := by
    have := hkeep1.1; rw [hm1, hgS, hl.panics_frame _ _ _ hagS] at this; exact this
  have hsv1 : P.saved m1 (gOf s) = none := by
    have := hkeep1.2.1; rw [hm1, hgS, hl.saved_frame _ _ _ hagS] at this; rw [this]; exact hsv
  have hrm1 : P.room cm (gOf s) ≤ P.room m1 (gOf s) + 1 := by
    have := hkeep1.2.2.2; rw [hm1, hgS, hl.room_frame _ _ _ hagS] at this; exact this
  clear hdef1 hkeep1 hm1 hpc1
  subst hs1
  janus64_run [hslot1, hflag1] until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine ReachesRet.name fun S3 hS3 => ?_
  have hS3mem : S3.mem = (((Janus.Arm64.Memory.writeLE m1 ((s.regs 4).toNat - 48) 8 1).writeLE
      ((s.regs 4).toNat - 105) 1 1).writeLE ((s.regs 4).toNat - 144) 8 4748366) := by
    rw [hS3]
    simp only [show (s.regs 4).toNat - 88 - 17 = (s.regs 4).toNat - 105 by omega,
      show (s.regs 4).toNat - 88 - 56 = (s.regs 4).toNat - 144 by omega]
  have hS3sp : S3.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 56#64 := by rw [hS3] <;> simp [setRegF]
  have hS3spn : (S3.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [hS3sp]; exact h144
  have hS314 : S3.regs 14 = s.regs 14 := by rw [hS3] <;> simp [setRegF, MapAmd64.keepABI, hS14]
  have hS35 : S3.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 8#64 := by
    rw [hS3] <;> simp [setRegF, MapAmd64.keepABI, hS5]
  have hS3x : S3.xmm 15 = 0 := by rw [hS3]; simpa [MapAmd64.keepX15] using hSx
  have hS3df : S3.df = false := by rw [hS3]
  have hS3pc : S3.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by
    rw [hS3] <;> rfl
  have hS3f : MemFrame m1 S3.mem [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)] := by
    rw [hS3]; janus_frame
  have hgS3 : gOf S3 = gOf s := by simp only [gOf, hS314]
  have hS3f1 : MemFrame m1 S3.mem [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)] :=
    hS3f.mono fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hagS3 : Spec.Map.Agrees m1 S3.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 144)) (hi := (s.regs 4).toNat + 8) hS3f1
      (Outside.of_sub hout (by omega) (by omega))
  have hS3fW : MemFrame s.mem S3.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hW1.trans hS3f1 fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hS3ra : S3.mem.readLE (S3.regs 4).toNat 8 = 4748366 := by
    rw [hS3mem, hS3spn, Janus.Arm64.Memory.readLE_writeLE_self]
  have hpre3 : PanicPre P 0 S3 := PanicPre.of_within hc hS3fW (hl.env_frame _ _ henv1 hagS3) (by omega) (by omega)
    (by rw [hS3spn]; omega) hS314 hS3x hS3df (by rw [hS3ra]; decide)
  have hsv3 : P.saved S3.mem (gOf S3) = none := by rw [hgS3, hl.saved_frame _ _ _ hagS3]; exact hsv1
  have hdf3 : P.defers S3.mem (gOf S3) =
      { sp := (s.regs 4).toNat - 56, fns := fvA :: fns0, token := some td } :: rest := by
    rw [hgS3, hl.defers_frame _ _ _ hagS3]; exact hd1
  have hfsp3 : fspOf S3 = (s.regs 4).toNat - 136 := by simp only [fspOf, hS3spn]; omega
  have hF3 : retFrame P S3 = ⟨(s.regs 4).toNat - 136, (s.regs 4).toNat - 136, 0, none⟩ := by
    simp only [retFrame, hsv3, hfsp3]
  have hds3 : ∀ d ∈ P.defers S3.mem (gOf S3), (s.regs 4).toNat - 136 < d.sp := by
    intro d hd; rw [hdf3] at hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · dsimp only; omega
    · have := hrest d hd; omega
  have hI3 : frameItems S3.mem (retFrame P S3) (P.defers S3.mem (gOf S3)) = [] := by
    rw [hF3]; simp only [frameItems, List.nil_append, recItems_above hds3]
  have hE3 := hdr S3 hS3pc ⟨hpre3, by
    rw [hI3, hF3]; exact ⟨⟨trivial, fun it h => absurd h (by simp)⟩, fun it h => absurd h (by simp)⟩⟩
  rw [hI3, hF3] at hE3
  rw [Engine_nil] at hE3
  refine ReachesRet.of_steps' hE3 ?_
  rintro d ⟨hdpc, hdsp, hd14, hd5, hdx, hddf, hdfr, hdenv, hdpan, hddef, hdsv, hdrp, hdrm⟩
  obtain ⟨dr, dpc, dfl, dxm, dm, dyh, dfs, ddf, dmx⟩ := d
  dsimp only at hdpc hdsp hd14 hd5 hdx hddf hdfr hdenv hdpan hddef hdsv hdrp hdrm
  rw [hS3ra] at hdpc
  have hdpc' : dpc = BitVec.ofNat 64 4748366 := by
    apply BitVec.eq_of_toNat_eq; rw [hdpc, BitVec.toNat_ofNat]
  subst hdpc' hddf
  rw [hF3] at hdfr
  simp only [rtWin, bitsWin, List.append_nil] at hdfr
  have hd4v : dr 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 136) := by
    rw [hdsp, hS3sp]; apply BitVec.eq_of_toNat_eq
    have := (s.regs 4).isLt
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp; omega
  have hd5v : dr 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 8#64 := by rw [hd5, hS35]
  have hd14v : dr 14 = s.regs 14 := by rw [hd14, hS314]
  have hdr' : dr = setRegF (setRegF (setRegF dr 4 (BitVec.ofNat 64 ((s.regs 4).toNat - 136))) 5
      (BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 8#64)) 14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact hd14v
    · rw [if_neg h14]
      by_cases h5 : i = 5
      · rw [if_pos h5, h5]; exact hd5v
      · rw [if_neg h5]
        by_cases h4 : i = 4
        · rw [if_pos h4, h4]; exact hd4v
        · rw [if_neg h4]
  rw [hdr']
  have hdm8 : ∀ a n, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - 136 - P.depth ∨ (s.regs 4).toNat - 144 ≤ a) →
      dm.readLE a n = S3.mem.readLE a n := by
    intro a n h1 h2
    exact hdfr.readLE a n (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, h2⟩)
  have hdflag : dm.readLE ((s.regs 4).toNat - 105) 1 = 1 := by
    rw [hdm8 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega), hS3mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  have hdrbp : dm.readLE ((s.regs 4).toNat - 96) 8 = (cr 5).toNat := by
    rw [hdm8 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega), hS3mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hrbp1
  have hdret : dm.readLE ((s.regs 4).toNat - 88) 8 = ra := by
    rw [hdm8 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega), hS3mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hret1
  have hdst : dm.readLE ((s.regs 4).toNat - 48) 8 = 1 := by
    rw [hdm8 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega), hS3mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  have hdacc : dm.accessible ((s.regs 4).toNat - 136) 136 true = true := by
    rw [hdfr.accessible, hS3fW.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hst0 (by omega) (by omega)
  have hret48 : cm.readLE ((s.regs 4).toNat - 136 + 48) 8 = ra := by
    rw [show (s.regs 4).toNat - 136 + 48 = (s.regs 4).toNat - 88 by omega]; exact hret
  have hdret48 : dm.readLE ((s.regs 4).toNat - 136 + 48) 8 = ra := by
    rw [show (s.regs 4).toNat - 136 + 48 = (s.regs 4).toNat - 88 by omega]; exact hdret
  have hdrbp40 : dm.readLE ((s.regs 4).toNat - 136 + 40) 8 = (cr 5).toNat := by
    rw [show (s.regs 4).toNat - 136 + 40 = (s.regs 4).toNat - 96 by omega]; exact hdrbp
  have hdflag31 : dm.readLE ((s.regs 4).toNat - 136 + 31) 1 = 1 := by
    rw [show (s.regs 4).toNat - 136 + 31 = (s.regs 4).toNat - 105 by omega]; exact hdflag
  janus64_run [hdflag31, hdrbp40, hdret48, hret48]
  have hA : MemFrame cm S.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  have hB : MemFrame cm m1 (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)]) :=
    hA.trans hfr1 fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hC : MemFrame cm S3.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)]) :=
    hB.trans hS3f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hD : MemFrame cm dm (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)]) :=
    hC.trans hdfr fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨h1, by omega⟩⟩
  have hdefd : P.defers dm (gOf s) =
      { sp := (s.regs 4).toNat - 56, fns := fvA :: fns0, token := some td } :: rest := by
    have h1 := hddef
    rw [hfsp3, (frameRecs_above hds3).2, hdf3, hgS3] at h1
    exact h1
  have hh14 : (BitVec.ofNat 64 ((s.regs 4).toNat - 136) + 56#64).toNat = (s.regs 4).toNat - 80 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hD, hdenv, hdefd, ?_, ?_, ?_, hdst⟩
  · simp only [retAddrOf, setRegF_apply]; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h88, hret]
  · simp only [setRegF_apply]; simp
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  · simp [setRegF]
  · simp [setRegF]
  · exact hdx
  · rfl
  · simp [setRegF]
  · rw [← hgS3]; exact hdsv
  · rw [← hgS3, hdpan, hgS3, hl.panics_frame _ _ _ hagS3]; exact hpn1
  · show P.room cm (gOf s) ≤ P.room dm (gOf s) + 1
    have h1 := hdrm
    rw [hgS3, hl.room_frame _ _ _ hagS3] at h1
    omega


set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
/-- The loop body, second iteration (`x = 2`, defers `accAdd2`). -/
theorem body2 (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hat : DeferprocatContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferprocat") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U)
    (s : State) (hc : PanicCallerOK P s 144 8) (ra : Nat) (hra : ra < 2 ^ 47) (tt td : Nat) (htt : tt < 2 ^ 64) (htd : td < 2 ^ 64) (fns0 : List Nat) (rest : List Spec.DeferRec) :
    Summary (Extracted.program.link impl) bodyA (fun e => BodyPre P s e ra 2 tt td fns0 rest)
      (fun e e' => BodyPost P s e e' (fvA + 8) td fns0 rest) := by
  intro e hpc hpre
  obtain ⟨hr0, hr2, hr14, hx15, hdf, hr4, hret, hW, henv, hc32, hc24, hc16, hst1, hdef, hsv, hrest, hroom⟩ := hpre
  have hc' := hc
  obtain ⟨henv0, hg, hal0, hd0, hb0, hst0, hout, hgd, hgo⟩ := hc'
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst0 hout hd0 hb0 hal0
  have hgv : e.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hW.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hgo, by omega⟩)
  have hga : e.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hW.accessible]; exact hgr
  have hwin : e.mem.accessible ((s.regs 4).toNat - (P.depth + 144)) (P.depth + 144 + 8) true = true := by
    rw [hW.accessible]; exact hst0
  have h88 : ((s.regs 4).toNat - 88) < 2 ^ 64 := by have := (s.regs 4).isLt; omega
  have hc32' : e.mem.readLE ((s.regs 4).toNat - 40 + 8) 8 = (s.regs 4).toNat - 48 := by
    rw [show (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 by omega]; exact hc32
  have hc24' : e.mem.readLE ((s.regs 4).toNat - 40 + 16) 8 = tt := by
    rw [show (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 by omega]; exact hc24
  have hc16' : e.mem.readLE ((s.regs 4).toNat - 40 + 24) 8 = td := by
    rw [show (s.regs 4).toNat - 40 + 24 = (s.regs 4).toNat - 16 by omega]; exact hc16
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpc hdf
  have hcr : cr = setRegF (setRegF (setRegF (setRegF cr 0 (BitVec.ofNat 64 2))
      2 (BitVec.ofNat 64 ((s.regs 4).toNat - 40))) 4 (BitVec.ofNat 64 ((s.regs 4).toNat - 88))) 14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact hr14
    · rw [if_neg h14]
      by_cases h4 : i = 4
      · rw [if_pos h4, h4]; exact hr4
      · rw [if_neg h4]
        by_cases h2 : i = 2
        · rw [if_pos h2, h2]; exact hr2
        · rw [if_neg h2]
          by_cases h0 : i = 0
          · rw [if_pos h0, h0]; exact hr0
          · rw [if_neg h0]
  rw [hcr]
  janus64_run [hc32', hc24', hc16', hst1] until [Extracted.program.contractAddr "runtime.deferprocat"]
  refine ReachesRet.name fun S hS => ?_
  have h144 : (BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 56#64).toNat = (s.regs 4).toNat - 144 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
  have hSsp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 56#64 := by rw [hS] <;> simp [setRegF]
  have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [hSsp]; exact h144
  have hS5 : S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 8#64 := by rw [hS] <;> simp [setRegF]
  have hS0 : S.regs 0 = 4969488#64 := by rw [hS] <;> simp [setRegF]
  have hS1 : S.regs 1 = BitVec.ofNat 64 td := by rw [hS] <;> simp [setRegF]
  have hS14 : S.regs 14 = s.regs 14 := by rw [hS] <;> simp [setRegF]
  have hSx : S.xmm 15 = 0 := by rw [hS]; exact hx15
  have hSdf : S.df = false := by rw [hS]
  have hSpc : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferprocat") := by
    rw [hS] <;> rfl
  have hSf : MemFrame cm S.mem [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)] := by
    rw [hS]; janus_frame
  have hSmem : S.mem = (((((Janus.Arm64.Memory.writeLE cm ((s.regs 4).toNat - 96) 8 (cr 5).toNat).writeLE
      ((s.regs 4).toNat - 105) 1 0).writeLE ((s.regs 4).toNat - 48) 8 2).writeLE
      ((s.regs 4).toNat - 104) 8 ((s.regs 4).toNat - 48)).writeLE ((s.regs 4).toNat - 144) 8 4748344) := by
    rw [hS]
    simp only [show (s.regs 4).toNat - 88 - 8 = (s.regs 4).toNat - 96 by omega,
      show (s.regs 4).toNat - 88 - 17 = (s.regs 4).toNat - 105 by omega,
      show (s.regs 4).toNat - 88 - 16 = (s.regs 4).toNat - 104 by omega,
      show (s.regs 4).toNat - 88 - 56 = (s.regs 4).toNat - 144 by omega]
  have hSra : S.mem.readLE (S.regs 4).toNat 8 = 4748344 := by
    rw [hSmem, hSspn, Janus.Arm64.Memory.readLE_writeLE_self]
  have hgS : gOf S = gOf s := by simp only [gOf, hS14]
  have hSf1 : MemFrame cm S.mem [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)] :=
    hSf.mono fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hagS : Spec.Map.Agrees cm S.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 144)) (hi := (s.regs 4).toNat + 8) hSf1
      (Outside.of_sub hout (by omega) (by omega))
  have hSfW : MemFrame s.mem S.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hW.trans hSf1 fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hdefS : P.defers S.mem (gOf S) = { sp := (s.regs 4).toNat - 56, fns := fns0, token := some td } :: rest := by
    rw [hgS, hl.defers_frame _ _ _ hagS]; exact hdef
  have hslot : S.mem.readLE ((s.regs 4).toNat - 104) 8 = (s.regs 4).toNat - 48 := by
    rw [hSmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 4).isLt; omega)
  have hflag : S.mem.readLE ((s.regs 4).toNat - 105) 1 = 0 := by
    rw [hSmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  have hrbp : S.mem.readLE ((s.regs 4).toNat - 96) 8 = (cr 5).toNat := by
    rw [hSmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (cr 5).isLt
  have hret' : S.mem.readLE ((s.regs 4).toNat - 88) 8 = ra := by
    rw [hSmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hret
  have hstS : S.mem.readLE ((s.regs 4).toNat - 48) 8 = 2 := by
    rw [hSmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  refine ReachesRet.call hat hSpc ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
      (by rw [hSspn]; omega) hS14 hSx hSdf (by rw [hSra]; decide),
    by rw [hgS, hl.room_frame _ _ _ hagS]; omega, ?_⟩ ?_
  · rw [hdefS]; exact ⟨_, _, rfl, by rw [hS1]; simp [Nat.mod_eq_of_lt htd]⟩
  intro s1 hpc1 hq1
  obtain ⟨⟨r1, x1, y1, f1, m1, hs1, hfr1, henv1⟩, hdef1, hkeep1⟩ := hq1
  have hm1 : s1.mem = m1 := by rw [hs1]
  have hd1 : P.defers m1 (gOf s) = { sp := (s.regs 4).toNat - 56, fns := (fvA + 8) :: fns0, token := some td } :: rest := by
    have hh := hdef1 _ _ hdefS
    rw [hm1, hgS, hS0] at hh
    exact hh
  simp only [MapAmd64.calleeStack, hSspn] at hfr1
  have hkeep : ∀ a n, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - 144 - P.depth ∨ (s.regs 4).toNat - 144 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 144 + 8 ∨ (s.regs 4).toNat - 144 + 8 + 8 * 2 ≤ a) → m1.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    exact hfr1.readLE a n (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3⟩)
  have hslot1 : m1.readLE ((s.regs 4).toNat - 104) 8 = (s.regs 4).toNat - 48 := by
    rw [hkeep _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hslot
  have hflag1 : m1.readLE ((s.regs 4).toNat - 105) 1 = 0 := by
    rw [hkeep _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hflag
  have hrbp1 : m1.readLE ((s.regs 4).toNat - 96) 8 = (cr 5).toNat := by
    rw [hkeep _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hrbp
  have hret1 : m1.readLE ((s.regs 4).toNat - 88) 8 = ra := by
    rw [hkeep _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hret'
  have hst1' : m1.readLE ((s.regs 4).toNat - 48) 8 = 2 := by
    rw [hkeep _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact hstS
  have hW1 : MemFrame s.mem m1 (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hSfW.trans hfr1 fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega⟩⟩
  have hpn1 : P.panics m1 (gOf s) = P.panics cm (gOf s) := by
    have := hkeep1.1; rw [hm1, hgS, hl.panics_frame _ _ _ hagS] at this; exact this
  have hsv1 : P.saved m1 (gOf s) = none := by
    have := hkeep1.2.1; rw [hm1, hgS, hl.saved_frame _ _ _ hagS] at this; rw [this]; exact hsv
  have hrm1 : P.room cm (gOf s) ≤ P.room m1 (gOf s) + 1 := by
    have := hkeep1.2.2.2; rw [hm1, hgS, hl.room_frame _ _ _ hagS] at this; exact this
  clear hdef1 hkeep1 hm1 hpc1
  subst hs1
  janus64_run [hslot1, hflag1] until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine ReachesRet.name fun S3 hS3 => ?_
  have hS3mem : S3.mem = (((Janus.Arm64.Memory.writeLE m1 ((s.regs 4).toNat - 48) 8 1).writeLE
      ((s.regs 4).toNat - 105) 1 1).writeLE ((s.regs 4).toNat - 144) 8 4748366) := by
    rw [hS3]
    simp only [show (s.regs 4).toNat - 88 - 17 = (s.regs 4).toNat - 105 by omega,
      show (s.regs 4).toNat - 88 - 56 = (s.regs 4).toNat - 144 by omega]
  have hS3sp : S3.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 56#64 := by rw [hS3] <;> simp [setRegF]
  have hS3spn : (S3.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [hS3sp]; exact h144
  have hS314 : S3.regs 14 = s.regs 14 := by rw [hS3] <;> simp [setRegF, MapAmd64.keepABI, hS14]
  have hS35 : S3.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 8#64 := by
    rw [hS3] <;> simp [setRegF, MapAmd64.keepABI, hS5]
  have hS3x : S3.xmm 15 = 0 := by rw [hS3]; simpa [MapAmd64.keepX15] using hSx
  have hS3df : S3.df = false := by rw [hS3]
  have hS3pc : S3.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by
    rw [hS3] <;> rfl
  have hS3f : MemFrame m1 S3.mem [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)] := by
    rw [hS3]; janus_frame
  have hgS3 : gOf S3 = gOf s := by simp only [gOf, hS314]
  have hS3f1 : MemFrame m1 S3.mem [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)] :=
    hS3f.mono fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hagS3 : Spec.Map.Agrees m1 S3.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 144)) (hi := (s.regs 4).toNat + 8) hS3f1
      (Outside.of_sub hout (by omega) (by omega))
  have hS3fW : MemFrame s.mem S3.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hW1.trans hS3f1 fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hS3ra : S3.mem.readLE (S3.regs 4).toNat 8 = 4748366 := by
    rw [hS3mem, hS3spn, Janus.Arm64.Memory.readLE_writeLE_self]
  have hpre3 : PanicPre P 0 S3 := PanicPre.of_within hc hS3fW (hl.env_frame _ _ henv1 hagS3) (by omega) (by omega)
    (by rw [hS3spn]; omega) hS314 hS3x hS3df (by rw [hS3ra]; decide)
  have hsv3 : P.saved S3.mem (gOf S3) = none := by rw [hgS3, hl.saved_frame _ _ _ hagS3]; exact hsv1
  have hdf3 : P.defers S3.mem (gOf S3) =
      { sp := (s.regs 4).toNat - 56, fns := (fvA + 8) :: fns0, token := some td } :: rest := by
    rw [hgS3, hl.defers_frame _ _ _ hagS3]; exact hd1
  have hfsp3 : fspOf S3 = (s.regs 4).toNat - 136 := by simp only [fspOf, hS3spn]; omega
  have hF3 : retFrame P S3 = ⟨(s.regs 4).toNat - 136, (s.regs 4).toNat - 136, 0, none⟩ := by
    simp only [retFrame, hsv3, hfsp3]
  have hds3 : ∀ d ∈ P.defers S3.mem (gOf S3), (s.regs 4).toNat - 136 < d.sp := by
    intro d hd; rw [hdf3] at hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · dsimp only; omega
    · have := hrest d hd; omega
  have hI3 : frameItems S3.mem (retFrame P S3) (P.defers S3.mem (gOf S3)) = [] := by
    rw [hF3]; simp only [frameItems, List.nil_append, recItems_above hds3]
  have hE3 := hdr S3 hS3pc ⟨hpre3, by
    rw [hI3, hF3]; exact ⟨⟨trivial, fun it h => absurd h (by simp)⟩, fun it h => absurd h (by simp)⟩⟩
  rw [hI3, hF3] at hE3
  rw [Engine_nil] at hE3
  refine ReachesRet.of_steps' hE3 ?_
  rintro d ⟨hdpc, hdsp, hd14, hd5, hdx, hddf, hdfr, hdenv, hdpan, hddef, hdsv, hdrp, hdrm⟩
  obtain ⟨dr, dpc, dfl, dxm, dm, dyh, dfs, ddf, dmx⟩ := d
  dsimp only at hdpc hdsp hd14 hd5 hdx hddf hdfr hdenv hdpan hddef hdsv hdrp hdrm
  rw [hS3ra] at hdpc
  have hdpc' : dpc = BitVec.ofNat 64 4748366 := by
    apply BitVec.eq_of_toNat_eq; rw [hdpc, BitVec.toNat_ofNat]
  subst hdpc' hddf
  rw [hF3] at hdfr
  simp only [rtWin, bitsWin, List.append_nil] at hdfr
  have hd4v : dr 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 136) := by
    rw [hdsp, hS3sp]; apply BitVec.eq_of_toNat_eq
    have := (s.regs 4).isLt
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp; omega
  have hd5v : dr 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 8#64 := by rw [hd5, hS35]
  have hd14v : dr 14 = s.regs 14 := by rw [hd14, hS314]
  have hdr' : dr = setRegF (setRegF (setRegF dr 4 (BitVec.ofNat 64 ((s.regs 4).toNat - 136))) 5
      (BitVec.ofNat 64 ((s.regs 4).toNat - 88) - 8#64)) 14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact hd14v
    · rw [if_neg h14]
      by_cases h5 : i = 5
      · rw [if_pos h5, h5]; exact hd5v
      · rw [if_neg h5]
        by_cases h4 : i = 4
        · rw [if_pos h4, h4]; exact hd4v
        · rw [if_neg h4]
  rw [hdr']
  have hdm8 : ∀ a n, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - 136 - P.depth ∨ (s.regs 4).toNat - 144 ≤ a) →
      dm.readLE a n = S3.mem.readLE a n := by
    intro a n h1 h2
    exact hdfr.readLE a n (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, h2⟩)
  have hdflag : dm.readLE ((s.regs 4).toNat - 105) 1 = 1 := by
    rw [hdm8 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega), hS3mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  have hdrbp : dm.readLE ((s.regs 4).toNat - 96) 8 = (cr 5).toNat := by
    rw [hdm8 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega), hS3mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hrbp1
  have hdret : dm.readLE ((s.regs 4).toNat - 88) 8 = ra := by
    rw [hdm8 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega), hS3mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hret1
  have hdst : dm.readLE ((s.regs 4).toNat - 48) 8 = 1 := by
    rw [hdm8 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega), hS3mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  have hdacc : dm.accessible ((s.regs 4).toNat - 136) 136 true = true := by
    rw [hdfr.accessible, hS3fW.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hst0 (by omega) (by omega)
  have hret48 : cm.readLE ((s.regs 4).toNat - 136 + 48) 8 = ra := by
    rw [show (s.regs 4).toNat - 136 + 48 = (s.regs 4).toNat - 88 by omega]; exact hret
  have hdret48 : dm.readLE ((s.regs 4).toNat - 136 + 48) 8 = ra := by
    rw [show (s.regs 4).toNat - 136 + 48 = (s.regs 4).toNat - 88 by omega]; exact hdret
  have hdrbp40 : dm.readLE ((s.regs 4).toNat - 136 + 40) 8 = (cr 5).toNat := by
    rw [show (s.regs 4).toNat - 136 + 40 = (s.regs 4).toNat - 96 by omega]; exact hdrbp
  have hdflag31 : dm.readLE ((s.regs 4).toNat - 136 + 31) 1 = 1 := by
    rw [show (s.regs 4).toNat - 136 + 31 = (s.regs 4).toNat - 105 by omega]; exact hdflag
  janus64_run [hdflag31, hdrbp40, hdret48, hret48]
  have hA : MemFrame cm S.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  have hB : MemFrame cm m1 (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)]) :=
    hA.trans hfr1 fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hC : MemFrame cm S3.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)]) :=
    hB.trans hS3f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hD : MemFrame cm dm (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)]) :=
    hC.trans hdfr fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨h1, by omega⟩⟩
  have hdefd : P.defers dm (gOf s) =
      { sp := (s.regs 4).toNat - 56, fns := (fvA + 8) :: fns0, token := some td } :: rest := by
    have h1 := hddef
    rw [hfsp3, (frameRecs_above hds3).2, hdf3, hgS3] at h1
    exact h1
  have hh14 : (BitVec.ofNat 64 ((s.regs 4).toNat - 136) + 56#64).toNat = (s.regs 4).toNat - 80 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hD, hdenv, hdefd, ?_, ?_, ?_, hdst⟩
  · simp only [retAddrOf, setRegF_apply]; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h88, hret]
  · simp only [setRegF_apply]; simp
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  · simp [setRegF]
  · simp [setRegF]
  · exact hdx
  · rfl
  · simp [setRegF]
  · rw [← hgS3]; exact hdsv
  · rw [← hgS3, hdpan, hgS3, hl.panics_frame _ _ _ hagS3]; exact hpn1
  · show P.room cm (gOf s) ≤ P.room dm (gOf s) + 1
    have h1 := hdrm
    rw [hgS3, hl.room_frame _ _ _ hagS3] at h1
    omega


/-- `count2`'s call (entered with `RSP = R - 64`): the iterator calls the body closure at `R - 40`
twice; the state `1`, the token's `any` and the record the token heads. -/
def CPre (P : Spec.PanicRuntime) (s e : State) (tt td : Nat) (rest : List Spec.DeferRec) : Prop :=
  e.regs 0 = BitVec.ofNat 64 ((s.regs 4).toNat - 40) ∧ e.regs 14 = s.regs 14 ∧ e.xmm 15 = 0 ∧ e.df = false ∧
    e.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 64) ∧ e.mem.readLE ((s.regs 4).toNat - 64) 8 = 4748198 ∧
    MemFrame s.mem e.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) ∧
    P.Env e.mem ∧ e.mem.readLE ((s.regs 4).toNat - 40) 8 = bodyA ∧
    e.mem.readLE ((s.regs 4).toNat - 32) 8 = (s.regs 4).toNat - 48 ∧
    e.mem.readLE ((s.regs 4).toNat - 24) 8 = tt ∧ e.mem.readLE ((s.regs 4).toNat - 16) 8 = td ∧
    e.mem.readLE ((s.regs 4).toNat - 48) 8 = 1 ∧
    P.defers e.mem (gOf s) = { sp := (s.regs 4).toNat - 56, fns := [], token := some td } :: rest ∧
    P.saved e.mem (gOf s) = none ∧ (∀ d ∈ rest, (s.regs 4).toNat ≤ d.sp) ∧ 2 ≤ P.room e.mem (gOf s)

/-- What `count2` leaves: both iterations ran their body. -/
def CPost (P : Spec.PanicRuntime) (s e e' : State) (td : Nat) (rest : List Spec.DeferRec) : Prop :=
  e'.rip = retAddrOf e ∧ e'.regs 4 = e.regs 4 + 8 ∧ e'.regs 14 = e.regs 14 ∧ e'.regs 5 = e.regs 5 ∧
    e'.xmm 15 = 0 ∧ e'.df = false ∧
    MemFrame e.mem e'.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 64),
      ((s.regs 4).toNat - 56, (s.regs 4).toNat - 40)]) ∧
    P.Env e'.mem ∧
    P.defers e'.mem (gOf s) =
      { sp := (s.regs 4).toNat - 56, fns := [fvA + 8, fvA], token := some td } :: rest ∧
    P.saved e'.mem (gOf s) = none ∧ P.panics e'.mem (gOf s) = P.panics e.mem (gOf s) ∧
    P.room e.mem (gOf s) ≤ P.room e'.mem (gOf s) + 2 ∧ e'.mem.readLE ((s.regs 4).toNat - 48) 8 = 1

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
/-- The iterator `count2`: it calls the loop body for `x = 1` and `x = 2`. -/
theorem count2_run (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hat : DeferprocatContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferprocat") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U)
    (s : State) (hc : PanicCallerOK P s 144 8) (tt td : Nat) (htt : tt < 2 ^ 64) (htd : td < 2 ^ 64)
    (rest : List Spec.DeferRec) :
    Summary (Extracted.program.link impl) count2A (fun e => CPre P s e tt td rest)
      (fun e e' => CPost P s e e' td rest) := by
  intro e hpc hpre
  obtain ⟨hr0, hr14, hx15, hdf, hr4, hret, hW, henv, hcb, hc32, hc24, hc16, hst1, hdef, hsv, hrest, hroom⟩ := hpre
  have hc' := hc
  obtain ⟨henv0, hg, hal0, hd0, hb0, hst0, hout, hgd, hgo⟩ := hc'
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst0 hout hd0 hb0 hal0
  have hgv : e.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hW.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hgo, by omega⟩)
  have hga : e.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hW.accessible]; exact hgr
  have hwin : e.mem.accessible ((s.regs 4).toNat - (P.depth + 144)) (P.depth + 144 + 8) true = true := by
    rw [hW.accessible]; exact hst0
  have h64 : ((s.regs 4).toNat - 64) < 2 ^ 64 := by have := (s.regs 4).isLt; omega
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpc hdf
  have hcr : cr = setRegF (setRegF (setRegF cr 0 (BitVec.ofNat 64 ((s.regs 4).toNat - 40)))
      4 (BitVec.ofNat 64 ((s.regs 4).toNat - 64))) 14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact hr14
    · rw [if_neg h14]
      by_cases h4 : i = 4
      · rw [if_pos h4, h4]; exact hr4
      · rw [if_neg h4]
        by_cases h0 : i = 0
        · rw [if_pos h0, h0]; exact hr0
        · rw [if_neg h0]
  rw [hcr]
  janus64_run [hcb] until [bodyA]
  refine ReachesRet.name fun S1 hS1 => ?_
  have h88 : (BitVec.ofNat 64 ((s.regs 4).toNat - 64) - 24#64).toNat = (s.regs 4).toNat - 88 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
  have hS1mem : S1.mem = (((Janus.Arm64.Memory.writeLE cm ((s.regs 4).toNat - 72) 8 (cr 5).toNat).writeLE
      ((s.regs 4).toNat - 56) 8 ((s.regs 4).toNat - 40)).writeLE ((s.regs 4).toNat - 88) 8 4748066) := by
    rw [hS1]
    simp only [show (s.regs 4).toNat - 64 - 8 = (s.regs 4).toNat - 72 by omega,
      show (s.regs 4).toNat - 64 + 8 = (s.regs 4).toNat - 56 by omega,
      show (s.regs 4).toNat - 64 - 24 = (s.regs 4).toNat - 88 by omega]
  have hS1sp : S1.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) := by
    apply BitVec.eq_of_toNat_eq
    rw [hS1]; simp only [setRegF_apply]; simp
    omega
  have hS1f : MemFrame cm S1.mem [((s.regs 4).toNat - 88, (s.regs 4).toNat - 80),
      ((s.regs 4).toNat - 72, (s.regs 4).toNat - 64), ((s.regs 4).toNat - 56, (s.regs 4).toNat - 48)] := by
    rw [hS1mem]; janus_frame
  have hS1fc : MemFrame cm S1.mem [((s.regs 4).toNat - 88, (s.regs 4).toNat - 48)] :=
    hS1f.mono fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hS1f' : MemFrame cm S1.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hS1fc.mono fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hS1fW : MemFrame s.mem S1.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hW.trans hS1f' fun a n h => ⟨h, h⟩
  have hagS1 : Spec.Map.Agrees cm S1.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - 88) (hi := (s.regs 4).toNat - 48) hS1fc
      (Outside.of_sub hout (by omega) (by omega))
  have hgS1 : gOf S1 = gOf s := by rw [hS1]; simp [gOf, setRegF]
  have hcl : ∀ a, a ≥ (s.regs 4).toNat - 40 → S1.mem.readLE a 8 = cm.readLE a 8 := by
    intro a ha
    rw [hS1mem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hbody1 := body1 impl P hl U hat hdr s hc 4748066 (by decide) tt td htt htd [] rest
  refine ReachesRet.call hbody1 (by rw [hS1]) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hS1fW, hl.env_frame _ _ henv hagS1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · rw [hS1]; simp [setRegF]
  · rw [hS1]; simp [setRegF]
  · rw [hS1]; simp [setRegF]
  · rw [hS1]; simpa [setRegF] using hx15
  · rw [hS1]
  · exact hS1sp
  · rw [hS1mem, Janus.Arm64.Memory.readLE_writeLE_self]
  · rw [hcl _ (by omega)]; exact hc32
  · rw [hcl _ (by omega)]; exact hc24
  · rw [hcl _ (by omega)]; exact hc16
  · rw [hS1mem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hst1
  · rw [hl.defers_frame _ _ _ hagS1]; exact hdef
  · rw [hl.saved_frame _ _ _ hagS1]; exact hsv
  · exact hrest
  · rw [hl.room_frame _ _ _ hagS1]; omega
  intro e1 hpc1 hq1
  obtain ⟨hp1, hs1sp, hs114, hs15, hx1, hdf1, hr01, hf1, henv1, hd1, hsv1, hpn1, hrm1, hst11⟩ := hq1
  have hS1ra : S1.mem.readLE (S1.regs 4).toNat 8 = 4748066 := by
    rw [hS1sp, hS1mem]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
  have hs1sp' : e1.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 80) := by
    rw [hs1sp, hS1sp]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  have hs1g : e1.regs 14 = s.regs 14 := by rw [hs114, hS1]; simp [setRegF]
  have hs1ip : e1.rip = BitVec.ofNat 64 4748066 := by
    rw [hp1, retAddrOf, hS1ra]
  have hs1rbp : e1.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 64) - 8#64 := by
    rw [hs15, hS1]; simp [setRegF]
  have hF1 : ∀ a n, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - (P.depth + 144) ∨ (s.regs 4).toNat - 88 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat - 40 ≤ a) → e1.mem.readLE a n = S1.mem.readLE a n := by
    intro a n h1 h2 h3
    exact hf1.readLE a n (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3⟩)
  have hspill : e1.mem.readLE ((s.regs 4).toNat - 56) 8 = (s.regs 4).toNat - 40 := by
    rw [hF1 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega), hS1mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 4).isLt; omega)
  have hcb1 : e1.mem.readLE ((s.regs 4).toNat - 40) 8 = bodyA := by
    rw [hF1 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega), hS1mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hcb
  have hc32b : e1.mem.readLE ((s.regs 4).toNat - 32) 8 = (s.regs 4).toNat - 48 := by
    rw [hF1 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega), hS1mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hc32
  have hc24b : e1.mem.readLE ((s.regs 4).toNat - 24) 8 = tt := by
    rw [hF1 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega), hS1mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hc24
  have hc16b : e1.mem.readLE ((s.regs 4).toNat - 16) 8 = td := by
    rw [hF1 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega), hS1mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hc16
  have hrbp72 : e1.mem.readLE ((s.regs 4).toNat - 72) 8 = (cr 5).toNat := by
    rw [hF1 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega), hS1mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (cr 5).isLt
  have hret64 : e1.mem.readLE ((s.regs 4).toNat - 64) 8 = 4748198 := by
    rw [hF1 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega), hS1mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hret
  obtain ⟨dr1, dpc1, dfl1, dxm1, dm1, dyh1, dfs1, ddf1, dmx1⟩ := e1
  dsimp only at *
  subst hs1ip hdf1
  have hdr1' : dr1 = setRegF (setRegF (setRegF (setRegF dr1 0 1#64)
      4 (BitVec.ofNat 64 ((s.regs 4).toNat - 80))) 5 (BitVec.ofNat 64 ((s.regs 4).toNat - 64) - 8#64))
      14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact hs1g
    · rw [if_neg h14]
      by_cases h5 : i = 5
      · rw [if_pos h5, h5]; exact hs1rbp
      · rw [if_neg h5]
        by_cases h4 : i = 4
        · rw [if_pos h4, h4]; exact hs1sp'
        · rw [if_neg h4]
          by_cases h0 : i = 0
          · rw [if_pos h0, h0]; exact hr01
          · rw [if_neg h0]
  have hspill24 : dm1.readLE ((s.regs 4).toNat - 80 + 24) 8 = (s.regs 4).toNat - 40 := by
    rw [show (s.regs 4).toNat - 80 + 24 = (s.regs 4).toNat - 56 by omega]; exact hspill
  rw [hdr1']
  janus64_run [hspill24, hcb1] until [bodyA]
  refine ReachesRet.name fun S2 hS2 => ?_
  have hS2mem : S2.mem = Janus.Arm64.Memory.writeLE dm1 ((s.regs 4).toNat - 88) 8 4748085 := by
    rw [hS2]; simp only [show (s.regs 4).toNat - 80 - 8 = (s.regs 4).toNat - 88 by omega]
  have hS2sp : S2.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 88) := by
    apply BitVec.eq_of_toNat_eq
    rw [hS2]; simp only [setRegF_apply]; simp
    omega
  have hS2f : MemFrame dm1 S2.mem [((s.regs 4).toNat - 88, (s.regs 4).toNat - 80)] := by
    rw [hS2mem]; janus_frame
  have hW1' : MemFrame s.mem dm1 (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hS1fW.trans (hf1.mono fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h; exact ⟨h1, by omega, by omega⟩)
      fun a n h => ⟨h, h⟩
  have hS2fW : MemFrame s.mem S2.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hW1'.trans (hS2f.mono fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega)
      fun a n h => ⟨h, h⟩
  have hagS2 : Spec.Map.Agrees dm1 S2.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - 88) (hi := (s.regs 4).toNat - 80) hS2f
      (Outside.of_sub hout (by omega) (by omega))
  have hS2d : ∀ a, a ≥ (s.regs 4).toNat - 80 → S2.mem.readLE a 8 = dm1.readLE a 8 := by
    intro a ha
    rw [hS2mem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hbody2 := body2 impl P hl U hat hdr s hc 4748085 (by decide) tt td htt htd [fvA] rest
  refine ReachesRet.call hbody2 (by rw [hS2]) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hS2fW, hl.env_frame _ _ henv1 hagS2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · rw [hS2]; simp [setRegF]
  · rw [hS2]; simp [setRegF]
  · rw [hS2]; simp [setRegF, hs1g]
  · rw [hS2]; simpa [setRegF] using hx1
  · rw [hS2]
  · exact hS2sp
  · rw [hS2mem, Janus.Arm64.Memory.readLE_writeLE_self]
  · rw [hS2d _ (by omega)]; exact hc32b
  · rw [hS2d _ (by omega)]; exact hc24b
  · rw [hS2d _ (by omega)]; exact hc16b
  · rw [hS2d _ (by omega)]; exact hst11
  · rw [hl.defers_frame _ _ _ hagS2]; exact hd1
  · rw [hl.saved_frame _ _ _ hagS2]; exact hsv1
  · exact hrest
  · rw [hl.room_frame _ _ _ hagS2]
    have : P.room cm (gOf s) = P.room S1.mem (gOf s) := by rw [hl.room_frame _ _ _ hagS1]
    omega
  intro e2 hpc2 hq2
  obtain ⟨hp2, hs2sp, hs214, hs25, hx2, hdf2, hr02, hf2, henv2, hd2, hsv2, hpn2, hrm2, hst22⟩ := hq2
  have hS2ra : S2.mem.readLE (S2.regs 4).toNat 8 = 4748085 := by
    rw [hS2sp, hS2mem]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
  have hs2ip : e2.rip = BitVec.ofNat 64 4748085 := by rw [hp2, retAddrOf, hS2ra]
  have hs2sp' : e2.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 80) := by
    rw [hs2sp, hS2sp]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  have hs2g : e2.regs 14 = s.regs 14 := by rw [hs214, hS2]; simp [setRegF, hs1g]
  have hs2rbp : e2.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 64) - 8#64 := by
    rw [hs25, hS2]; simp [setRegF]
  have hF2 : ∀ a n, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - (P.depth + 144) ∨ (s.regs 4).toNat - 88 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat - 40 ≤ a) → e2.mem.readLE a n = S2.mem.readLE a n := by
    intro a n h1 h2 h3
    exact hf2.readLE a n (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3⟩)
  have hrbp72' : e2.mem.readLE ((s.regs 4).toNat - 72) 8 = (cr 5).toNat := by
    rw [hF2 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega), hS2d _ (by omega)]
    exact hrbp72
  have hret64' : e2.mem.readLE ((s.regs 4).toNat - 64) 8 = 4748198 := by
    rw [hF2 _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega), hS2d _ (by omega)]
    exact hret64
  have hcM : MemFrame cm e2.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 64),
      ((s.regs 4).toNat - 56, (s.regs 4).toNat - 40)]) := by
    have a1 : MemFrame cm S1.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 64),
        ((s.regs 4).toNat - 56, (s.regs 4).toNat - 40)]) :=
      hS1f.mono fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; obtain ⟨_, h2, h3⟩ := h; refine ⟨?_, ?_, ?_⟩ <;> omega
    have a2 : MemFrame cm dm1 (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 64),
        ((s.regs 4).toNat - 56, (s.regs 4).toNat - 40)]) :=
      a1.trans (hf1.mono fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
        obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, by omega, by omega⟩) fun a n h => ⟨h, h⟩
    have a3 : MemFrame cm S2.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat - 64),
        ((s.regs 4).toNat - 56, (s.regs 4).toNat - 40)]) :=
      a2.trans (hS2f.mono fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; obtain ⟨_, h2, h3⟩ := h; omega)
        fun a n h => ⟨h, h⟩
    exact a3.trans (hf2.mono fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, by omega, by omega⟩) fun a n h => ⟨h, h⟩
  obtain ⟨dr2, dpc2, dfl2, dxm2, dm2, dyh2, dfs2, ddf2, dmx2⟩ := e2
  dsimp only at *
  subst hs2ip hdf2
  have hdr2' : dr2 = setRegF (setRegF (setRegF (setRegF dr2 0 1#64)
      4 (BitVec.ofNat 64 ((s.regs 4).toNat - 80))) 5 (BitVec.ofNat 64 ((s.regs 4).toNat - 64) - 8#64))
      14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact hs2g
    · rw [if_neg h14]
      by_cases h5 : i = 5
      · rw [if_pos h5, h5]; exact hs2rbp
      · rw [if_neg h5]
        by_cases h4 : i = 4
        · rw [if_pos h4, h4]; exact hs2sp'
        · rw [if_neg h4]
          by_cases h0 : i = 0
          · rw [if_pos h0, h0]; exact hr02
          · rw [if_neg h0]
  have hrbp72'' : dm2.readLE ((s.regs 4).toNat - 80 + 8) 8 = (cr 5).toNat := by
    rw [show (s.regs 4).toNat - 80 + 8 = (s.regs 4).toNat - 72 by omega]; exact hrbp72'
  have hret64'' : dm2.readLE ((s.regs 4).toNat - 80 + 16) 8 = 4748198 := by
    rw [show (s.regs 4).toNat - 80 + 16 = (s.regs 4).toNat - 64 by omega]; exact hret64'
  have hret64c : cm.readLE ((s.regs 4).toNat - 64) 8 = 4748198 := hret
  rw [hdr2']
  janus64_run [hrbp72'', hret64'', hret64c]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcM, henv2, hd2, hsv2, ?_, ?_, hst22⟩
  · simp only [retAddrOf, setRegF_apply]; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, hret]
  · simp only [setRegF_apply]; simp
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  · simp [setRegF]
  · simp [setRegF]
  · exact hx2
  · rfl
  · show P.panics dm2 (gOf s) = P.panics cm (gOf s)
    rw [hpn2, hl.panics_frame _ _ _ hagS2, hpn1, hl.panics_frame _ _ _ hagS1]
  · show P.room cm (gOf s) ≤ P.room dm2 (gOf s) + 2
    have e1 : P.room S1.mem (gOf s) = P.room cm (gOf s) := by rw [hl.room_frame _ _ _ hagS1]
    have e2 : P.room S2.mem (gOf s) = P.room dm1 (gOf s) := by rw [hl.room_frame _ _ _ hagS2]
    omega

/-- The precondition of `correctness`, as one proposition. -/
def Pre (P : Spec.PanicRuntime) (s : State) : Prop :=
  PanicCallerOK P s 144 8 ∧ Extracted.program.DataLoaded s.mem ∧ s.mem.accessible accA 8 true = true ∧
    Outside accA 8 (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) ∧
    Outside fvA 16 (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) ∧
    3 ≤ P.room s.mem (gOf s) ∧ P.saved s.mem (gOf s) = none ∧
    ∀ d ∈ P.defers s.mem (gOf s), (s.regs 4).toNat ≤ d.sp

/-- What the runtime and the deferred calls write at the exit: `P.priv`, the runtime's window below
the frame and `Acc`. -/
abbrev winB (P : Spec.PanicRuntime) (s : State) : List (Nat × Nat) :=
  P.priv ++ [((s.regs 4).toNat - 56 - P.depth, (s.regs 4).toNat - 64), (accA, accA + 8)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hrf : DeferrangefuncContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferrangefunc") P)
    (hat : DeferprocatContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferprocat") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry []
      (fun s => Pre P s)
      (fun _ => goClass P)
      (fun s s' => s'.mem.readLE accA 8 = mix (s.mem.readLE accA 8))
      (fun _ _ _ => False) := by
  intro ret hret s hs hpre
  obtain ⟨hc, hd, hacc, hao, hfo, hroom, hsave, hdss⟩ := hpre
  have hc' := hc
  obtain ⟨henv, hg, hal, hd', hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd' hb hal hdss
  have hr47 : ret < 2 ^ 47 := hret.user
  have h64 : (s.regs 4 - 64#64).toNat = (s.regs 4).toNat - 64 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hagw : ∀ m, MemFrame s.mem m [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)] →
      Spec.Map.Agrees s.mem m P.priv :=
    fun m hf => Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 144)) (hi := (s.regs 4).toNat + 8) hf
      (Outside.of_sub hout (by omega) (by omega))
  have hao2 : accA + 8 ≤ (s.regs 4).toNat - (P.depth + 144) ∨ (s.regs 4).toNat + 8 ≤ accA := by
    have h := hao
    simp only [outside_append, outside_cons, outside_nil, and_true] at h
    exact h.2
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn"))
    hret.fetch_none ?_
  -- RangeDefer: start the range-over-func defer list
  janus64_run until [Extracted.program.contractAddr "runtime.deferrangefunc"]
  refine ReachesRet.name fun S hS => ?_
  have hSsp : S.regs 4 = s.regs 4 - 64#64 := by rw [hS] <;> simp [setRegF]
  have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [hSsp]; exact h64
  have hS14 : S.regs 14 = s.regs 14 := by rw [hS] <;> simp [setRegF]
  have hS5 : S.regs 5 = s.regs 4 - 8#64 := by rw [hS] <;> simp [setRegF]
  have hSx : S.xmm 15 = 0 := by rw [hS]; exact h_x15
  have hSdf : S.df = false := by rw [hS]
  have hSpc : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferrangefunc") := by
    rw [hS] <;> rfl
  have hSmem : S.mem = (Janus.Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      ((s.regs 4).toNat - 64) 8 4748147 := by rw [hS]
  have hSf : MemFrame s.mem S.mem [((s.regs 4).toNat - 64, (s.regs 4).toNat - 56),
      ((s.regs 4).toNat - 8, (s.regs 4).toNat)] := by
    rw [hSmem]; janus_frame
  have hSfW : MemFrame s.mem S.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hSf.mono fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; obtain ⟨h1, h2⟩ := h
      exact ⟨by omega, by omega⟩
  have hSra : S.mem.readLE (S.regs 4).toNat 8 = 4748147 := by
    rw [hSmem, hSspn, Janus.Arm64.Memory.readLE_writeLE_self]
  have hgS : gOf S = gOf s := by simp only [gOf, hS14]
  have hSf1 : MemFrame s.mem S.mem [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)] :=
    hSf.mono fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hagS : Spec.Map.Agrees s.mem S.mem P.priv := hagw _ hSf1
  refine ReachesRet.call hrf hSpc ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
      (by rw [hSspn]; omega) hS14 hSx hSdf (by rw [hSra]; decide),
    by rw [hgS, hl.room_frame _ _ _ hagS]; omega⟩ ?_
  intro s1 hpc1 hq1
  obtain ⟨⟨r1, x1, y1, f1, m1, hs1, hfr1, henv1⟩, hx0, hdef1, hkeep1⟩ := hq1
  have hm1 : s1.mem = m1 := by rw [hs1]
  simp only [MapAmd64.calleeStack, hSspn] at hfr1
  have hW1 : MemFrame s.mem m1 (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hSfW.trans hfr1 fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega, by omega⟩⟩
  have hd1 : P.defers m1 (gOf s) = { sp := (s.regs 4).toNat - 56, fns := [], token := some (s1.regs 3).toNat } ::
      P.defers s.mem (gOf s) := by
    have := hdef1
    rw [hm1, hgS, show fspOf S = (s.regs 4).toNat - 56 by simp only [fspOf, hSspn]; omega,
      hl.defers_frame _ _ _ hagS] at this
    exact this
  have hsv1 : P.saved m1 (gOf s) = none := by
    have := hkeep1.2.1; rw [hm1, hgS, hl.saved_frame _ _ _ hagS] at this; rw [this]; exact hsave
  have hpn1 : P.panics m1 (gOf s) = P.panics s.mem (gOf s) := by
    have := hkeep1.1; rw [hm1, hgS, hl.panics_frame _ _ _ hagS] at this; exact this
  have hrm1 : P.room s.mem (gOf s) ≤ P.room m1 (gOf s) + 1 := by
    have := hkeep1.2.2.2; rw [hm1, hgS, hl.room_frame _ _ _ hagS] at this; exact this
  have hk : ∀ a n, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - 64 - P.depth ∨ (s.regs 4).toNat - 56 ≤ a) →
      m1.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2
    exact hfr1.readLE a n (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, by omega, by omega⟩)
  have hrbp1 : m1.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hk _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega), hSmem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 5).isLt
  have hret1 : m1.readLE (s.regs 4).toNat 8 = ret := by
    rw [hk _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega), hSmem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact h_ret
  clear hdef1 hkeep1 hm1 hpc1
  subst hs1
  janus64_run until [count2A]
  refine ReachesRet.name fun S2 hS2 => ?_
  have hS2mem : S2.mem = (((((Janus.Arm64.Memory.writeLE m1 ((s.regs 4).toNat - 48) 8 1).writeLE
      ((s.regs 4).toNat - 40) 8 4748256).writeLE ((s.regs 4).toNat - 32) 8 ((s.regs 4).toNat - 48)).writeLE
      ((s.regs 4).toNat - 24) 8 (r1 0).toNat).writeLE ((s.regs 4).toNat - 16) 8 (r1 3).toNat).writeLE
      ((s.regs 4).toNat - 64) 8 4748198 := by rw [hS2]
  have hS2sp : S2.regs 4 = s.regs 4 - 64#64 := by rw [hS2] <;> simp [setRegF]
  have hS2spn : (S2.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [hS2sp]; exact h64
  have hS214 : S2.regs 14 = s.regs 14 := by rw [hS2] <;> simp [setRegF, MapAmd64.keepABI, hS14]
  have hS2x : S2.xmm 15 = 0 := by rw [hS2]; simpa [MapAmd64.keepX15] using hSx
  have hS20 : S2.regs 0 = BitVec.ofNat 64 ((s.regs 4).toNat - 40) := by
    rw [hS2]; simp only [setRegF_apply]; simp
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
  have hS2f : MemFrame m1 S2.mem [((s.regs 4).toNat - 64, (s.regs 4).toNat - 56),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 8)] := by
    rw [hS2mem]; janus_frame
  have hS2f1 : MemFrame m1 S2.mem [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)] :=
    hS2f.mono fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hS2fW : MemFrame s.mem S2.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hW1.trans hS2f1 fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagS2 : Spec.Map.Agrees m1 S2.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 144)) (hi := (s.regs 4).toNat + 8) hS2f1
      (Outside.of_sub hout (by omega) (by omega))
  have hgS2 : gOf S2 = gOf s := by simp only [gOf, hS214]
  have hs13 : MapAmd64.keepABI S.regs r1 3 = r1 3 := by simp [MapAmd64.keepABI]
  have hS2d : ∀ a, a ≥ (s.regs 4).toNat → S2.mem.readLE a 8 = m1.readLE a 8 := by
    intro a ha
    rw [hS2mem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hbody := count2_run impl P hl U hat hdr s hc (r1 0).toNat (r1 3).toNat (r1 0).isLt (r1 3).isLt
    (P.defers s.mem (gOf s))
  refine ReachesRet.call hbody (by rw [hS2]) ⟨?_, ?_, ?_, ?_, ?_, ?_, hS2fW, hl.env_frame _ _ henv1 hagS2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · exact hS20
  · exact hS214
  · exact hS2x
  · rw [hS2]
  · rw [hS2sp]; apply BitVec.eq_of_toNat_eq; rw [h64, BitVec.toNat_ofNat]; omega
  · rw [hS2mem, Janus.Arm64.Memory.readLE_writeLE_self]
  · rw [hS2mem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  · rw [hS2mem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 4).isLt; omega)
  · rw [hS2mem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (r1 0).isLt
  · rw [hS2mem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (r1 3).isLt
  · rw [hS2mem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  · rw [hl.defers_frame _ _ _ hagS2]; simpa [MapAmd64.keepABI] using hd1
  · rw [hl.saved_frame _ _ _ hagS2]; exact hsv1
  · intro d hd; have := hdss d hd; omega
  · rw [hl.room_frame _ _ _ hagS2]; omega
  intro e' hpc' hq'
  obtain ⟨hp', hs'sp, hs'14, hs'5, hx', hdf', hf', henv', hd', hsv', hpn', hrm', hst'⟩ := hq'
  have hS2ra : S2.mem.readLE (S2.regs 4).toNat 8 = 4748198 := by
    rw [hS2spn, hS2mem, Janus.Arm64.Memory.readLE_writeLE_self]
  have hs'ip : e'.rip = BitVec.ofNat 64 4748198 := by rw [hp', retAddrOf, hS2ra]
  have hs'sp' : e'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 56) := by
    rw [hs'sp, hS2sp]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
  have hs'g : e'.regs 14 = s.regs 14 := by rw [hs'14, hS214]
  have hS2rbp : S2.regs 5 = s.regs 4 - 8#64 := by
    rw [hS2]; simp [setRegF, MapAmd64.keepABI, hS5]
  have hs'rbp : e'.regs 5 = s.regs 4 - 8#64 := by rw [hs'5, hS2rbp]
  have hS2d8 : ∀ a, a ≥ (s.regs 4).toNat - 8 → S2.mem.readLE a 8 = m1.readLE a 8 := by
    intro a ha
    rw [hS2mem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hF'e : ∀ a n, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - (P.depth + 144) ∨ (s.regs 4).toNat - 64 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 56 ∨ (s.regs 4).toNat - 40 ≤ a) → e'.mem.readLE a n = S2.mem.readLE a n := by
    intro a n h1 h2 h3
    exact hf'.readLE a n (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3⟩)
  have hrbpE : e'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hF'e _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega), hS2d8 _ (by omega)]
    exact hrbp1
  have hretE : e'.mem.readLE (s.regs 4).toNat 8 = ret := by
    rw [hF'e _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega), hS2d8 _ (by omega)]
    exact hret1
  obtain ⟨dr, dpc, dfl, dxm, dm, dyh, dfs, ddf, dmx⟩ := e'
  dsimp only at *
  subst hs'ip hdf'
  have hdr' : dr = setRegF (setRegF (setRegF dr 4 (BitVec.ofNat 64 ((s.regs 4).toNat - 56))) 5
      (s.regs 4 - 8#64)) 14 (s.regs 14) := by
    funext i; simp only [setRegF]
    by_cases h14 : i = 14
    · rw [if_pos h14, h14]; exact hs'g
    · rw [if_neg h14]
      by_cases h5 : i = 5
      · rw [if_pos h5, h5]; exact hs'rbp
      · rw [if_neg h5]
        by_cases h4 : i = 4
        · rw [if_pos h4, h4]; exact hs'sp'
        · rw [if_neg h4]
  have hst8 : dm.readLE ((s.regs 4).toNat - 56 + 8) 8 = 1 := by
    rw [show (s.regs 4).toNat - 56 + 8 = (s.regs 4).toNat - 48 by omega]; exact hst'
  rw [hdr']
  janus64_run [hst8] until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine ReachesRet.done rfl ?_
  refine GoReturns.name fun D hD => ?_
  have hDmem : D.mem = (Janus.Arm64.Memory.writeLE dm ((s.regs 4).toNat - 48) 8 3).writeLE
      ((s.regs 4).toNat - 64) 8 4748220 := by
    rw [hD]
    simp only [show (s.regs 4).toNat - 56 + 8 = (s.regs 4).toNat - 48 by omega,
      show (s.regs 4).toNat - 56 - 8 = (s.regs 4).toNat - 64 by omega]
  have hDsp : D.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 56) - 8#64 := by rw [hD] <;> simp [setRegF]
  have hDspn : (D.regs 4).toNat = (s.regs 4).toNat - 64 := by
    rw [hDsp, BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
  have hD14 : D.regs 14 = s.regs 14 := by rw [hD] <;> simp [setRegF]
  have hD5 : D.regs 5 = s.regs 4 - 8#64 := by rw [hD] <;> simp [setRegF]
  have hDx : D.xmm 15 = 0 := by rw [hD]; exact hx'
  have hDdf : D.df = false := by rw [hD]
  have hDpc : D.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by
    rw [hD] <;> rfl
  have hgD : gOf D = gOf s := by simp only [gOf, hD14]
  have hDra : D.mem.readLE (D.regs 4).toNat 8 = 4748220 := by
    rw [hDmem, hDspn, Janus.Arm64.Memory.readLE_writeLE_self]
  have hDf : MemFrame dm D.mem [((s.regs 4).toNat - 64, (s.regs 4).toNat - 56),
      ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)] := by
    rw [hDmem]; janus_frame
  have hDf1 : MemFrame dm D.mem [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)] :=
    hDf.mono fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hW2 : MemFrame s.mem dm (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    (hW1.trans hS2f1 fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩).trans
      (hf'.mono fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
        obtain ⟨h1, h2⟩ := h; exact ⟨h1, by omega, by omega⟩) fun a n h => ⟨h, h⟩
  have hDfW : MemFrame s.mem D.mem (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    hW2.trans hDf1 fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagD : Spec.Map.Agrees dm D.mem P.priv :=
    Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 144)) (hi := (s.regs 4).toNat + 8) hDf1
      (Outside.of_sub hout (by omega) (by omega))
  have hpre : PanicPre P 0 D := PanicPre.of_within hc hDfW (hl.env_frame _ _ henv' hagD) (by omega) (by omega)
    (by omega) hD14 hDx hDdf (by rw [hDra]; decide)
  have hdefD : P.defers D.mem (gOf D) = { sp := (s.regs 4).toNat - 56, fns := [fvA + 8, fvA], token := some (r1 3).toNat } ::
      P.defers s.mem (gOf s) := by
    rw [hgD, hl.defers_frame _ _ _ hagD]; simpa [MapAmd64.keepABI] using hd'
  have hsvD : P.saved D.mem (gOf D) = none := by rw [hgD, hl.saved_frame _ _ _ hagD]; exact hsv'
  have hfspD : fspOf D = (s.regs 4).toNat - 56 := by simp only [fspOf, hDspn]; omega
  have hF : retFrame P D = ⟨(s.regs 4).toNat - 56, (s.regs 4).toNat - 56, 0, none⟩ := by
    simp only [retFrame, hsvD, hfspD]
  have hds' : ∀ d ∈ P.defers s.mem (gOf s), (s.regs 4).toNat - 56 < d.sp := fun d hd => by
    have := hdss d hd; omega
  have hrA := recItems_above hds'
  have hI : frameItems D.mem (retFrame P D) (P.defers D.mem (gOf D)) =
      [{ fn := fvA + 8, bits := none, chain := { sp := (s.regs 4).toNat - 56, fns := [fvA] } ::
          P.defers s.mem (gOf s) },
       { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] := by
    rw [hF, hdefD]
    simp [frameItems, recItems, fnItems, hrA]
  have hfo1 : Outside fvA 8 (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
    Outside.of_sub hfo (by omega) (by omega)
  have hfo2 : Outside (fvA + 8) 8 (P.priv ++ [((s.regs 4).toNat - (P.depth + 144), (s.regs 4).toNat + 8)]) :=
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
      rcases hit with rfl | rfl <;> dsimp only
      · exact ⟨by omega, hfa2, by rw [hfv2], by rw [hfv2]; decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
      · exact ⟨by omega, hfa1, by rw [hfv1], by rw [hfv1]; decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl <;> dsimp only
      · rw [hfv2]; decide
      · rw [hfv1]; decide
  have hpaD : D.mem.accessible accA 8 true = true := by rw [hDfW.accessible]; exact hacc
  have hv0 : D.mem.readLE accA 8 = s.mem.readLE accA 8 := hDfW.readLE _ _ hao
  have hKp : frameKeep D.mem ⟨(s.regs 4).toNat - 56, (s.regs 4).toNat - 56, 0, none⟩
      [{ fn := fvA + 8, bits := none, chain := { sp := (s.regs 4).toNat - 56, fns := [fvA] } ::
          P.defers s.mem (gOf s) },
       { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] =
      [(fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)] := by
    simp [frameKeep, Frame.openAt]
  have hsubR : ∀ a n, Outside a n (winB P s) →
      Outside a n (P.priv ++ rtWin P ⟨(s.regs 4).toNat - 56, (s.regs 4).toNat - 56, 0, none⟩ ++
        bitsWin ⟨(s.regs 4).toNat - 56, (s.regs 4).toNat - 56, 0, none⟩) := by
    intro a n h
    simp only [winB, rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at h ⊢
    exact ⟨h.1, h.2.1⟩
  have hoT : Outside accA 8 (P.priv ++ rtWin P ⟨(s.regs 4).toNat - 56, (s.regs 4).toNat - 56, 0, none⟩ ++
      bitsWin ⟨(s.regs 4).toNat - 56, (s.regs 4).toNat - 56, 0, none⟩) := by
    have hao' := hao
    simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at hao' ⊢
    exact ⟨hao'.1, by omega⟩
  have hsubA : ∀ a n, Outside a n (winB P s) → Outside a n [(accA, accA + 8)] := by
    intro a n h
    simp only [winB, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact h.2.2
  have hoA : ∀ (e : State), (s.regs 4).toNat - 56 - P.depth ≤ (e.regs 4).toNat →
      Outside accA (accA + 8 - accA) (P.priv ++ ((e.regs 4).toNat + 8, (s.regs 4).toNat - 56) ::
        [(fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) := by
    intro e hlo
    have hao' := hao
    simp only [outside_append, outside_cons, outside_nil, and_true] at hao' ⊢
    simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hao'.1, by omega, by omega, by omega⟩
  have hacD : ∀ (e : State), (s.regs 4).toNat - 56 - P.depth ≤ (e.regs 4).toNat →
      (e.regs 4).toNat + 16 ≤ (s.regs 4).toNat - 56 →
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
  have hae1 : MemFrame D.mem e1.mem (winB P s) := hfrE1.mono hsubR
  have hm1 : e1.mem.readLE (fvA + 8) 8 = accAdd2A := by
    rw [hae1.readLE _ _ (by
      simp only [winB, outside_append, outside_cons, outside_nil, and_true]
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
  have hacc1 : MemFrame D.mem f1.mem (winB P s) := hae1.trans hff1 fun a n h => ⟨h, hsubA a n h⟩
  obtain ⟨hdr1, hpf1⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 56)
    (keep := [(fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl
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
  have hae2 : MemFrame D.mem e2.mem (winB P s) := hacc1.trans hfrE2 fun a n h => ⟨h, hsubR a n h⟩
  have hm2 : e2.mem.readLE fvA 8 = accAdd1A := by
    rw [hae2.readLE _ _ (by
      have h2 := hfo1
      simp only [outside_append, outside_cons, outside_nil, and_true] at h2
      simp only [winB, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h2.1, by omega, by omega⟩)]
    exact hfv1
  have hv2 : e2.mem.readLE accA 8 = digit 2 (s.mem.readLE accA 8) := by
    rw [hfrE2.readLE _ _ hoT]; exact hw1
  rw [hm2] at hpc2
  have hpa2 : e2.mem.accessible accA 8 true = true := by rw [hae2.accessible]; exact hpaD
  have hrac2 : e2.mem.accessible (e2.regs 4).toNat 8 false = true :=
    hacD e2 hlo2 hhi2 e2.mem (fun a n w => by rw [hae2.accessible])
  have hcl2 := call_acc1 impl e2 hpc2 hpa2 hra2 hrac2 (by omega)
  obtain ⟨j2, f2, hj2, -, hfpc2, hfsp2, hf142, hf52, hfx2, hfdf2, hff2, hpv2⟩ := hcl2
  refine GoReturns.of_steps (hj2.withExit hret.fetch_none) ?_
  have hw2 : f2.mem.readLE accA 8 = digit 1 (digit 2 (s.mem.readLE accA 8)) := by rw [hpv2, hv2]
  have hacc2 : MemFrame D.mem f2.mem (winB P s) := hae2.trans hff2 fun a n h => ⟨h, hsubA a n h⟩
  obtain ⟨hdr2, hpf2⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 56)
    (keep := [(fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl
    (by rw [hfpc2, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)) hfsp2
    (hf142.trans h14_2) hf52 (by rw [hfx2]; exact hx2) (by rw [hfdf2]; exact hdf2) henvE2 hff2
    (hoA e2 hlo2)
  have hE2 := (hcont2 f2 hdr2).1 (hpf2.trans hpn2)
  rw [Engine_nil] at hE2
  obtain ⟨k3, d2, hst3, hfin⟩ := hE2
  obtain ⟨hfpc, hfsp, hf14, hf5, hfx, hfdf, hfmf, hfenv, -⟩ := hfin
  refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
  obtain ⟨er, erip, efl, exm, em, eyh, efs, edf, emx⟩ := d2
  dsimp only at hfpc hfsp hf14 hf5 hfx hfdf hfmf hfenv
  rw [hDra] at hfpc
  have hepc : erip = BitVec.ofNat 64 4748220 := by
    apply BitVec.eq_of_toNat_eq; rw [hfpc, BitVec.toNat_ofNat]
  subst hepc hfdf
  have he4 : er 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 56) := by
    rw [hfsp, hDsp]; apply BitVec.eq_of_toNat_eq
    have := (s.regs 4).isLt
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp; omega
  have he5 : er 5 = s.regs 4 - 8#64 := by rw [hf5, hD5]
  have he14 : er 14 = s.regs 14 := by rw [hf14, hD14]
  have her : er = setRegF (setRegF (setRegF er 4 (BitVec.ofNat 64 ((s.regs 4).toNat - 56))) 5 (s.regs 4 - 8#64))
      14 (s.regs 14) := by
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
  have hxfer : ∀ a n, Outside a n P.priv → (a + n ≤ (s.regs 4).toNat - 56 - P.depth ∨ (s.regs 4).toNat - 64 ≤ a) →
      (a + n ≤ accA ∨ accA + 8 ≤ a) → (a + n ≤ (s.regs 4).toNat - 64 ∨ (s.regs 4).toNat - 56 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat - 40 ≤ a) →
      em.readLE a n = dm.readLE a n := by
    intro a n hpr h1 h2 h3 h4
    rw [hfmf.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpr, h1⟩),
      hacc2.readLE _ _ (by
      simp only [winB, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hpr, h1, h2⟩), hDmem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hdl : em.readLE (s.regs 4).toNat 8 = ret := by
    rw [hxfer _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega) (by omega)]
    exact hretE
  have hdf8 : em.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hxfer _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega) (by omega)]
    exact hrbpE
  have hdA : em.readLE accA 8 = mix (s.mem.readLE accA 8) := by
    rw [hfmf.readLE _ _ (by
      have hao' := hao
      simp only [outside_append, outside_cons, outside_nil, and_true] at hao' ⊢
      exact ⟨hao'.1, by omega⟩)]
    exact hw2
  have hdl8 : em.readLE ((s.regs 4).toNat - 56 + 48 + 8) 8 = ret := by
    rw [show (s.regs 4).toNat - 56 + 48 + 8 = (s.regs 4).toNat by omega]; exact hdl
  have hdf8' : em.readLE ((s.regs 4).toNat - 56 + 48) 8 = (s.regs 5).toNat := by
    rw [show (s.regs 4).toNat - 56 + 48 = (s.regs 4).toNat - 8 by omega]; exact hdf8
  refine GoReturns.of_reaches ?_
  janus64_run [hdl8, hdf8']
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; simp; omega
  · rw [hfx]


/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSatAmd64` (code that
`PanicSatAmd64Run`/`PanicSatAmd64Entry` prove meets the three contracts in every program that contains
it) linked into `RangeDefer`'s program with a `jmp` to it at each contract address, and a call state
satisfying the precondition: so `correctness` applies (`nonvacuous`), and `RangeDefer` returns from
that state (`returns`). -/

namespace Witness

open Janus.Contracts.PanicSat (tabWords witMemD)
open Janus.Contracts.PanicSatAmd64
open Janus.Contracts.PanicModel

abbrev T0 : List Spec.FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : Spec.PanicRuntime := P0 T0 RPa

def rfA : Nat := Extracted.program.contractAddr "runtime.deferrangefunc"
def paA : Nat := Extracted.program.contractAddr "runtime.deferprocat"
def drA : Nat := Extracted.program.contractAddr "runtime.deferreturn"

/-- The code linked next to `RangeDefer`: the model engine and a `jmp` to it at each contract address. -/
def implW : List Janus.Amd64.Segment :=
  panicImpl Extracted.program [("runtime.deferrangefunc", eDeferrangefunc), ("runtime.deferprocat", eDeferprocat),
    ("runtime.deferreturn", eDeferreturn)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

set_option maxRecDepth 100000 in
theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubRf : StubAt (Extracted.program.link implW) rfA eDeferrangefunc :=
  StubAt.of_jmp (bs := stubCode rfA eDeferrangefunc) (rel := (eDeferrangefunc + 2 ^ 64 - (rfA + 5)) % 2 ^ 64)
    (len := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubPa : StubAt (Extracted.program.link implW) paA eDeferprocat :=
  StubAt.of_jmp (bs := stubCode paA eDeferprocat) (rel := (eDeferprocat + 2 ^ 64 - (paA + 5)) % 2 ^ 64)
    (len := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubDr : StubAt (Extracted.program.link implW) drA eDeferreturn :=
  StubAt.of_jmp (bs := stubCode drA eDeferreturn) (rel := (eDeferreturn + 2 ^ 64 - (drA + 5)) % 2 ^ 64)
    (len := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem hrf : DeferrangefuncContract (Extracted.program.link implW) rfA PW :=
  deferrangefunc_at stubRf (deferrangefunc_contract engineAt T0)

theorem hat : DeferprocatContract (Extracted.program.link implW) paA PW :=
  deferprocat_at stubPa (deferprocat_contract engineAt T0)

theorem hdr : DeferreturnContract (Extracted.program.link implW) drA PW U1 :=
  deferreturn_at stubDr (deferreturn_run (T := T0) engineAt)

def ret : Nat := 0x200000

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
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wm }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h, rfl⟩

set_option maxRecDepth 100000 in
theorem pre : Pre PW s0 := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩,
    dataLoaded, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · simp only [P0_priv, outside_append, outside_cons, outside_nil, and_true]; decide
  · simp only [P0_priv, outside_append, outside_cons, outside_nil, and_true]; decide
  · show 3 ≤ room0 wm
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
    DeferrangefuncContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferrangefunc") P ∧
    DeferprocatContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferprocat") P ∧
    DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P U ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [] s ∧
    Pre P s :=
  ⟨implW, PW, U1, ret, s0, P0_laws T0 RPa, hrf, hat, hdr, hret, setup, pre⟩

/-- So the guarantee is reached: `RangeDefer` returns, having run its two deferred calls in LIFO
order. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClass PW) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ s'.mem.readLE accA 8 = mix (s0.mem.readLE accA 8)
    | .panicked _ _ => False
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U1 hrf hat hdr ret hret s0 setup pre

end Witness

end Proof
