import Extracted

/-!
# `RangeDefer()`: defers in a range-over-func loop body run in LIFO order (arm64)

`RangeDefer` is `for x := range count2 { if x == 1 { defer accAdd1() } else { defer accAdd2() } }`
over the iterator `count2` (which yields 1 and 2). The defers belong to `RangeDefer`'s frame, not
the loop body closure's: `RangeDefer` gets a token from `runtime.deferrangefunc`, each iteration
of the body records its deferred call on it with `runtime.deferprocat`, the body itself calls
`runtime.deferreturn` (a no-op for its own frame), and `RangeDefer`'s exit (`runtime.deferreturn`)
runs the recorded calls in LIFO order. `accAdd1` / `accAdd2` append the digit 1 / 2 to the package
variable `Acc`.

**Guarantee (example 7 of docs/COVERAGE.md R6).** For every panic-runtime model `P` satisfying its
laws, every implementation of `runtime.deferrangefunc`, `runtime.deferprocat` and
`runtime.deferreturn` meeting their contracts (`Janus.Contracts.Panic`, pinned to the Go 1.26
runtime's code), every admissible return address and every call state in which the runtime is
usable (with the stack for `RangeDefer`, `count2` and the body below), `Acc` is a writable word and
the two deferred functions' funcvals are in memory, with room for three records: the call
**returns** (obeying the ABI) and `Acc` ends as `(Acc*10+2)*10+1` (mod `2^64`).

The iterator `count2` and the loop body are the program's own code, run by the proof; the
iterator's two calls of the body, the `deferprocat` call and the nested `deferreturn` call in each,
and the iteration state machine (state 1 on entry to the body, 2 while it runs, 1 after, 3 at exit)
are all established. `Acc` lives in `.noptrbss`, whose content the binary does not fix, so the
extractor does not copy it and the precondition provides the word (`accA`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Proof

/-! Code addresses are read off the extraction (`janus_eval%`), never copied: a relinked
binary needs no edit. -/
local macro "loc_count2_44" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.count2" + 44))
local macro "loc_count2_64" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.count2" + 64))
local macro "loc_RangeDefer_28" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RangeDefer" + 28))
local macro "loc_RangeDefer_72" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RangeDefer" + 72))
local macro "loc_RangeDefer_96" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RangeDefer" + 96))
local macro "loc_RangeDefer_range1_0" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RangeDefer-range1" + 0))
local macro "loc_RangeDefer_range1_80" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RangeDefer-range1" + 80))
local macro "loc_RangeDefer_range1_96" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RangeDefer-range1" + 96))
local macro "loc_RangeDefer_range1_120" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RangeDefer-range1" + 120))

/-- The address of `example.com/basic.Acc` (`.noptrbss`; the extractor does not copy it). -/
local macro "accA" : term => `(janus_eval% (adrpLdTarget (segAddr Extracted.program "example.com/basic.accAdd1") (segWord Extracted.program "example.com/basic.accAdd1" 0) (segWord Extracted.program "example.com/basic.accAdd1" 1) 3))
local macro "fvA" : term => `(janus_eval% (Extracted.program.data.head!.base))
local macro "bodyA" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.RangeDefer-range1"))

def digit (k v : Nat) : Nat := (v * 10 + k) % 2 ^ 64

local macro "accAdd1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.accAdd1"))
local macro "accAdd2A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.accAdd2"))
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

set_option maxRecDepth 100000 in
theorem fv1_read (m : Memory) (hd : Extracted.program.DataLoaded m) : m.readLE fvA 8 = accAdd1A :=
  readLE_of_dataRead hd (by decide)
set_option maxRecDepth 100000 in
theorem fv2_read (m : Memory) (hd : Extracted.program.DataLoaded m) : m.readLE (fvA + 8) 8 = accAdd2A :=
  readLE_of_dataRead hd (by decide)
set_option maxRecDepth 100000 in
theorem fv_acc (m : Memory) (hd : Extracted.program.DataLoaded m) : m.accessible fvA 16 false = true :=
  accessible_of_dataRead hd (by decide)

/-- What the runtime and the deferred calls write: `P.priv`, the runtime's window below the frame,
and `Acc`. -/
abbrev winB (P : PanicRuntime) (s : State) : List (Nat × Nat) :=
  P.priv ++ [(s.sp.toNat - 64 - P.depth, s.sp.toNat - 64 - 8), (accA, accA + 8)]

/-- The deferred calls in LIFO order. -/
def mix (v : Nat) : Nat := digit 1 (digit 2 v)


theorem ReachesRet.of_steps' {p : Program} {tgt : W64} {S : State} {Q : State → Prop} {R : State → Prop}
    (h : ∃ k d, Program.Steps p S k d ∧ R d) (hcont : ∀ d, R d → ReachesRet p tgt d Q) :
    ReachesRet p tgt S Q := by
  obtain ⟨k, d, hst, hr⟩ := h
  obtain ⟨k', e, hst', he, hq⟩ := hcont d hr
  exact ⟨k + k', e, hst.trans hst', he, hq⟩


/-- A runtime call leaves an 8-byte slot of its caller's frame alone when the slot is outside
`P.priv`, the callee's stack window below its `SP` (not its saved frame pointer slot at `SP - 8`)
and its argument spill area. -/
theorem keep8 {P : PanicRuntime} {S : State} {m m' : Memory} {nargs : Nat} {ex : List (Nat × Nat)}
    (hf : MemFrame m m' (P.priv ++ calleeStack S P.depth nargs ++ ex)) {a : Nat} (hp : Outside a 8 P.priv)
    (h1 : a + 8 ≤ S.sp.toNat - P.depth ∨ S.sp.toNat - 8 ≤ a)
    (h2 : a + 8 ≤ S.sp.toNat + 8 ∨ S.sp.toNat + 8 + 8 * nargs ≤ a) (hex : Outside a 8 ex) :
    m'.readLE a 8 = m.readLE a 8 := by
  rw [hf.readLE _ _ (by
    simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack]
    exact ⟨⟨hp, h1, h2⟩, hex⟩)]

/-- `keep8` for a byte. -/
theorem keep1 {P : PanicRuntime} {S : State} {m m' : Memory} {nargs : Nat} {ex : List (Nat × Nat)}
    (hf : MemFrame m m' (P.priv ++ calleeStack S P.depth nargs ++ ex)) {a : Nat} (hp : Outside a 1 P.priv)
    (h1 : a + 1 ≤ S.sp.toNat - P.depth ∨ S.sp.toNat - 8 ≤ a)
    (h2 : a + 1 ≤ S.sp.toNat + 8 ∨ S.sp.toNat + 8 + 8 * nargs ≤ a) (hex : Outside a 1 ex) :
    m'.readLE a 1 = m.readLE a 1 := by
  rw [hf.readLE _ _ (by
    simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack]
    exact ⟨⟨hp, h1, h2⟩, hex⟩)]

set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hrf : DeferrangefuncContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferrangefunc") P)
    (hat : DeferprocatContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferprocat") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P U) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry []
      (fun s => PanicCallerOK P s 160 0 ∧ Extracted.program.DataLoaded s.mem ∧
        s.mem.accessible accA 8 true = true ∧
        Outside accA 8 (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) ∧
        Outside fvA 16 (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) ∧
        3 ≤ P.room s.mem (gOf s) ∧ P.saved s.mem (gOf s) = none ∧
        ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp)
      (fun _ => goClass P)
      (fun s s' => s'.mem.readLE accA 8 = mix (s.mem.readLE accA 8))
      (fun _ _ _ => False) := by
  intro ret hret s hs ⟨hc, hd, hacc, hao, hfo, hroom, hsave, hdss⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd', hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd
  have h64 : (64 : Nat) ≤ s.sp.toNat := by omega
  have h64' : (s.sp - 64#64).toNat = s.sp.toNat - 64 := by rw [BitVec.toNat_sub]; simp; omega
  have hagw : ∀ m, MemFrame s.mem m [(s.sp.toNat - (P.depth + 160), s.sp.toNat)] → Map.Agrees s.mem m P.priv :=
    fun m hf => Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 160)) (hi := s.sp.toNat) hf
      (Outside.of_sub hout (by omega) (by omega))
  have hr48 : ret < 2 ^ 48 := hret.user
  have hao2 : accA + 8 ≤ s.sp.toNat - (P.depth + 160) ∨ s.sp.toNat ≤ accA := by
    have h := hao
    simp only [outside_append, outside_cons, outside_nil, and_true] at h
    exact h.2
  have h256 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn"))
    hret.fetch_none ?_
  -- RangeDefer: start the range-over-func defer list
  janus_run until [Extracted.program.contractAddr "runtime.deferrangefunc"]
  refine ReachesRet.name fun S hS => ?_
  have hSsp : S.sp = s.sp - 64#64 := by rw [hS] <;> rfl
  have hSspn : S.sp.toNat = s.sp.toNat - 64 := by rw [hSsp]; exact h64'
  have hSf : MemFrame s.mem S.mem [(s.sp.toNat - (P.depth + 160), s.sp.toNat)] := by rw [hS]; janus_frame
  have hS28 : S.regs 28 = s.regs 28 := by rw [hS] <;> rfl
  have hS18 : S.regs 18 = s.regs 18 := by rw [hS] <;> rfl
  have hS30 : S.regs 30 = BitVec.ofNat 64 loc_RangeDefer_28 := by rw [hS] <;> rfl
  have hSpc : S.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferrangefunc") := by rw [hS] <;> rfl
  have hgS : gOf S = gOf s := by simp only [gOf, hS28]
  have hagS : Map.Agrees s.mem S.mem P.priv := hagw _ hSf
  have hSfW : MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) :=
    hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
  refine ReachesRet.call hrf hSpc ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hagS) (by omega) (by omega)
      (by rw [hSspn]; omega) hS28 (by rw [hS30]; decide) (by rw [hS30]; decide),
    by rw [hgS, hl.room_frame _ _ _ hagS]; omega⟩ ?_
  intro s1 hpc1 hq1
  obtain ⟨⟨j1, f1, v1, m1, ex1, ep1, hs1, hfr1, henv1⟩, hx0, hdef1, hpan1, hsav1, hrp1, hroom1⟩ := hq1
  have hm1 : s1.mem = m1 := by rw [hs1]; rfl
  have hstep : ∀ (S : State) (m : Memory) (ex : List (Nat × Nat)) (nargs : Nat),
      MemFrame s.mem S.mem (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) →
      S.sp.toNat + 8 + 8 * nargs ≤ s.sp.toNat → s.sp.toNat - 160 ≤ S.sp.toNat →
      (∀ a n, Outside a n [(s.sp.toNat - (P.depth + 160), s.sp.toNat)] → Outside a n ex) →
      MemFrame S.mem m (P.priv ++ calleeStack S P.depth nargs ++ ex) →
      MemFrame s.mem m (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) := by
    intro S m ex nargs h1 h2 h3 h4 h5
    refine h1.trans h5 fun a n h => ⟨h, ?_⟩
    have h' := h
    simp only [outside_append] at h' ⊢
    obtain ⟨h6, h7⟩ := h'
    refine ⟨⟨h6, ?_⟩, h4 a n h7⟩
    simp only [outside_cons, outside_nil, and_true, calleeStack] at h7 ⊢
    omega
  have hW1 : MemFrame s.mem m1 (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) :=
    hstep S m1 [] 0 hSfW (by omega) (by omega) (fun a n h => by simp only [outside_nil]) (by simpa using hfr1)
  have hgv1 : m1.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hW1.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hgo, by omega⟩)]
  have hga1 : m1.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hW1.accessible]; exact hg2
  have hwin1 : m1.accessible (s.sp.toNat - (P.depth + 160)) (P.depth + 160 + 0) true = true := by
    rw [hW1.accessible]; exact hst
  have hd1 : P.defers m1 (gOf s) = { sp := s.sp.toNat - 64, fns := [], token := some (j1 1).toNat } ::
      P.defers s.mem (gOf s) := by
    have hr1 : s1.regs 1 = j1 1 := by rw [hs1]; simp [retStateX, callRegs_apply]
    have := hdef1; rw [hm1, hgS, hSspn, hl.defers_frame _ _ _ hagS, hr1] at this
    exact this
  have hrm1 : P.room s.mem (gOf s) ≤ P.room m1 (gOf s) + 1 := by
    have := hroom1; rw [hm1, hgS, hl.room_frame _ _ _ hagS] at this; exact this
  have hsv1 : P.saved m1 (gOf s) = none := by
    have := hsav1; rw [hm1, hgS, hl.saved_frame _ _ _ hagS] at this; rw [this]; exact hsave
  have hpn1 : P.panics m1 (gOf s) = P.panics s.mem (gOf s) := by
    have := hpan1; rw [hm1, hgS, hl.panics_frame _ _ _ hagS] at this; exact this
  have hfr1e : MemFrame S.mem m1 (P.priv ++ calleeStack S P.depth 0 ++ []) := by simpa using hfr1
  have hrlr0 : S.mem.readLE (s.sp.toNat - 64) 8 = ret := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    rw [h256]; exact Nat.mod_eq_of_lt (by omega)
  have hrfp0 : S.mem.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat := by
    rw [hS]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    rw [h256]; exact Nat.mod_eq_of_lt (s.regs 29).isLt
  have hrlr1 : m1.readLE (s.sp.toNat - 64) 8 = ret := by
    rw [keep8 hfr1e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hrlr0
  have hrfp1 : m1.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat := by
    rw [keep8 hfr1e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hrfp0
  clear hdef1 hpan1 hsav1 hrp1 hroom1 hSf hSfW hagS hS28 hS18 hS30 hSpc hgS hSsp hSspn hm1 hpc1 hfr1 hfr1e hrlr0 hrfp0
  subst hs1
  subst hS
  janus_run until [Extracted.program.contractAddr "runtime.deferprocat"]
  refine ReachesRet.name fun S2 hS2 => ?_
  have hS2sp : S2.sp = s.sp - 160#64 := by rw [hS2] <;> rfl
  have h160 : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by rw [BitVec.toNat_sub]; simp; omega
  have hS2spn : S2.sp.toNat = s.sp.toNat - 160 := by rw [hS2sp]; exact h160
  have hS2f : MemFrame m1 S2.mem [(s.sp.toNat - (P.depth + 160), s.sp.toNat)] := by rw [hS2]; janus_frame
  have hS228 : S2.regs 28 = s.regs 28 := by rw [hS2] <;> rfl
  have hS218 : S2.regs 18 = s.regs 18 := by rw [hS2] <;> rfl
  have hS230 : S2.regs 30 = BitVec.ofNat 64 loc_RangeDefer_range1_80 := by rw [hS2] <;> rfl
  have hS20 : S2.regs 0 = BitVec.ofNat 64 fvA := by rw [hS2] <;> rfl
  have hS22 : S2.regs 2 = j1 1 := by rw [hS2] <;> simp [setReg]
  have hS2pc : S2.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferprocat") := by rw [hS2] <;> rfl
  have hgS2 : gOf S2 = gOf s := by simp only [gOf, hS228]
  have hS2fW : MemFrame s.mem S2.mem (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) :=
    hW1.trans hS2f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagS2 : Map.Agrees m1 S2.mem P.priv :=
    Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 160)) (hi := s.sp.toNat) hS2f
      (Outside.of_sub hout (by omega) (by omega))
  have hk_state2 : S2.mem.readLE (s.sp.toNat - 48) 8 = 2 := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; decide)
  have hk_bst2 : S2.mem.readLE (s.sp.toNat - 112) 8 = s.sp.toNat - 48 := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; decide)
  have hk_bfp2 : S2.mem.readLE (s.sp.toNat - 168) 8 = s.sp.toNat - 104 := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; decide)
  have hk_blr2 : S2.mem.readLE (s.sp.toNat - 160) 8 = loc_count2_44 := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; decide)
  have hk_c02 : S2.mem.readLE (s.sp.toNat - 56) 8 = s.sp.toNat - 40 := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; decide)
  have hk_clr2 : S2.mem.readLE (s.sp.toNat - 96) 8 = loc_RangeDefer_72 := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; decide)
  have hk_cfp2 : S2.mem.readLE (s.sp.toNat - 104) 8 = s.sp.toNat - 72 := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; decide)
  have hk_code2 : S2.mem.readLE (s.sp.toNat - 40) 8 = loc_RangeDefer_range1_0 := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; decide)
  have hk_cst2 : S2.mem.readLE (s.sp.toNat - 32) 8 = s.sp.toNat - 48 := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; decide)
  have hk_t02 : S2.mem.readLE (s.sp.toNat - 24) 8 = (j1 0).toNat := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; decide)
  have hk_t12 : S2.mem.readLE (s.sp.toNat - 16) 8 = (j1 1).toNat := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; decide)
  have hrlr2 : S2.mem.readLE (s.sp.toNat - 64) 8 = ret := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hrlr1
  have hrfp2 : S2.mem.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat := by
    rw [hS2]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hrfp1
  refine ReachesRet.call hat hS2pc ⟨PanicPre.of_within hc hS2fW (hl.env_frame _ _ henv1 hagS2) (by omega) (by omega)
      (by rw [hS2spn]; omega) hS228 (by rw [hS230]; decide) (by rw [hS230]; decide),
    by rw [hgS2, hl.room_frame _ _ _ hagS2]; omega, ?_⟩ ?_
  · rw [hgS2, hl.defers_frame _ _ _ hagS2, hd1]
    exact ⟨_, _, rfl, by rw [hS22]⟩
  intro s2 hpc2 hq2
  obtain ⟨⟨j2, f2, v2, m2, ex2, ep2, hs2, hfr2, henv2⟩, hdef2, hpan2, hsav2, hrp2, hroom2⟩ := hq2
  have hm2 : s2.mem = m2 := by rw [hs2]; rfl
  have hfr2e : MemFrame S2.mem m2 (P.priv ++ calleeStack S2 P.depth 2 ++ []) := by simpa using hfr2
  have hS20n : (S2.regs 0).toNat = fvA := by rw [hS20]; simp
  have hd2 : P.defers m2 (gOf s) = { sp := s.sp.toNat - 64, fns := [fvA], token := some (j1 1).toNat } ::
      P.defers s.mem (gOf s) := by
    have hh := hdef2 { sp := s.sp.toNat - 64, fns := [], token := some (j1 1).toNat } (P.defers s.mem (gOf s)) (by
      rw [hgS2, hl.defers_frame _ _ _ hagS2]; exact hd1)
    rw [hm2, hgS2, hS20n] at hh
    exact hh
  have hsv2 : P.saved m2 (gOf s) = none := by
    have := hsav2; rw [hm2, hgS2, hl.saved_frame _ _ _ hagS2] at this; rw [this]; exact hsv1
  have hpn2 : P.panics m2 (gOf s) = P.panics s.mem (gOf s) := by
    have := hpan2; rw [hm2, hgS2, hl.panics_frame _ _ _ hagS2] at this; rw [this]; exact hpn1
  have hrm2 : P.room s.mem (gOf s) ≤ P.room m2 (gOf s) + 2 := by
    have := hroom2; rw [hm2, hgS2, hl.room_frame _ _ _ hagS2] at this; omega
  have hW2 := hstep S2 m2 [] 2 hS2fW (by omega) (by omega) (fun a n h => by simp only [outside_nil]) hfr2e
  have hwin2 : m2.accessible (s.sp.toNat - (P.depth + 160)) (P.depth + 160 + 0) true = true := by
    rw [hW2.accessible]; exact hst
  have hk_bst3 : m2.readLE (s.sp.toNat - 112) 8 = s.sp.toNat - 48 := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_bst2
  have hk_bfp3 : m2.readLE (s.sp.toNat - 168) 8 = s.sp.toNat - 104 := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_bfp2
  have hk_blr3 : m2.readLE (s.sp.toNat - 160) 8 = loc_count2_44 := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_blr2
  have hk_c03 : m2.readLE (s.sp.toNat - 56) 8 = s.sp.toNat - 40 := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_c02
  have hk_clr3 : m2.readLE (s.sp.toNat - 96) 8 = loc_RangeDefer_72 := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_clr2
  have hk_cfp3 : m2.readLE (s.sp.toNat - 104) 8 = s.sp.toNat - 72 := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_cfp2
  have hk_code3 : m2.readLE (s.sp.toNat - 40) 8 = loc_RangeDefer_range1_0 := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_code2
  have hk_cst3 : m2.readLE (s.sp.toNat - 32) 8 = s.sp.toNat - 48 := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_cst2
  have hk_t03 : m2.readLE (s.sp.toNat - 24) 8 = (j1 0).toNat := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_t02
  have hk_t13 : m2.readLE (s.sp.toNat - 16) 8 = (j1 1).toNat := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_t12
  have hk_rlr3 : m2.readLE (s.sp.toNat - 64) 8 = ret := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hrlr2
  have hk_rfp3 : m2.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat := by
    rw [keep8 hfr2e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hrfp2
  clear hdef2 hpan2 hsav2 hrp2 hroom2 hS2f hS2fW hagS2 hS20 hS228 hS218 hS230 hS2pc hgS2 hS2sp hS2spn hS20n hm2 hpc2 hd1 hrm1 hsv1 hpn1 hW1 henv1 hfr2 hfr2e hS22
  subst hs2
  subst hS2
  janus_run [hk_bst3] until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine ReachesRet.name fun S3 hS3 => ?_
  have hS3sp : S3.sp = s.sp - 160#64 := by rw [hS3] <;> rfl
  have hS3spn : S3.sp.toNat = s.sp.toNat - 160 := by rw [hS3sp]; exact h160
  have hS3f : MemFrame m2 S3.mem [(s.sp.toNat - (P.depth + 160), s.sp.toNat)] := by rw [hS3]; janus_frame
  have hS328 : S3.regs 28 = s.regs 28 := by rw [hS3] <;> rfl
  have hS318 : S3.regs 18 = s.regs 18 := by rw [hS3] <;> rfl
  have hS330 : S3.regs 30 = BitVec.ofNat 64 loc_RangeDefer_range1_120 := by rw [hS3] <;> rfl
  have hS329 : S3.regs 29 = s.sp - 168#64 := by rw [hS3] <;> rfl
  have hS3pc : S3.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by rw [hS3] <;> rfl
  have hgS3 : gOf S3 = gOf s := by simp only [gOf, hS328]
  have hS3fW : MemFrame s.mem S3.mem (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) :=
    hW2.trans hS3f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagS3 : Map.Agrees m2 S3.mem P.priv :=
    Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 160)) (hi := s.sp.toNat) hS3f
      (Outside.of_sub hout (by omega) (by omega))
  have hpre3 : PanicPre P 0 S3 := PanicPre.of_within hc hS3fW (hl.env_frame _ _ henv2 hagS3) (by omega) (by omega)
    (by rw [hS3spn]; omega) hS328 (by rw [hS330]; decide) (by rw [hS330]; decide)
  have hsv3 : P.saved S3.mem (gOf S3) = none := by rw [hgS3, hl.saved_frame _ _ _ hagS3]; exact hsv2
  have hdf3 : P.defers S3.mem (gOf S3) = { sp := s.sp.toNat - 64, fns := [fvA], token := some (j1 1).toNat } ::
      P.defers s.mem (gOf s) := by rw [hgS3, hl.defers_frame _ _ _ hagS3]; exact hd2
  have hF3 : retFrame P S3 = ⟨s.sp.toNat - 160, s.sp.toNat - 160, 0, none⟩ := by
    simp only [retFrame, hsv3, hS3spn]
  have hds3 : ∀ d ∈ P.defers S3.mem (gOf S3), s.sp.toNat - 160 < d.sp := by
    intro d hd; rw [hdf3] at hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · dsimp only; omega
    · have := hdss d hd; omega
  have hI3 : frameItems S3.mem (retFrame P S3) (P.defers S3.mem (gOf S3)) = [] := by
    rw [hF3]; simp only [frameItems, List.nil_append, recItems_above hds3]
  have hE3 := hdr S3 hS3pc ⟨hpre3, by rw [hI3, hF3]; exact ⟨trivial, fun it h => absurd h (by simp)⟩⟩
  rw [hI3, hF3] at hE3
  rw [Engine_nil] at hE3
  refine ReachesRet.of_steps' hE3 ?_
  rintro d ⟨hdpc, hdsp, hd28, hd18, hd29, hdfr, hdenv, hdpan, hddef, hdsv, hdrp, hdrm⟩
  obtain ⟨dr, dsp, dpc, dfl, dm, ddz, dv, dtp, dfc, dfs⟩ := d
  dsimp only at hdpc hdsp hd28 hd18 hd29 hdfr hdenv hdpan hddef hdsv hdrp hdrm
  rw [hF3] at hdfr
  simp only [rtWin, bitsWin, List.append_nil] at hdfr
  have hdm8 : ∀ a, Outside a 8 P.priv → (a + 8 ≤ s.sp.toNat - 160 - P.depth ∨ s.sp.toNat - 168 ≤ a) →
      (a + 8 ≤ s.sp.toNat - 113 ∨ s.sp.toNat - 112 ≤ a) → (a + 8 ≤ s.sp.toNat - 48 ∨ s.sp.toNat - 40 ≤ a) →
      dm.readLE a 8 = m2.readLE a 8 := by
    intro a h1 h2 h3 h4
    rw [hdfr.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h1, by omega⟩)]
    rw [hS3]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
  have hdstate : dm.readLE (s.sp.toNat - 48) 8 = 1 := by
    rw [hdfr.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩)]
    rw [hS3]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  have hdbyte : dm.readLE (s.sp.toNat - 113) 1 = 1 := by
    rw [hdfr.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩)]
    rw [hS3]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  have hWd : MemFrame s.mem dm (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) :=
    hS3fW.trans hdfr fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega⟩⟩
  have hbfp4 : dm.readLE (s.sp.toNat - 168) 8 = s.sp.toNat - 104 := by
    rw [hdm8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_bfp3
  have hblr4 : dm.readLE (s.sp.toNat - 160) 8 = loc_count2_44 := by
    rw [hdm8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_blr3
  have hc04 : dm.readLE (s.sp.toNat - 56) 8 = s.sp.toNat - 40 := by
    rw [hdm8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_c03
  have hcode4 : dm.readLE (s.sp.toNat - 40) 8 = loc_RangeDefer_range1_0 := by
    rw [hdm8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_code3
  have hcst4 : dm.readLE (s.sp.toNat - 32) 8 = s.sp.toNat - 48 := by
    rw [hdm8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_cst3
  have ht04 : dm.readLE (s.sp.toNat - 24) 8 = (j1 0).toNat := by
    rw [hdm8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_t03
  have ht14 : dm.readLE (s.sp.toNat - 16) 8 = (j1 1).toNat := by
    rw [hdm8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_t13
  have hclr4 : dm.readLE (s.sp.toNat - 96) 8 = loc_RangeDefer_72 := by
    rw [hdm8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_clr3
  have hcfp4 : dm.readLE (s.sp.toNat - 104) 8 = s.sp.toNat - 72 := by
    rw [hdm8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_cfp3
  have hrlr4 : dm.readLE (s.sp.toNat - 64) 8 = ret := by
    rw [hdm8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_rlr3
  have hrfp4 : dm.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat := by
    rw [hdm8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_rfp3
  have hgv4 : dm.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hWd.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hgo, by omega⟩)]
  have hga4 : dm.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hWd.accessible]; exact hg2
  have hwin4 : dm.accessible (s.sp.toNat - (P.depth + 160)) (P.depth + 160 + 0) true = true := by
    rw [hWd.accessible]; exact hst
  rw [hS330] at hdpc
  rw [hS3sp] at hdsp
  subst hdpc hdsp
  have h160' : BitVec.ofNat 64 (s.sp.toNat - 160) = s.sp - 160#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hdr' : dr = setReg (setReg (setReg dr 18 (s.regs 18)) 28 (s.regs 28)) 29 (s.sp - 168#64) := by
    funext i; simp only [setReg]
    by_cases h29 : i = 29
    · rw [if_pos h29, h29]; rw [hd29, hS329]
    · rw [if_neg h29]
      by_cases h28 : i = 28
      · rw [if_pos h28, h28, hd28, hS328]
      · rw [if_neg h28]
        by_cases h18 : i = 18
        · rw [if_pos h18, h18, hd18, hS318]
        · rw [if_neg h18]
  have hrmD : P.room s.mem (gOf s) ≤ P.room dm (gOf s) + 2 := by
    have h1 := hdrm
    rw [hgS3, hl.room_frame _ _ _ hagS3] at h1
    omega
  have hsvD : P.saved dm (gOf s) = none := by
    have h1 := hdsv; rw [hgS3] at h1; exact h1
  have hpnD : P.panics dm (gOf s) = P.panics s.mem (gOf s) := by
    have h1 := hdpan
    rw [hgS3, hl.panics_frame _ _ _ hagS3] at h1
    rw [h1, hpn2]
  rw [hdr']
  clear hdfr hdm8 hS3fW hS3f hagS3 hW2
  have hcst4' : dm.readLE (s.sp.toNat - 40 + 8) 8 = s.sp.toNat - 48 := by
    rw [show s.sp.toNat - 40 + 8 = s.sp.toNat - 32 by omega]; exact hcst4
  have ht04' : dm.readLE (s.sp.toNat - 40 + 16) 8 = (j1 0).toNat := by
    rw [show s.sp.toNat - 40 + 16 = s.sp.toNat - 24 by omega]; exact ht04
  have ht14' : dm.readLE (s.sp.toNat - 40 + 24) 8 = (j1 1).toNat := by
    rw [show s.sp.toNat - 40 + 24 = s.sp.toNat - 16 by omega]; exact ht14
  janus_run [hdbyte, hbfp4, hblr4, hc04, hcode4, hcst4, ht04, ht14, hdstate, hcst4', ht04', ht14'] until [Extracted.program.contractAddr "runtime.deferprocat"]
  refine ReachesRet.name fun S4 hS4 => ?_
  have hS4sp : S4.sp = s.sp - 160#64 := by rw [hS4] <;> rfl
  have hS4spn : S4.sp.toNat = s.sp.toNat - 160 := by rw [hS4sp]; exact h160
  have hS4f : MemFrame dm S4.mem [(s.sp.toNat - (P.depth + 160), s.sp.toNat)] := by rw [hS4]; janus_frame
  have hS428 : S4.regs 28 = s.regs 28 := by rw [hS4] <;> rfl
  have hS418 : S4.regs 18 = s.regs 18 := by rw [hS4] <;> rfl
  have hS430 : S4.regs 30 = BitVec.ofNat 64 loc_RangeDefer_range1_96 := by rw [hS4] <;> rfl
  have hS40 : S4.regs 0 = BitVec.ofNat 64 (fvA + 8) := by rw [hS4] <;> rfl
  have hS42 : S4.regs 2 = j1 1 := by rw [hS4] <;> simp [setReg]
  have hS4pc : S4.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferprocat") := by rw [hS4] <;> rfl
  have hgS4 : gOf S4 = gOf s := by simp only [gOf, hS428]
  have hS4fW : MemFrame s.mem S4.mem (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) :=
    hWd.trans hS4f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagS4 : Map.Agrees dm S4.mem P.priv :=
    Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 160)) (hi := s.sp.toNat) hS4f
      (Outside.of_sub hout (by omega) (by omega))
  have hk_state5 : S4.mem.readLE (s.sp.toNat - 48) 8 = 2 := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (s.regs 29).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (by omega)) | (rw [h256]; decide)
  have hk_bst5 : S4.mem.readLE (s.sp.toNat - 112) 8 = s.sp.toNat - 48 := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (s.regs 29).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (by omega)) | (rw [h256]; decide)
  have hk_bfp5 : S4.mem.readLE (s.sp.toNat - 168) 8 = s.sp.toNat - 104 := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (s.regs 29).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (by omega)) | (rw [h256]; decide)
  have hk_blr5 : S4.mem.readLE (s.sp.toNat - 160) 8 = loc_count2_64 := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    all_goals first | (rw [h256]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 0).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (j1 1).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (s.regs 29).isLt) | (rw [h256]; exact Nat.mod_eq_of_lt (by omega)) | (rw [h256]; decide)
  have hk_c05 : S4.mem.readLE (s.sp.toNat - 56) 8 = s.sp.toNat - 40 := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hc04
  have hk_clr5 : S4.mem.readLE (s.sp.toNat - 96) 8 = loc_RangeDefer_72 := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hclr4
  have hk_cfp5 : S4.mem.readLE (s.sp.toNat - 104) 8 = s.sp.toNat - 72 := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hcfp4
  have hk_code5 : S4.mem.readLE (s.sp.toNat - 40) 8 = loc_RangeDefer_range1_0 := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hcode4
  have hk_cst5 : S4.mem.readLE (s.sp.toNat - 32) 8 = s.sp.toNat - 48 := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hcst4
  have hk_t05 : S4.mem.readLE (s.sp.toNat - 24) 8 = (j1 0).toNat := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact ht04
  have hk_t15 : S4.mem.readLE (s.sp.toNat - 16) 8 = (j1 1).toNat := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact ht14
  have hk_rlr5 : S4.mem.readLE (s.sp.toNat - 64) 8 = ret := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hrlr4
  have hk_rfp5 : S4.mem.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat := by
    rw [hS4]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hrfp4
  have hdd : P.defers dm (gOf s) = { sp := s.sp.toNat - 64, fns := [fvA], token := some (j1 1).toNat } ::
      P.defers s.mem (gOf s) := by
    have h1 := hddef
    rw [hS3spn, (frameRecs_above hds3).2, hdf3, hgS3] at h1
    exact h1
  refine ReachesRet.call hat hS4pc ⟨PanicPre.of_within hc hS4fW (hl.env_frame _ _ hdenv hagS4) (by omega) (by omega)
      (by rw [hS4spn]; omega) hS428 (by rw [hS430]; decide) (by rw [hS430]; decide),
    by rw [hgS4, hl.room_frame _ _ _ hagS4]; omega, ?_⟩ ?_
  · rw [hgS4, hl.defers_frame _ _ _ hagS4, hdd]
    exact ⟨_, _, rfl, by rw [hS42]⟩
  intro s4 hpc4 hq4
  obtain ⟨⟨j4, f4, v4, m4, ex4, ep4, hs4, hfr4, henv4⟩, hdef4, hpan4, hsav4, hrp4, hroom4⟩ := hq4
  have hm4 : s4.mem = m4 := by rw [hs4]; rfl
  have hfr4e : MemFrame S4.mem m4 (P.priv ++ calleeStack S4 P.depth 2 ++ []) := by simpa using hfr4
  have hS40n : (S4.regs 0).toNat = fvA + 8 := by rw [hS40]; simp
  have hd4 : P.defers m4 (gOf s) = { sp := s.sp.toNat - 64, fns := [fvA + 8, fvA], token := some (j1 1).toNat } ::
      P.defers s.mem (gOf s) := by
    have hh := hdef4 { sp := s.sp.toNat - 64, fns := [fvA], token := some (j1 1).toNat } (P.defers s.mem (gOf s)) (by
      rw [hgS4, hl.defers_frame _ _ _ hagS4]; exact hdd)
    rw [hm4, hgS4, hS40n] at hh
    exact hh
  have hsv4 : P.saved m4 (gOf s) = none := by
    have := hsav4; rw [hm4, hgS4, hl.saved_frame _ _ _ hagS4] at this; rw [this]; exact hsvD
  have hpn4 : P.panics m4 (gOf s) = P.panics s.mem (gOf s) := by
    have := hpan4; rw [hm4, hgS4, hl.panics_frame _ _ _ hagS4] at this; rw [this]; exact hpnD
  have hrm4 : P.room s.mem (gOf s) ≤ P.room m4 (gOf s) + 3 := by
    have := hroom4; rw [hm4, hgS4, hl.room_frame _ _ _ hagS4] at this; omega
  have hW4 := hstep S4 m4 [] 2 hS4fW (by omega) (by omega) (fun a n h => by simp only [outside_nil]) hfr4e
  have hwin6 : m4.accessible (s.sp.toNat - (P.depth + 160)) (P.depth + 160 + 0) true = true := by
    rw [hW4.accessible]; exact hst
  have hk_bst6 : m4.readLE (s.sp.toNat - 112) 8 = s.sp.toNat - 48 := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_bst5
  have hk_bfp6 : m4.readLE (s.sp.toNat - 168) 8 = s.sp.toNat - 104 := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_bfp5
  have hk_blr6 : m4.readLE (s.sp.toNat - 160) 8 = loc_count2_64 := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_blr5
  have hk_c06 : m4.readLE (s.sp.toNat - 56) 8 = s.sp.toNat - 40 := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_c05
  have hk_clr6 : m4.readLE (s.sp.toNat - 96) 8 = loc_RangeDefer_72 := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_clr5
  have hk_cfp6 : m4.readLE (s.sp.toNat - 104) 8 = s.sp.toNat - 72 := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_cfp5
  have hk_code6 : m4.readLE (s.sp.toNat - 40) 8 = loc_RangeDefer_range1_0 := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_code5
  have hk_cst6 : m4.readLE (s.sp.toNat - 32) 8 = s.sp.toNat - 48 := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_cst5
  have hk_t06 : m4.readLE (s.sp.toNat - 24) 8 = (j1 0).toNat := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_t05
  have hk_t16 : m4.readLE (s.sp.toNat - 16) 8 = (j1 1).toNat := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_t15
  have hk_rlr6 : m4.readLE (s.sp.toNat - 64) 8 = ret := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_rlr5
  have hk_rfp6 : m4.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat := by
    rw [keep8 hfr4e (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by simp only [outside_nil])]
    exact hk_rfp5
  clear hdef4 hpan4 hsav4 hrp4 hroom4 hS4f hS4fW hagS4 hS40 hS428 hS418 hS430 hS4pc hgS4 hS4sp hS4spn hS40n hm4 hpc4 hfr4 hfr4e hS42 hdd hrmD hsvD hpnD hWd hbfp4 hblr4 hc04 hcode4 hcst4 ht04 ht14 hcst4' ht04' ht14' hdstate hdbyte hclr4 hcfp4 hrlr4 hrfp4 hgv4 hga4 hwin4 hk_state5 hk_bst5 hk_bfp5 hk_blr5 hk_c05 hk_clr5 hk_cfp5 hk_code5 hk_cst5 hk_t05 hk_t15 hk_rlr5 hk_rfp5
  subst hs4
  subst hS4
  janus_run [hk_bst6] until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine ReachesRet.name fun S5 hS5 => ?_
  have hS5sp : S5.sp = s.sp - 160#64 := by rw [hS5] <;> rfl
  have hS5spn : S5.sp.toNat = s.sp.toNat - 160 := by rw [hS5sp]; exact h160
  have hS5f : MemFrame m4 S5.mem [(s.sp.toNat - (P.depth + 160), s.sp.toNat)] := by rw [hS5]; janus_frame
  have hS528 : S5.regs 28 = s.regs 28 := by rw [hS5] <;> rfl
  have hS518 : S5.regs 18 = s.regs 18 := by rw [hS5] <;> rfl
  have hS530 : S5.regs 30 = BitVec.ofNat 64 loc_RangeDefer_range1_120 := by rw [hS5] <;> rfl
  have hS529 : S5.regs 29 = s.sp - 168#64 := by rw [hS5] <;> rfl
  have hS5pc : S5.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by rw [hS5] <;> rfl
  have hgS5 : gOf S5 = gOf s := by simp only [gOf, hS528]
  have hS5fW : MemFrame s.mem S5.mem (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) :=
    hW4.trans hS5f fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  have hagS5 : Map.Agrees m4 S5.mem P.priv :=
    Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 160)) (hi := s.sp.toNat) hS5f
      (Outside.of_sub hout (by omega) (by omega))
  have hpre5 : PanicPre P 0 S5 := PanicPre.of_within hc hS5fW (hl.env_frame _ _ henv4 hagS5) (by omega) (by omega)
    (by rw [hS5spn]; omega) hS528 (by rw [hS530]; decide) (by rw [hS530]; decide)
  have hsv5 : P.saved S5.mem (gOf S5) = none := by rw [hgS5, hl.saved_frame _ _ _ hagS5]; exact hsv4
  have hdf5 : P.defers S5.mem (gOf S5) =
      { sp := s.sp.toNat - 64, fns := [fvA + 8, fvA], token := some (j1 1).toNat } ::
      P.defers s.mem (gOf s) := by rw [hgS5, hl.defers_frame _ _ _ hagS5]; exact hd4
  have hF5 : retFrame P S5 = ⟨s.sp.toNat - 160, s.sp.toNat - 160, 0, none⟩ := by
    simp only [retFrame, hsv5, hS5spn]
  have hds5 : ∀ d ∈ P.defers S5.mem (gOf S5), s.sp.toNat - 160 < d.sp := by
    intro d hd; rw [hdf5] at hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · dsimp only; omega
    · have := hdss d hd; omega
  have hI5 : frameItems S5.mem (retFrame P S5) (P.defers S5.mem (gOf S5)) = [] := by
    rw [hF5]; simp only [frameItems, List.nil_append, recItems_above hds5]
  have hE5 := hdr S5 hS5pc ⟨hpre5, by rw [hI5, hF5]; exact ⟨trivial, fun it h => absurd h (by simp)⟩⟩
  rw [hI5, hF5] at hE5
  rw [Engine_nil] at hE5
  refine ReachesRet.of_steps' hE5 ?_
  rintro e ⟨hepc, hesp, he28, he18, he29, hefr, heenv, hepan, heddef, hesv, herp, herm⟩
  obtain ⟨er, esp, epc, efl, em, edz, ev, etp, efc, efs⟩ := e
  dsimp only at hepc hesp he28 he18 he29 hefr heenv hepan heddef hesv herp herm
  rw [hF5] at hefr
  simp only [rtWin, bitsWin, List.append_nil] at hefr
  have hem8 : ∀ a, Outside a 8 P.priv → (a + 8 ≤ s.sp.toNat - 160 - P.depth ∨ s.sp.toNat - 168 ≤ a) →
      (a + 8 ≤ s.sp.toNat - 113 ∨ s.sp.toNat - 112 ≤ a) → (a + 8 ≤ s.sp.toNat - 48 ∨ s.sp.toNat - 40 ≤ a) →
      em.readLE a 8 = m4.readLE a 8 := by
    intro a h1 h2 h3 h4
    rw [hefr.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h1, by omega⟩)]
    rw [hS5]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
  have hestate : em.readLE (s.sp.toNat - 48) 8 = 1 := by
    rw [hefr.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩)]
    rw [hS5]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  have hebyte : em.readLE (s.sp.toNat - 113) 1 = 1 := by
    rw [hefr.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩)]
    rw [hS5]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  have hWe : MemFrame s.mem em (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) :=
    hS5fW.trans hefr fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, by omega⟩⟩
  have hbfp7 : em.readLE (s.sp.toNat - 168) 8 = s.sp.toNat - 104 := by
    rw [hem8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_bfp6
  have hblr7 : em.readLE (s.sp.toNat - 160) 8 = loc_count2_64 := by
    rw [hem8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_blr6
  have hclr7 : em.readLE (s.sp.toNat - 96) 8 = loc_RangeDefer_72 := by
    rw [hem8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_clr6
  have hcfp7 : em.readLE (s.sp.toNat - 104) 8 = s.sp.toNat - 72 := by
    rw [hem8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_cfp6
  have hrlr7 : em.readLE (s.sp.toNat - 64) 8 = ret := by
    rw [hem8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_rlr6
  have hrfp7 : em.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat := by
    rw [hem8 _ (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega) (by omega)]; exact hk_rfp6
  have hgv7 : em.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hWe.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hgo, by omega⟩)]
  have hga7 : em.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hWe.accessible]; exact hg2
  have hwin7 : em.accessible (s.sp.toNat - (P.depth + 160)) (P.depth + 160 + 0) true = true := by
    rw [hWe.accessible]; exact hst
  rw [hS530] at hepc
  rw [hS5sp] at hesp
  subst hepc hesp
  have her' : er = setReg (setReg (setReg er 18 (s.regs 18)) 28 (s.regs 28)) 29 (s.sp - 168#64) := by
    funext i; simp only [setReg]
    by_cases h29 : i = 29
    · rw [if_pos h29, h29]; rw [he29, hS529]
    · rw [if_neg h29]
      by_cases h28 : i = 28
      · rw [if_pos h28, h28, he28, hS528]
      · rw [if_neg h28]
        by_cases h18 : i = 18
        · rw [if_pos h18, h18, he18, hS518]
        · rw [if_neg h18]
  have hrmE : P.room s.mem (gOf s) ≤ P.room em (gOf s) + 3 := by
    have h1 := herm
    rw [hgS5, hl.room_frame _ _ _ hagS5] at h1
    omega
  have hsvE : P.saved em (gOf s) = none := by
    have h1 := hesv; rw [hgS5] at h1; exact h1
  have hpnE : P.panics em (gOf s) = P.panics s.mem (gOf s) := by
    have h1 := hepan
    rw [hgS5, hl.panics_frame _ _ _ hagS5] at h1
    rw [h1, hpn4]
  have hdE : P.defers em (gOf s) = { sp := s.sp.toNat - 64, fns := [fvA + 8, fvA], token := some (j1 1).toNat } ::
      P.defers s.mem (gOf s) := by
    have h1 := heddef
    rw [hS5spn, (frameRecs_above hds5).2, hdf5, hgS5] at h1
    exact h1
  rw [her']
  clear hefr hem8 hS5fW hS5f hagS5 hW4
  janus_run [hebyte, hbfp7, hblr7, hclr7, hcfp7, hestate] until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine ReachesRet.name fun S6 hS6 => ?_
  refine ReachesRet.done (by rw [hS6] <;> rfl) ?_
  have hF6sp : S6.sp = s.sp - 64#64 := by rw [hS6]
  have hF6spn : S6.sp.toNat = s.sp.toNat - 64 := by rw [hF6sp]; exact h64'
  have hF6f : MemFrame em S6.mem [(s.sp.toNat - 48, s.sp.toNat - 48 + 8)] := by rw [hS6]; janus_frame
  have hF628 : S6.regs 28 = s.regs 28 := by rw [hS6]; simp [setReg]
  have hF618 : S6.regs 18 = s.regs 18 := by rw [hS6]; simp [setReg]
  have hF630 : S6.regs 30 = BitVec.ofNat 64 loc_RangeDefer_96 := by rw [hS6]; simp [setReg]
  have hF629 : S6.regs 29 = s.sp - 72#64 := by
    rw [hS6]; simp [setReg]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hF6pc : S6.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") := by rw [hS6] <;> rfl
  have hgD : gOf S6 = gOf s := by simp only [gOf, hF628]
  have hF6fW : MemFrame s.mem S6.mem (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) :=
    hWe.trans hF6f fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      omega⟩
  have hagD : Map.Agrees em S6.mem P.priv :=
    Map.Agrees.of_window (lo := s.sp.toNat - 48) (hi := s.sp.toNat - 48 + 8) hF6f
      (Outside.of_sub hout (by omega) (by omega))
  have hlr : (S6.regs 30).toNat % 4 = 0 ∧ (S6.regs 30).toNat < 2 ^ 48 := by rw [hF630]; decide
  have hpre : PanicPre P 0 S6 := PanicPre.of_within hc hF6fW (hl.env_frame _ _ heenv hagD) (by omega) (by omega)
    (by rw [hF6spn]; omega) hF628 hlr.1 hlr.2
  have hsvD : P.saved S6.mem (gOf S6) = none := by rw [hgD, hl.saved_frame _ _ _ hagD]; exact hsvE
  have hdD : P.defers S6.mem (gOf S6) = { sp := s.sp.toNat - 64, fns := [fvA + 8, fvA], token := some (j1 1).toNat } ::
      P.defers s.mem (gOf s) := by rw [hgD, hl.defers_frame _ _ _ hagD]; exact hdE
  have hF : retFrame P S6 = ⟨s.sp.toNat - 64, s.sp.toNat - 64, 0, none⟩ := by
    simp only [retFrame, hsvD, hF6spn]
  have hds' : ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat - 64 < d.sp := fun d hd => by have := hdss d hd; omega
  have hrA := recItems_above hds'
  have hI : frameItems S6.mem (retFrame P S6) (P.defers S6.mem (gOf S6)) =
      [{ fn := fvA + 8, bits := none, chain := { sp := s.sp.toNat - 64, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] := by
    rw [hF, hdD]
    simp [frameItems, recItems, fnItems, hrA]
  have hfo1 : Outside fvA 8 (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) :=
    Outside.of_sub hfo (by omega) (by omega)
  have hfo2 : Outside (fvA + 8) 8 (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) :=
    Outside.of_sub hfo (by omega) (by omega)
  have hfv1 : S6.mem.readLE fvA 8 = accAdd1A := by rw [hF6fW.readLE _ _ hfo1]; exact fv1_read _ hd
  have hfv2 : S6.mem.readLE (fvA + 8) 8 = accAdd2A := by rw [hF6fW.readLE _ _ hfo2]; exact fv2_read _ hd
  have hfa1 : S6.mem.accessible fvA 8 false = true := by
    rw [hF6fW.accessible]; exact Memory.accessible_mono _ (fv_acc _ hd) (by omega) (by omega)
  have hfa2 : S6.mem.accessible (fvA + 8) 8 false = true := by
    rw [hF6fW.accessible]; exact Memory.accessible_mono _ (fv_acc _ hd) (by omega) (by omega)
  have hFO : FrameOK P S6.mem (retFrame P S6) (frameItems S6.mem (retFrame P S6) (P.defers S6.mem (gOf S6))) := by
    rw [hI, hF]
    simp only [outside_append, outside_cons, outside_nil, and_true] at hfo
    refine ⟨trivial, fun it hit => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl <;> dsimp only
    · exact ⟨by omega, hfa2, by rw [hfv2] <;> decide, by rw [hfv2] <;> decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
    · exact ⟨by omega, hfa1, by rw [hfv1] <;> decide, by rw [hfv1] <;> decide, Outside.of_sub hfo.1 (by omega) (by omega), by omega⟩
  have hpaD : S6.mem.accessible accA 8 true = true := by rw [hF6fW.accessible]; exact hacc
  have hv0 : S6.mem.readLE accA 8 = s.mem.readLE accA 8 := hF6fW.readLE _ _ hao
  have hKp : frameKeep S6.mem ⟨s.sp.toNat - 64, s.sp.toNat - 64, 0, none⟩
      [{ fn := fvA + 8, bits := none, chain := { sp := s.sp.toNat - 64, fns := [fvA] } :: P.defers s.mem (gOf s) },
       { fn := fvA, bits := none, chain := P.defers s.mem (gOf s) }] =
      [(fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)] := by
    simp [frameKeep, Frame.openAt]
  have hoT : Outside accA 8 (P.priv ++ rtWin P ⟨s.sp.toNat - 64, s.sp.toNat - 64, 0, none⟩ ++
      bitsWin ⟨s.sp.toNat - 64, s.sp.toNat - 64, 0, none⟩) := by
    have hao' := hao
    simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at hao' ⊢
    exact ⟨hao'.1, by omega⟩
  have hsubR : ∀ a n, Outside a n (winB P s) →
      Outside a n (P.priv ++ rtWin P ⟨s.sp.toNat - 64, s.sp.toNat - 64, 0, none⟩ ++
        bitsWin ⟨s.sp.toNat - 64, s.sp.toNat - 64, 0, none⟩) := by
    intro a n h
    simp only [winB, rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true, List.append_nil] at h ⊢
    exact ⟨h.1, h.2.1⟩
  have hsubA : ∀ a n, Outside a n (winB P s) → Outside a n [(accA, accA + 8)] := by
    intro a n h
    simp only [winB, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact h.2.2
  have hoA : ∀ (e : State), P.depth ≥ 0 → (s.sp.toNat - 64 - P.depth ≤ e.sp.toNat) →
      Outside accA (accA + 8 - accA) (P.priv ++ (e.sp.toNat, s.sp.toNat - 64) ::
        [(fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) := by
    intro e _ hlo
    have hao' := hao
    simp only [outside_append, outside_cons, outside_nil, and_true] at hao' ⊢
    simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hao'.1, by omega, by omega, by omega⟩
  refine DeferreturnContract.apply (S := S6) hdr hF6pc ⟨hpre, hFO⟩ ?_
  intro hE
  rw [hI, hF] at hE
  rw [hKp] at hE
  -- the first deferred call (the later `deferprocat`): `Acc = Acc*10 + 2`
  rw [Engine_cons] at hE
  obtain ⟨k1, e1, hst1, ⟨hpc1, h26_1, h28_1, h18_1, h29_1, hal1, hlo1, hhi1, h30a1, h30b1, henvE1⟩,
    hfrE1, -, -, hpn1, -, -, hcont1, -⟩ := hE
  dsimp only at hpc1 h26_1 hlo1 hhi1 hfrE1 hcont1
  refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
  have hae1 : MemFrame S6.mem e1.mem (winB P s) := hfrE1.mono hsubR
  have hm1 : e1.mem.readLE (fvA + 8) 8 = accAdd2A := by
    rw [hae1.readLE _ _ (by
      have h2 := hfo2
      simp only [outside_append, outside_cons, outside_nil, and_true] at h2
      simp only [winB, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h2.1, by omega, by omega⟩)]
    exact hfv2
  have hv1 : e1.mem.readLE accA 8 = s.mem.readLE accA 8 := by
    rw [hfrE1.readLE _ _ hoT]; exact hv0
  rw [hm1] at hpc1
  have hpa1 : e1.mem.accessible accA 8 true = true := by rw [hae1.accessible]; exact hpaD
  have hcl1 := call_acc2 impl e1 hpc1 hpa1 h30a1 h30b1
  obtain ⟨j1, f1, hj1, -, hfpc1, hfsp1, hf281, hf181, hff1, hpv1⟩ := hcl1
  refine GoReturns.of_steps (hj1.withExit hret.fetch_none) ?_
  have hw1 : f1.mem.readLE accA 8 = digit 2 (s.mem.readLE accA 8) := by rw [hpv1, hv1]
  have hacc1 : MemFrame S6.mem f1.mem (winB P s) := hae1.trans hff1 fun a n h => ⟨h, hsubA a n h⟩
  obtain ⟨hdr1, hpf1⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 64)
    (keep := [(fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl hfpc1 hfsp1
    (hf281.trans h28_1) (hf181.trans h18_1) henvE1 hff1 (hoA e1 (Nat.zero_le _) (by omega))
  have hE1 := (hcont1 f1 hdr1).1 (hpf1.trans hpn1)
  rw [Engine_cons] at hE1
  obtain ⟨k2, e2, hst2, ⟨hpc2, h26_2, h28_2, h18_2, h29_2, hal2, hlo2, hhi2, h30a2, h30b2, henvE2⟩,
    hfrE2, -, -, hpn2, -, -, hcont2, -⟩ := hE1
  dsimp only at hpc2 h26_2 hlo2 hhi2 hfrE2 hcont2
  refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
  have hae2 : MemFrame S6.mem e2.mem (winB P s) := hacc1.trans hfrE2 fun a n h => ⟨h, hsubR a n h⟩
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
  have hcl2 := call_acc1 impl e2 hpc2 hpa2 h30a2 h30b2
  obtain ⟨j2, f2, hj2, -, hfpc2, hfsp2, hf282, hf182, hff2, hpv2⟩ := hcl2
  refine GoReturns.of_steps (hj2.withExit hret.fetch_none) ?_
  have hw2 : f2.mem.readLE accA 8 = digit 1 (digit 2 (s.mem.readLE accA 8)) := by rw [hpv2, hv2]
  have hacc2 : MemFrame S6.mem f2.mem (winB P s) := hae2.trans hff2 fun a n h => ⟨h, hsubA a n h⟩
  obtain ⟨hdr2, hpf2⟩ := DeferReturned.of_window (fsp := s.sp.toNat - 64)
    (keep := [(fvA + 8, fvA + 8 + 8), (fvA, fvA + 8)]) hl hfpc2 hfsp2
    (hf282.trans h28_2) (hf182.trans h18_2) henvE2 hff2 (hoA e2 (Nat.zero_le _) (by omega))
  have hE2 := (hcont2 f2 hdr2).1 (hpf2.trans hpn2)
  rw [Engine_nil] at hE2
  obtain ⟨k3, d, hst3, hdpc, hdsp, hd28, hd18, hd29, hdfr, hdenv, -⟩ := hE2
  refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
  rw [hF] at hdfr
  simp only [rtWin, bitsWin, List.append_nil] at hdfr
  obtain ⟨dr, dsp, dpc, dfl, dm, ddz, dv, dtp, dfc, dfs⟩ := d
  dsimp only at hdpc hdsp hd28 hd18 hd29 hdfr hdenv
  have hdl : dm.readLE (s.sp.toNat - 64) 8 = ret := by
    rw [hdfr.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩),
      hacc2.readLE _ _ (by
        simp only [winB, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    rw [hS6]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hrlr7
  have hdf8 : dm.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat := by
    rw [hdfr.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩),
      hacc2.readLE _ _ (by
        simp only [winB, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    rw [hS6]; simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hrfp7
  have hdA : dm.readLE accA 8 = mix (s.mem.readLE accA 8) := by
    have hoT' : Outside accA 8 (P.priv ++ [(s.sp.toNat - 64 - P.depth, s.sp.toNat - 64 - 8)]) := by
      have h1 := hoT
      simp only [rtWin, bitsWin, List.append_nil] at h1
      exact h1
    rw [hdfr.readLE _ _ hoT']; exact hw2
  rw [hF630] at hdpc
  rw [hF6sp] at hdsp
  subst hdpc hdsp
  have hdr' : dr = setReg (setReg dr 18 (s.regs 18)) 28 (s.regs 28) := by
    funext i; simp only [setReg]
    by_cases h28 : i = 28
    · rw [if_pos h28, h28, hd28, hF628]
    · rw [if_neg h28]
      by_cases h18 : i = 18
      · rw [if_pos h18, h18, hd18, hF618]
      · rw [if_neg h18]
  rw [hdr']
  refine GoReturns.of_reaches ?_
  janus_run [hdl, hdf8]
  exact hdA

/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSat` (code that
`Janus.Contracts.PanicSatRun` proves meets the three contracts in every program that contains it)
linked into `RangeDefer`'s program with a branch to it at each contract address, and a call state
satisfying the precondition: so `correctness` applies (`nonvacuous`), and `RangeDefer` returns
from that state (`returns`). -/

namespace Witness

open Janus.Contracts.PanicSat Janus.Contracts.PanicModel

abbrev T0 : List FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : PanicRuntime := P0 T0 RPa

def rfA : Nat := Extracted.program.contractAddr "runtime.deferrangefunc"
def paA : Nat := Extracted.program.contractAddr "runtime.deferprocat"
def drA : Nat := Extracted.program.contractAddr "runtime.deferreturn"

/-- The code linked next to `RangeDefer`: the model engine and a branch to it at each contract
address. -/
def implW : List Segment :=
  panicImpl Extracted.program [("runtime.deferrangefunc", eDeferrangefunc), ("runtime.deferprocat", eDeferprocat),
    ("runtime.deferreturn", eDeferreturn)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

theorem stubRf : StubAt (Extracted.program.link implW) rfA eDeferrangefunc :=
  StubAt.of_decode (w := stubWord rfA eDeferrangefunc) (imm := (eDeferrangefunc - rfA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem stubPa : StubAt (Extracted.program.link implW) paA eDeferprocat :=
  StubAt.of_decode (w := stubWord paA eDeferprocat) (imm := (eDeferprocat - paA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem stubDr : StubAt (Extracted.program.link implW) drA eDeferreturn :=
  StubAt.of_decode (w := stubWord drA eDeferreturn) (imm := (eDeferreturn - drA) / 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem hrf : DeferrangefuncContract (Extracted.program.link implW) rfA PW :=
  deferrangefunc_at stubRf (deferrangefunc_contract engineAt T0)

theorem hat : DeferprocatContract (Extracted.program.link implW) paA PW :=
  deferprocat_at stubPa (deferprocat_contract engineAt T0)

theorem hdr : DeferreturnContract (Extracted.program.link implW) drA PW U0 :=
  deferreturn_at stubDr (deferreturn_run engineAt)

/-- The witness memory, with `Acc` a writable word. -/
def wm : Memory :=
  ⟨(witMemD (tabWords T0) Extracted.data).bytes,
    (witMemD (tabWords T0) Extracted.data).regions ++ [⟨accA, 8, true⟩]⟩

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

set_option maxRecDepth 100000 in
theorem pre : PanicCallerOK PW s0 160 0 ∧ Extracted.program.DataLoaded s0.mem ∧
    s0.mem.accessible accA 8 true = true ∧
    Outside accA 8 (PW.priv ++ [(s0.sp.toNat - (PW.depth + 160), s0.sp.toNat)]) ∧
    Outside fvA 16 (PW.priv ++ [(s0.sp.toNat - (PW.depth + 160), s0.sp.toNat)]) ∧
    3 ≤ PW.room s0.mem (gOf s0) ∧ PW.saved s0.mem (gOf s0) = none ∧
    ∀ d ∈ PW.defers s0.mem (gOf s0), s0.sp.toNat ≤ d.sp := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_⟩, dataLoaded, by decide, ?_, ?_, ?_, ?_, ?_⟩
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
theorem nonvacuous : ∃ (impl : List Segment) (P : PanicRuntime) (U : State → Nat → Nat → Prop) (ret : Nat)
    (s : State), P.Laws ∧
    DeferrangefuncContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferrangefunc") P ∧
    DeferprocatContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferprocat") P ∧
    DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P U ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [] s ∧
    (PanicCallerOK P s 160 0 ∧ Extracted.program.DataLoaded s.mem ∧ s.mem.accessible accA 8 true = true ∧
      Outside accA 8 (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) ∧
      Outside fvA 16 (P.priv ++ [(s.sp.toNat - (P.depth + 160), s.sp.toNat)]) ∧
      3 ≤ P.room s.mem (gOf s) ∧ P.saved s.mem (gOf s) = none ∧
      ∀ d ∈ P.defers s.mem (gOf s), s.sp.toNat ≤ d.sp) :=
  ⟨implW, PW, U0, ret, s0, P0_laws T0 RPa, hrf, hat, hdr, hret, setup, pre⟩

/-- So the guarantee is reached: `RangeDefer` returns, having run its two deferred calls in LIFO
order. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClass PW) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ s'.mem.readLE accA 8 = mix (s0.mem.readLE accA 8)
    | .panicked _ _ => False
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U0 hrf hat hdr ret hret s0 setup pre

end Witness

end Proof
