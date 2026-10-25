import Extracted

/-!
# `BigLocal(x, i uint64) uint64`: a large frame, correct with stack growth (R7)

```go
func BigLocal(x, i uint64) uint64 {
	var buf [20]uint64
	buf[i&15] = x
	return buf[0]
}
```

`BigLocal` has a 176-byte frame (more than `abi.StackSmall = 128`), so its prologue
(`SUB $48, RSP, R17; CMP R16, R17; BLS morestack`) calls `runtime.morestack_noctxt` whenever the
goroutine's stack has fewer than `48 + stackGuard` free bytes below `SP` — in particular on
every small stack.

**Guarantee.** For every frame table `FT` (the binary's stack maps), every stack pool, every
runtime-owned memory `rt`, every readiness predicate `H` and every runtime that meets the
`morestack` contract (`MorestackContract`, `Janus/Contracts/Stack.lean`), and for every call
state whose goroutine stack `[lo, hi)` is described by `g.stack` — **with no assumption that the
frame fits** — the call returns (`GrownReturns`: after at most one stack growth) with
`X0 = x` if `i & 15 = 0` and `X0 = 0` otherwise. The precondition (`GPre`) states the goroutine
stack, the caller's walk (`Chain`, whose stack maps do not mark `BigLocal`'s argument slots),
the pools, the readiness and the `maxstacksize` bound; `TableOK` the table's entry for
`BigLocal` at the glue pc (no frame, largest frame 176 bytes, both arguments scalars).

**How.** `summary` is the roomy proof (`janus_run`). `correctness` splits on the prologue's
check: with room it is `summary`; without, `janus_run` runs the prologue to the `morestack`
stub, the contract moves the stack, `glue` re-enters `BigLocal`, and `summary` applies on the
new stack, which has room for the function's largest frame (`Grown.room`). The arguments survive
the move because `Moved` copies the words the stack maps call scalars (`Moved.readLE_scalar`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Stack Janus.Contracts
  Janus.Contracts.Stack

namespace Proof


/-- The roomy precondition (the prologue falls through): an admissible return address, the guard
48 bytes below `SP` (`176 - abi.StackSmall`), the 184-byte window `[SP - 184, SP)` writable (the
frame and the saved frame pointer below it), the guard word outside it, `X29 = SP - 8`. -/
abbrev Pre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧
  GuardOK s 48 ∧ StackOK s 184 0 ∧
  Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 184) 184 ∧ s.regs 29 = s.sp - 8

/-- **`BigLocal` on a stack with room**: it returns `buf[0]`, which is `x` when `i & 15 = 0` and
`0` otherwise (the 20-word array is zeroed first). -/
theorem summary : Summary Extracted.program Extracted.entry Pre
    (fun s s' => s'.regs 0 = (if (s.regs 1).toNat % 16 = 0 then s.regs 0 else 0)) := by
  intro s hpc ⟨h30a, h30, ⟨hg1,hg2,hg3⟩, ⟨hal,hb,ha,hw⟩, hd, hfp⟩
  simp only [Disjoint] at hd
  have hlt : (s.regs 1).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  by_cases hz : (s.regs 1).toNat % 16 = 0
  · janus_run <;> simp [hz]
  · janus_run <;> simp [hz]

/-- The glue after the `morestack` call (`LDP 8(RSP), (R0, R1); B BigLocal`): from any state
there it re-enters `BigLocal` with the spilled arguments reloaded. -/
theorem glue : ∀ t : State, t.pc = BitVec.ofNat 64 (Extracted.entry + 0x6c) →
    t.mem.accessible (t.sp.toNat + 8) 16 false = true → t.sp.toNat + 24 ≤ 2 ^ 48 →
    t.sp.toNat % 16 = 0 →
    ReachesRet Extracted.program (BitVec.ofNat 64 Extracted.entry) t (fun t' =>
      t'.pc = BitVec.ofNat 64 Extracted.entry ∧ t'.sp = t.sp ∧ t'.mem = t.mem ∧
      t'.regs 0 = BitVec.ofNat 64 (t.mem.readLE (t.sp.toNat + 8) 8) ∧
      t'.regs 1 = BitVec.ofNat 64 (t.mem.readLE (t.sp.toNat + 16) 8) ∧
      (∀ r, r ≠ 0 → r ≠ 1 → t'.regs r = t.regs r)) := by
  intro t hpc hacc hsp hal
  janus_run until [Extracted.entry]
  exact ReachesRet.done rfl ⟨rfl, rfl, rfl, by simp [setReg], by simp [setReg],
    fun r h0 h1 => by simp [setReg, h0, h1]⟩

/-- The glue pc after the `morestack` call (`LDP 8(RSP), (R0, R1)`). -/
abbrev gluePc : Nat := Extracted.entry + 108

/-- What the frame table (the pclntab) says about `BigLocal` at the glue pc. -/
def TableOK (FT : FrameTable) : Prop :=
  FT.valid gluePc = true ∧ FT.stop gluePc = false ∧ FT.injected gluePc = false ∧
  FT.spdelta gluePc = 0 ∧ FT.maxspd gluePc = 176 ∧ (FT.args gluePc).getD 0 false = false ∧
  (FT.args gluePc).getD 1 false = false ∧ FT.objs gluePc = []

/-- The grown precondition: the goroutine stack `[lo, hi)` (no room assumed). -/
def GPre (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s : State) : Prop :=
  ∃ lo hi, GStack s.mem (s.regs 28).toNat lo hi ∧ Outside (s.regs 28).toNat 24 pool ∧
    4096 ≤ lo ∧ lo + 8 ≤ s.sp.toNat ∧ s.sp.toNat + 24 ≤ hi ∧ hi ≤ 2 ^ 48 ∧
    lo % 16 = 0 ∧ hi % 16 = 0 ∧ s.sp.toNat % 16 = 0 ∧ s.regs 29 = s.sp - 8 ∧
    InRanges lo (hi - lo) pool ∧ PoolOK s.mem pool ∧ Outside lo (hi - lo) rt ∧
    (∃ fs, Chain Arch.arm64 FT s.mem hi (s.regs 30).toNat s.sp.toNat none fs ∧
      (∀ f ∈ fs, f.sp = s.sp.toNat ∨ s.sp.toNat + 24 ≤ f.sp) ∧
      framesCls Arch.arm64 FT fs (s.sp.toNat + 8) = false ∧
      framesCls Arch.arm64 FT fs (s.sp.toNat + 16) = false) ∧
    2 * (hi - lo) ≤ maxstacksize ∧ 2 * ((hi - s.sp.toNat) + 176 + stackGuard) ≤ maxstacksize ∧
    FT.CodeOutside pool ∧ FT.Aligned ∧ H [] (s.regs 28).toNat 0 (rtView rt s.mem)

/-- The growth path: from the prologue's `morestack` call, the contract resumes on a larger stack,
the glue reloads `x` and `i` from the moved spill slots (copied unchanged: the stack maps call
them scalars), and the stack now has room, so `summary` applies there. -/
theorem grow_branch (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract Extracted.program FT pool rt H reloc)
    (hFT : TableOK FT) (x i : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (g lo hi : Nat) (s_m : State) (hm : MorestackPre Extracted.program FT pool rt H g lo hi s_m)
    (hglue : s_m.regs 30 = BitVec.ofNat 64 gluePc) (hx3 : s_m.regs 3 = BitVec.ofNat 64 ret)
    (hspill : s_m.sp.toNat + 24 ≤ hi)
    (hsx : s_m.mem.readLE (s_m.sp.toNat + 8) 8 = x.toNat)
    (hsi : s_m.mem.readLE (s_m.sp.toNat + 16) 8 = i.toNat)
    (hcls : ∀ fs, Chain Arch.arm64 FT s_m.mem hi (s_m.regs 30).toNat s_m.sp.toNat
        (some (s_m.regs 3).toNat) fs →
      framesCls Arch.arm64 FT fs (s_m.sp.toNat + 8) = false ∧
      framesCls Arch.arm64 FT fs (s_m.sp.toNat + 16) = false) :
    ∃ s_r, reloc s_m s_r ∧ GrownReturns (Extracted.program.withExit ret) reloc s_r
      (fun s' => s'.regs 0 = if i.toNat % 16 = 0 then x else 0) := by
  obtain ⟨s_r, lo', hi', hre, hgr⟩ := hms g lo hi s_m hm
  refine ⟨s_r, hre, ?_⟩
  obtain ⟨hgr1, hgr2, h4k', hal1', hal2', hhi48', hinp', happ⟩ := hgr.grows
  have hroom := hgr.room
  have hgl : (s_m.regs 30).toNat = gluePc := by rw [hglue]; rfl
  have hmax : FT.maxspd (s_m.regs 30).toNat = 176 := by rw [hgl]; exact hFT.2.2.2.2.1
  rw [hmax] at hroom
  simp only [stackGuard] at hroom
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hm.low
  obtain ⟨ha1, ha2, ha3⟩ := hm.aligned
  have hret48 : ret < 2 ^ 48 := hret.user
  have hsp_r : s_r.sp.toNat = s_m.sp.toNat + hi' - hi := by
    rw [hgr.sp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hpok_r : PoolOK s_r.mem pool := hm.inPool.2.of_accessible hgr.frame.accessible
  have hacc_r : s_r.mem.accessible lo' (hi' - lo') true = true := hpok_r.accessible hinp'
  have hpc_r : s_r.pc = BitVec.ofNat 64 (Extracted.entry + 0x6c) := hgr.pc.trans hglue
  obtain ⟨k, t, hst, htpc, -, htsp, htmem, ht0, ht1, htr⟩ := glue s_r hpc_r
    (Memory.accessible_read_of_write _ (Memory.accessible_mono _ hacc_r (by omega) (by omega)))
    (by omega) (by omega)
  apply GrownReturns.of_steps (hst.withExit hret.fetch_none)
  apply GrownReturns.done
  obtain ⟨fs, hchm⟩ := hm.chain
  have hmv := hgr.moved fs hchm
  obtain ⟨hc8, hc16⟩ := hcls fs hchm
  have hrd : ∀ off, off = 8 ∨ off = 16 → framesCls Arch.arm64 FT fs (s_m.sp.toNat + off) = false →
      s_r.mem.readLE (s_r.sp.toNat + off) 8 = s_m.mem.readLE (s_m.sp.toNat + off) 8 := by
    intro off hoff hc
    rw [hsp_r, show s_m.sp.toNat + hi' - hi + off = (s_m.sp.toNat + off) + hi' - hi by omega]
    exact hmv.readLE_scalar (by omega) (by omega) (fun j hj => by
      rw [show s_m.sp.toNat + off + j - (s_m.sp.toNat + off + j) % 8 = s_m.sp.toNat + off by omega]
      simp only [moveCls, hc, Bool.or_false, decide_eq_false_iff_not]; omega) trivial
  have hg28 : t.regs 28 = s_m.regs 28 := (htr 28 (by decide) (by decide)).trans hgr.gkeep.1
  have hgreg := hm.greg
  obtain ⟨hgg24, hggacc, -, -, hggd⟩ := hgr.gstack
  simp only [gStackguard0, stackGuard] at hggd
  have hgout := hm.gout
  have hr30 : (t.regs 30).toNat = ret := by
    rw [htr 30 (by decide) (by decide), hgr.lr, hx3, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine Summary.returns summary hret htpc ((htr 30 (by decide) (by decide)).trans (hgr.lr.trans hx3))
    ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ ?_
  · rw [hr30]; exact hret.aligned
  · rw [hr30]; omega
  · rw [hg28, hgreg]; exact hgg24
  · rw [hg28, hgreg, htmem]; exact Memory.accessible_mono _ hggacc (by omega) (by omega)
  · rw [hg28, hgreg, htmem, hggd, htsp, hsp_r]; omega
  · rw [htsp, hsp_r]; omega
  · rw [htsp, hsp_r]; omega
  · rw [htsp, hsp_r]; omega
  · rw [htsp, hsp_r, htmem]; exact Memory.accessible_mono _ hacc_r (by omega) (by omega)
  · rw [hg28, hgreg, htsp, hsp_r]
    have := InRanges.disjoint (InRanges.sub hinp' (a := s_m.sp.toNat + hi' - hi - 184) (n := 184)
      (by omega) (by omega)) hgout
    simp only [Disjoint]; omega
  · rw [htr 29 (by decide) (by decide), hgr.regs 29 rfl, htsp, hgr.sp]
    have hfp := hm.fp
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hfp,
      show (8 : BitVec 64).toNat = 8 from rfl]
    omega
  · intro s' hs'
    show s'.regs 0 = _
    rw [hs', ht0, ht1, hrd 8 (.inl rfl) hc8, hrd 16 (.inr rfl) hc16, hsx, hsi,
      BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]

/-- **`BigLocal` is correct on a stack of any size, stack growth included.** -/
theorem correctness (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract Extracted.program FT pool rt H reloc)
    (hFT : TableOK FT) (x i : BitVec 64) :
    EnsuresGrow Extracted.program reloc Extracted.entry [x, i] (GPre FT pool rt H)
      (fun _ s' => s'.regs 0 = if i.toNat % 16 = 0 then x else 0) := by
  intro ret hret s hs hpre
  janus_intro hs
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hfp, hinp, hpok, hrt,
    ⟨fs, hch, hfsp, hc8, hc16⟩, hfit1, hfit2, hcode, hal, hH⟩ := hpre
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
  have hacc : s.mem.accessible lo (hi - lo) true = true := hpok.accessible hinp
  have hret48 : ret < 2 ^ 48 := hret.user
  have hlrn : (s.regs 30).toNat = ret := by
    rw [h_lr, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hdisj : ∀ a n, InRanges a n pool → Disjoint ((s.regs 28).toNat + 16) 8 a n := by
    intro a n hin
    have := InRanges.disjoint hin hgo
    simp only [Disjoint]; omega
  by_cases hroom : lo + 928 + 48 < s.sp.toNat
  · apply GrownReturns.done
    refine Summary.returns summary hret (by rw [h_pc]; rfl) h_lr ⟨?_, ?_, ⟨hg24, ?_, ?_⟩, ⟨hal3, ?_, ?_, ?_⟩, ?_, hfp⟩ ?_
    · rw [hlrn]; exact hret.aligned
    · rw [hlrn]; omega
    · exact Memory.accessible_mono _ hgacc (by omega) (by omega)
    · rw [hgg]; omega
    · omega
    · omega
    · exact Memory.accessible_mono _ hacc (by omega) (by omega)
    · exact hdisj _ _ (InRanges.sub hinp (by omega) (by omega))
    · intro s' hs'; show s'.regs 0 = _; rw [hs', h_x0, h_x1]
  · obtain ⟨hv, hst, hinj, hspd, hmx, ha0, ha1, hob⟩ := hFT
    -- the memory at the `morestack` call: the stub spilled `x` and `i`
    obtain ⟨mm, hmm⟩ : ∃ mm, mm = (s.mem.writeLE (s.sp.toNat + 8) 8 x.toNat).writeLE (s.sp.toNat + 16) 8 i.toNat :=
      ⟨_, rfl⟩
    have hgw : (s.regs 28).toNat + 24 ≤ s.sp.toNat + 8 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat := by
      have := InRanges.disjoint (InRanges.sub hinp (a := s.sp.toNat + 8) (n := 16) (by omega) (by omega)) hgo
      omega
    have hrdm : ∀ a n, a + n ≤ s.sp.toNat + 8 ∨ s.sp.toNat + 24 ≤ a → mm.readLE a n = s.mem.readLE a n := by
      intro a n h
      rw [hmm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have haccm : ∀ a n w, mm.accessible a n w = s.mem.accessible a n w := by
      intro a n w; rw [hmm, Memory.accessible_writeLE, Memory.accessible_writeLE]
    have hfp0 : Arch.arm64.fp FT gluePc s.sp.toNat = s.sp.toNat := by simp [Arch.fp, hspd]
    have hcm : Chain Arch.arm64 FT mm hi ret s.sp.toNat none fs := by
      rw [← hlrn]
      refine Chain.congr hch (by omega) fun f hf _ => hrdm _ _ ?_
      simp only [Arch.lrSlot]; rcases hfsp f hf with h | h <;> omega
    have hchain : Chain Arch.arm64 FT mm hi gluePc s.sp.toNat (some ret)
        (⟨gluePc, s.sp.toNat, Arch.arm64.fp FT gluePc s.sp.toNat⟩ :: fs) := by
      refine .cons hv hst hinj (by omega) (by rw [hfp0]; omega) ?_
      rw [hfp0]; simpa [Arch.lrOf] using hcm
    have hf0 : ∀ off, off = 8 ∨ off = 16 →
        frameCls Arch.arm64 FT gluePc s.sp.toNat s.sp.toNat (s.sp.toNat + off) = false := by
      intro off hoff
      have hv0 : Arch.arm64.varp s.sp.toNat s.sp.toNat = s.sp.toNat := by simp [Arch.varp]
      simp only [frameCls, hv0, Arch.argp, Arch.minLocals, hob, List.any_nil, Bool.or_false]
      have e1 : decide (s.sp.toNat + 8 = s.sp.toNat + 16) = false := by simp
      have e2 : decide (16 + s.sp.toNat < s.sp.toNat) = false := by simp
      rw [e1, e2, Bool.false_and, Bool.false_and, Bool.false_or, Bool.false_or]
      simp only [bitsAt]
      rcases hoff with rfl | rfl
      · rw [show ((s.sp.toNat + 8 : Nat) : Int) - ((s.sp.toNat + 8 : Nat) : Int) = 0 by omega]; simpa using ha0
      · rw [show ((s.sp.toNat + 16 : Nat) : Int) - ((s.sp.toNat + 8 : Nat) : Int) = 8 by omega]; simpa using ha1
    apply GrownReturns.of_reaches_stub
    janus_run
    rw [← hmm]
    refine grow_branch FT pool rt H reloc hms ⟨hv, hst, hinj, hspd, hmx, ha0, ha1, hob⟩ x i ret hret
      (s.regs 28).toNat lo hi _ ⟨?_, ?_, ?_, hgo, ?_, ⟨hal1, hal2, hal3⟩, ?_, ⟨hinp, hpok.of_accessible haccm⟩,
        ?_, ?_, ⟨hcode, hal⟩, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_
    · exact ⟨_, rfl⟩
    · simp [setReg, regG]
    · refine ⟨hg24, by rw [haccm]; exact hgacc, ?_, ?_, ?_⟩ <;>
        simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] <;>
        rw [hrdm _ _ (by omega)]
      · exact hglo
      · exact hghi
      · exact hgg
    · exact ⟨h4k, hlo, show s.sp.toNat + 8 ≤ hi by omega, hhi48⟩
    · show (s.regs 29).toNat = s.sp.toNat - 8
      rw [hfp, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · refine ⟨⟨gluePc, s.sp.toNat, Arch.arm64.fp FT gluePc s.sp.toNat⟩ :: fs, ?_⟩
      show Chain Arch.arm64 FT mm hi (BitVec.ofNat 64 gluePc).toNat s.sp.toNat
        (some (BitVec.ofNat 64 ret).toNat) _
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show gluePc < 2 ^ 64 by decide)]
      exact hchain
    · refine ⟨hfit1, ?_⟩
      show 2 * ((hi - s.sp.toNat) + FT.maxspd (BitVec.ofNat 64 gluePc).toNat + stackGuard) ≤ maxstacksize
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show gluePc < 2 ^ 64 by decide), hmx]; omega
    · show H [] (s.regs 28).toNat 0 (rtView rt mm)
      rw [hmm, rtView_writeLE (Outside.of_sub hrt (by omega) (by omega)),
        rtView_writeLE (Outside.of_sub hrt (by omega) (by omega))]
      exact hH
    · rfl
    · rfl
    · exact hhi
    · show mm.readLE (s.sp.toNat + 8) 8 = x.toNat
      rw [hmm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt x.isLt
    · show mm.readLE (s.sp.toNat + 16) 8 = i.toNat
      rw [hmm, Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt i.isLt
    · intro fs' hfs'
      have hfs'' : Chain Arch.arm64 FT mm hi gluePc s.sp.toNat (some ret) fs' := by
        have e2 : (BitVec.ofNat 64 ret).toNat = ret :=
          by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        have := hfs'; simp [setReg_apply, e2] at this
        exact this
      rw [Chain.unique hfs'' hchain]
      simp only [framesCls_cons, hfp0]
      exact ⟨by rw [hf0 8 (.inl rfl), hc8]; rfl, by rw [hf0 16 (.inr rfl), hc16]; rfl⟩


/-! ## The theorem is not vacuous -/

namespace Witness

open Janus.Contracts.StackSat

/-- The caller's return address. -/
def ret : Nat := 0x200000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- A frame table: `BigLocal` at the glue (no frame, largest frame 176, scalar arguments) and its
caller, which stops the walk. -/
def FTb : FrameTable :=
  { valid := fun pc => pc == gluePc || pc == ret, entry := id, spdelta := fun _ => 0,
    maxspd := fun _ => 176, stop := fun pc => pc == ret, injected := fun _ => false,
    locals := fun _ => [], args := fun _ => [], objs := fun _ => [] }

theorem tableOK : TableOK FTb := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;> simp [FTb, gluePc, ret] <;> decide

/-- The stack pointer: 64 bytes above the small slot's bottom, so the frame does **not** fit. -/
def spw : Nat := SL + 64

/-- The call state `BigLocal(7, 0)` on the small 4 KiB stack of `StackSat`. -/
def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 G0 else if i = 29 then BitVec.ofNat 64 (spw - 8)
      else if i = 30 then BitVec.ofNat 64 ret else if i = 0 then 7#64 else 0,
    sp := BitVec.ofNat 64 spw, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [7#64, 0#64] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl⟩

/-- The frame does not fit: the prologue's check fails, so the call can only return through a
stack growth. -/
theorem no_room : ¬ GuardOK s0 48 := by
  intro ⟨_, _, h⟩
  have hg : (s0.regs 28).toNat = G0 := by decide
  rw [hg, show s0.mem = mem0 from rfl, mem0_desc.2.2, show s0.sp.toNat = spw by decide] at h
  simp only [stackGuard, spw] at h; omega

theorem pre : GPre FTb pool rt H s0 := by
  obtain ⟨d1, d2, d3⟩ := mem0_desc
  have hin0 : InRanges G0 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hin8 : InRanges (G0 + 8) 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hg : (s0.regs 28).toNat = G0 := by decide
  have hsp : s0.sp.toNat = spw := by decide
  refine ⟨SL, SH, ?_, ?_, by decide, ?_, ?_, by decide, by decide, by decide, ?_, ?_,
    ⟨⟨(SL, SH), by simp [pool], Nat.le_refl _, by decide⟩, ?_, ?_⟩⟩
  · rw [hg]; exact ⟨by decide, by decide, by simp only [gStackLo, Nat.add_zero]; exact d1, d2, d3⟩
  · rw [hg]; simp [pool, G0, SL, SH, BL, BH]
  · rw [hsp]; decide
  · rw [hsp]; decide
  · rw [hsp]; decide
  · rfl
  · intro r hr
    simp only [pool, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  · refine ⟨by simp [rt, SL, SH, G0], ⟨[⟨ret, spw, spw⟩], ?_, ?_, ?_, ?_⟩, by decide, by decide, ?_, fun _ => rfl, ?_⟩
    · rw [hsp, show (s0.regs 30).toNat = ret by decide]
      exact .stop (by decide) (by decide) (by decide) (by decide) (by decide)
    · intro f hf; simp at hf; subst hf; left; rw [hsp]
    · rw [hsp]; decide
    · rw [hsp]; decide
    · intro pc hv
      simp only [FTb, Bool.or_eq_true, beq_iff_eq] at hv
      rcases hv with rfl | rfl <;>
        exact ⟨by simp only [pool, outside_cons, outside_nil, and_true]; decide, by decide⟩
    · rw [hg]; refine ⟨rfl, .inl ⟨?_, ?_⟩⟩
      · rw [readLE_rtView hin0]; exact d1
      · rw [readLE_rtView hin8]; exact d2

/-- All hypotheses of `correctness` hold together, for a call whose frame does not fit. -/
theorem nonvacuous : ∃ (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (ret : Nat) (s : State),
    MorestackContract Extracted.program FT pool rt H reloc ∧ TableOK FT ∧
    RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [7#64, 0#64] s ∧
    GPre FT pool rt H s ∧ ¬ GuardOK s 48 :=
  ⟨FTb, pool, rt, H, reloc FTb, ret, s0, contract _ FTb, tableOK, hret, setup, pre, no_room⟩

/-- So the guarantee is reached: from a stack where the frame does not fit, `BigLocal(7, 0)`
grows the stack and returns `7`. -/
theorem returns : GrownReturns (Extracted.program.withExit ret) (reloc FTb) s0
    (fun s' => s'.regs 0 = 7#64) :=
  (correctness FTb pool rt H (reloc FTb) (contract _ FTb) tableOK 7#64 0#64 ret hret s0 setup pre).mono
    (fun s' h => by simpa using h)

end Witness

end Proof
