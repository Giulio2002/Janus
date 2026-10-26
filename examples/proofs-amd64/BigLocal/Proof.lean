import Janus
import Extracted

/-!
# `BigLocal(x, i uint64) uint64` on amd64: a large frame, correct with stack growth (R7)

```go
func BigLocal(x, i uint64) uint64 {
	var buf [20]uint64
	buf[i&15] = x
	return buf[0]
}
```

The amd64 counterpart of `examples/proofs/BigLocal.lean`. `BigLocal`'s frame is 168 bytes (the
pushed `RBP` and 160 bytes of locals, more than `abi.StackSmall = 128`), so its prologue
(`LEAQ -40(SP), R12; CMPQ R12, 16(R14); JBE morestack`) calls `runtime.morestack_noctxt`
whenever fewer than `40 + stackGuard` bytes are free below `RSP`. The tail spills `x` and `i` to
`8(SP)` and `16(SP)` (the caller's argument area), `CALL`s the stub, and the glue after it reloads
them and jumps back to the entry.

**Guarantee** (`correctness`). For every frame table that agrees with the binary's frame record
(`FT.Agrees Extracted.frames`: at the glue no frame, largest frame 168 bytes, no pointer
arguments), every stack pool, runtime memory and readiness, and every runtime that meets the amd64
`morestack` contract (`MorestackContract64`, `Janus/Contracts/StackAmd64.lean`), and every call
state whose goroutine stack `[lo, hi)` is described by `g.stack` — **with no assumption that the
frame fits** — the call returns (`GrownReturns64`: after at most one growth) with `RAX = x` if
`i & 15 = 0` and `RAX = 0` otherwise.

**How.** `summary` is the roomy proof (`janus64_run`). `correctness` splits on the prologue's
check: with room it is `summary`; without, `janus64_run` runs the prologue and the tail to the
`morestack` stub, `grow_entry` establishes the contract's precondition there, and `grow_branch`
takes the contract's resumed state through the glue into `summary`, on a stack that now has room
(`Grown64.room`). The return address and the spilled arguments survive the move because `Moved`
copies the words the stack maps call scalars (`Moved.readLE_scalar`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Stack
  Janus.Contracts Janus.Contracts.Stack Janus.Contracts.StackAmd64

namespace Proof

/-- The roomy precondition (the prologue falls through): the return address readable at `[RSP]`
and below `2^47`, the guard 40 bytes below `RSP` (`168 - abi.StackSmall`), the 176-byte window
`[RSP - 168, RSP + 8)` writable, `X15 = 0`. -/
abbrev Pre (s : State) : Prop :=
  s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
  StackGuardOK s 40 ∧ StackWritable s 168 8 ∧ s.xmm 15 = 0

/-- **`BigLocal` on a stack with room**: it returns `buf[0]`, which is `x` when `i & 15 = 0` and
`0` otherwise (the array is zeroed first). -/
theorem summary : Summary Extracted.program Extracted.entry Pre
    (fun s s' => s'.regs 0 = (if (s.regs 3).toNat % 16 = 0 then s.regs 0 else 0)) := by
  intro s hpc ⟨hra, hra2, hg, ⟨hle, hnw, hacc⟩, hx15⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  have hlt : (s.regs 3).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  by_cases hz : (s.regs 3).toNat % 16 = 0
  · janus64_run
    all_goals simp [hz]
  · janus64_run
    all_goals simp [hz]

/-- The glue pc after the `morestack` call (`MOVQ 8(SP), AX`). -/
abbrev gluePc : Nat := Extracted.entry + 0x74

/-- The glue (`MOVQ 8(SP), AX; MOVQ 16(SP), BX; JMP BigLocal`): from any state there it re-enters
`BigLocal` with the spilled arguments reloaded. -/
theorem glue : ∀ t : State, t.rip = BitVec.ofNat 64 gluePc →
    t.mem.accessible ((t.regs 4).toNat + 8) 16 false = true → (t.regs 4).toNat + 24 ≤ 2 ^ 48 →
    ReachesRet Extracted.program (BitVec.ofNat 64 Extracted.entry) t (fun t' =>
      t'.rip = BitVec.ofNat 64 Extracted.entry ∧ t'.regs 4 = t.regs 4 ∧ t'.mem = t.mem ∧
      t'.xmm = t.xmm ∧
      t'.regs 0 = BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 8) 8) ∧
      t'.regs 3 = BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 16) 8) ∧
      (∀ r, r ≠ 0 → r ≠ 3 → t'.regs r = t.regs r)) := by
  intro t hpc hacc hsp
  janus64_run until [Extracted.entry]
  exact ReachesRet.done rfl ⟨rfl, by simp [setRegF], rfl, rfl, by simp [setRegF], by simp [setRegF],
    fun r h0 h3 => by simp [setRegF, h0, h3]⟩

/-- What the binary's frame record says about `BigLocal` at the glue pc (`tableOK_of`). -/
def TableOK (FT : FrameTable) : Prop :=
  FT.valid gluePc = true ∧ FT.stop gluePc = false ∧ FT.injected gluePc = false ∧
  FT.spdelta gluePc = 0 ∧ FT.maxspd gluePc = 168 ∧ FT.args gluePc = [] ∧ FT.objs gluePc = []

/-- `TableOK`, read off the binary's frame record of `BigLocal` (`Extracted.frames`). -/
theorem tableOK_of {FT : FrameTable} (h : FT.Agrees Extracted.frames) : TableOK FT := by
  obtain ⟨a1, -, a3, a4, a5, a6, -, a8, a9⟩ := h _ (List.mem_cons_self ..) gluePc (by decide) (by decide)
  refine ⟨a1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a5] <;> rfl
  · rw [a6] <;> rfl
  · rw [a3] <;> rfl
  · rw [a4] <;> rfl
  · rw [a8] <;> rfl
  · rw [a9] <;> rfl

/-- The grown precondition: the goroutine stack `[lo, hi)` (no room assumed), the caller's walk
from the return address (whose return-address slots lie above the spill slots, and whose stack
maps do not mark the return-address word or `BigLocal`'s argument slots), the pools, the
readiness and the `maxstacksize` bound. -/
def GPre (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s : State) : Prop :=
  ∃ lo hi, GStack s.mem (s.regs 14).toNat lo hi ∧ Outside (s.regs 14).toNat 24 pool ∧
    4096 ≤ lo ∧ lo + 8 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 24 ≤ hi ∧ hi ≤ 2 ^ 48 ∧
    lo % 16 = 0 ∧ hi % 16 = 0 ∧ (s.regs 4).toNat % 8 = 0 ∧
    InRanges lo (hi - lo) pool ∧ PoolOK s.mem pool ∧ Outside lo (hi - lo) rt ∧
    (∃ fs, Chain Arch.amd64 FT s.mem hi (s.mem.readLE (s.regs 4).toNat 8) ((s.regs 4).toNat + 8) none fs ∧
      (∀ f ∈ fs, FT.stop f.pc = false → (s.regs 4).toNat + 24 ≤ f.fp - 8) ∧
      framesCls Arch.amd64 FT fs (s.regs 4).toNat = false ∧
      framesCls Arch.amd64 FT fs ((s.regs 4).toNat + 8) = false ∧
      framesCls Arch.amd64 FT fs ((s.regs 4).toNat + 16) = false) ∧
    2 * (hi - lo) ≤ maxstacksize ∧ 2 * ((hi - (s.regs 4).toNat) + 168 + stackGuard) ≤ maxstacksize ∧
    FT.CodeOutside pool ∧ FT.Aligned ∧ H [] (s.regs 14).toNat 0 (rtView rt s.mem) ∧ NoStackPtr s.mem pool rt

/-- The growth path, from the contract's precondition at the `morestack` stub: the contract
resumes on a larger stack, the glue reloads `x` and `i` from the moved spill slots, and `summary`
applies there. -/
theorem grow_branch (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (hFT : TableOK FT) (x i : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (g lo hi : Nat) (s_m : State) (hm : MorestackPre64 Extracted.program FT pool rt H g lo hi s_m)
    (hglue : gluePcOf s_m = gluePc) (hspill : (s_m.regs 4).toNat + 32 ≤ hi)
    (hsr : s_m.mem.readLE ((s_m.regs 4).toNat + 8) 8 = ret)
    (hsx : s_m.mem.readLE ((s_m.regs 4).toNat + 16) 8 = x.toNat)
    (hsi : s_m.mem.readLE ((s_m.regs 4).toNat + 24) 8 = i.toNat)
    (hcls : ∀ fs, Chain Arch.amd64 FT s_m.mem hi (gluePcOf s_m) (fspOf s_m) none fs →
      ∀ j, j = 0 ∨ j = 8 ∨ j = 16 → framesCls Arch.amd64 FT fs ((s_m.regs 4).toNat + 8 + j) = false) :
    ∃ s_r, reloc s_m s_r ∧ GrownReturns64 (Extracted.program.withExit ret) reloc s_r
      (fun s' => s'.regs 0 = if i.toNat % 16 = 0 then x else 0) := by
  obtain ⟨s_r, lo', hi', hre, hgr⟩ := hms g lo hi s_m hm
  refine ⟨s_r, hre, ?_⟩
  obtain ⟨hgr1, hgr2, h4k', hal1', hal2', hhi48', hinp', happ⟩ := hgr.grows
  have hroom := hgr.room
  have hmax : FT.maxspd (gluePcOf s_m) = 168 := by rw [hglue]; exact hFT.2.2.2.2.1
  rw [hmax] at hroom
  simp only [stackGuard, fspOf, regSP] at hroom
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hm.low
  obtain ⟨ha1, ha2, ha3⟩ := hm.aligned
  simp only [regSP] at hl2 hl3 ha3
  have hret47 : ret < 2 ^ 47 := hret.user
  have hsp_r : (s_r.regs 4).toNat = (s_m.regs 4).toNat + 8 + hi' - hi := by
    rw [show s_r.regs 4 = s_r.regs regSP from rfl, hgr.sp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by simp only [fspOf, regSP]; omega)
  have hpok_r : PoolOK s_r.mem pool := hm.inPool.2.of_accessible hgr.frame.accessible
  have hacc_r : s_r.mem.accessible lo' (hi' - lo') true = true := hpok_r.accessible hinp'
  have hpc_r : s_r.rip = BitVec.ofNat 64 gluePc := by
    rw [hgr.pc, retAddrOf, ← hglue]
  obtain ⟨k, t, hst, htpc, -, ht4, htmem, htx, ht0, ht3, htr⟩ := glue s_r hpc_r
    (Arm64.Memory.accessible_read_of_write _ (Arm64.Memory.accessible_mono _ hacc_r (by omega) (by omega)))
    (by omega)
  apply GrownReturns64.of_steps (hst.withExit hret.fetch_none)
  apply GrownReturns64.done
  obtain ⟨fs, hchm⟩ := hm.chain
  have hmv := hgr.moved fs hchm
  have hrd : ∀ j, j = 0 ∨ j = 8 ∨ j = 16 →
      s_r.mem.readLE ((s_r.regs 4).toNat + j) 8 = s_m.mem.readLE ((s_m.regs 4).toNat + 8 + j) 8 := by
    intro j hj
    have hc := hcls fs hchm j hj
    rw [hsp_r, show (s_m.regs 4).toNat + 8 + hi' - hi + j = ((s_m.regs 4).toNat + 8 + j) + hi' - hi by omega]
    exact hmv.readLE_scalar (by simp only [fspOf, regSP]; omega) (by omega) (fun j' hj' => by
      rw [show (s_m.regs 4).toNat + 8 + j + j' - ((s_m.regs 4).toNat + 8 + j + j') % 8 =
        (s_m.regs 4).toNat + 8 + j by omega]; exact hc) trivial
  have hg14 : t.regs 14 = s_m.regs 14 := (htr 14 (by decide) (by decide)).trans hgr.gkeep
  have hgreg := hm.greg
  simp only [regG] at hgreg
  obtain ⟨hgg24, hggacc, -, -, hggd⟩ := hgr.gstack
  simp only [gStackguard0, stackGuard] at hggd
  have hr0 : t.mem.readLE (t.regs 4).toNat 8 = ret := by
    rw [htmem, ht4]; exact (hrd 0 (.inl rfl)).trans hsr
  refine Summary.returns summary hret htpc (by rw [retAddrOf, hr0]) ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ ?_
  · rw [ht4, hsp_r, htmem]
    exact Arm64.Memory.accessible_read_of_write _ (Arm64.Memory.accessible_mono _ hacc_r (by omega) (by omega))
  · rw [hr0]; exact hret47
  · simp only [regG, stackguard0Offset]; rw [hg14, hgreg]; omega
  · simp only [regG, stackguard0Offset]; rw [hg14, hgreg, htmem]
    exact Arm64.Memory.accessible_mono _ hggacc (by omega) (by omega)
  · simp only [stackguard0, regG, regSP, stackguard0Offset]
    rw [hg14, hgreg, htmem, hggd, ht4, hsp_r]; omega
  · simp only [regSP]; rw [ht4, hsp_r]; omega
  · simp only [regSP]; rw [ht4, hsp_r]; omega
  · simp only [regSP]; rw [ht4, hsp_r, htmem]
    exact Arm64.Memory.accessible_mono _ hacc_r (by omega) (by omega)
  · rw [htx]; exact hgr.zero
  · intro s' hs'
    show s'.regs 0 = _
    rw [hs', ht0, ht3, show (s_r.regs 4).toNat + 8 = (s_r.regs 4).toNat + 8 from rfl,
      hrd 8 (.inr (.inl rfl)), hrd 16 (.inr (.inr rfl))]
    rw [show (s_m.regs 4).toNat + 8 + 8 = (s_m.regs 4).toNat + 16 by omega,
      show (s_m.regs 4).toNat + 8 + 16 = (s_m.regs 4).toNat + 24 by omega, hsx, hsi,
      BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]

/-- The memory at the `morestack` call: the tail spilled `x` and `i` to `8(SP)`, `16(SP)`, and
the `CALL` pushed the glue address `v` at `-8(SP)`. -/
abbrev stubMem (s : State) (x i : BitVec 64) (v : Nat) : Memory :=
  ((s.mem.writeLE ((s.regs 4).toNat + 8) 8 x.toNat).writeLE ((s.regs 4).toNat + 16) 8 i.toNat).writeLE
    ((s.regs 4).toNat - 8) 8 v

/-- The growth path from the call state `s` (whose prologue check failed): the stub state `S`
satisfies the contract's precondition, and the call returns after the growth. -/
theorem grow_entry (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (hFT : TableOK FT) (x i : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hpre : GPre FT pool rt H s) (h_ret : s.mem.readLE (s.regs 4).toNat 8 = ret)
    (S : State) (hstub : ∃ name, Extracted.program.stubAt S.rip.toNat = some ⟨name, S.rip.toNat, .morestack⟩)
    (h4 : S.regs 4 = s.regs 4 - 8#64) (h14 : S.regs 14 = s.regs 14)
    (hmem : S.mem = stubMem s x i gluePc) :
    ∃ s_r, reloc S s_r ∧ GrownReturns64 (Extracted.program.withExit ret) reloc s_r
      (fun s' => s'.regs 0 = if i.toNat % 16 = 0 then x else 0) := by
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hinp, hpok, hrt,
    ⟨fs, hch, hfsp, hc0, hc8, hc16⟩, hfit1, hfit2, hcode, hal, hH, hNP⟩ := hpre
  obtain ⟨hv, hst, hinj, hspd, hmx, hargs, hob⟩ := hFT
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero] at hglo hghi hgg
  have hsp := (s.regs 4).isLt
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 8 := by
    rw [h4, BitVec.toNat_sub]; rw [show (8#64).toNat = 8 from rfl]; omega
  have hgw : (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 24 ≤ (s.regs 14).toNat := by
    have := InRanges.disjoint (InRanges.sub hinp (a := (s.regs 4).toNat - 8) (n := 32) (by omega) (by omega)) hgo
    omega
  have hrdm : ∀ a n, (a + n ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat ≤ a) →
      (a + n ≤ (s.regs 4).toNat + 8 ∨ (s.regs 4).toNat + 24 ≤ a) → S.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    rw [hmem, stubMem, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have haccm : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [hmem, stubMem, Arm64.Memory.accessible_writeLE, Arm64.Memory.accessible_writeLE,
      Arm64.Memory.accessible_writeLE]
  have hglue : gluePcOf S = gluePc := by
    simp only [gluePcOf, regSP]
    rw [hS4, hmem, stubMem, Arm64.Memory.readLE_writeLE_self]; rfl
  have hfspS : fspOf S = (s.regs 4).toNat := by simp only [fspOf, regSP]; rw [hS4]; omega
  have hcm : Chain Arch.amd64 FT S.mem hi ret ((s.regs 4).toNat + 8) none fs := by
    rw [← h_ret]
    have := Chain.congr hch (m' := S.mem) (by omega) fun f hf hstp => by
      have := hfsp f hf hstp
      exact hrdm _ _ (by simp only [Arch.lrSlot]; omega) (by simp only [Arch.lrSlot]; omega)
    exact this
  have hfp0 : Arch.amd64.fp FT gluePc (s.regs 4).toNat = (s.regs 4).toNat + 8 := by
    simp [Arch.fp, hspd]
  have hchain : Chain Arch.amd64 FT S.mem hi gluePc (s.regs 4).toNat none
      (⟨gluePc, (s.regs 4).toNat, (s.regs 4).toNat + 8⟩ :: fs) := by
    have hlr : Arch.amd64.lrOf S.mem (s.regs 4).toNat ((s.regs 4).toNat + 8) none = ret := by
      simp only [Arch.lrOf, Nat.add_sub_cancel]
      rw [hrdm _ _ (by omega) (by omega)]; exact h_ret
    have := Chain.cons (A := Arch.amd64) (FT := FT) (m := S.mem) (hi := hi) (pc := gluePc)
      (sp := (s.regs 4).toNat) (lr0 := none) (fs := fs) hv hst hinj (by omega) (by rw [hfp0]; omega)
      (by rw [hfp0, hlr]; exact hcm)
    rw [hfp0] at this; exact this
  have hf0 : ∀ a, frameCls Arch.amd64 FT gluePc (s.regs 4).toNat ((s.regs 4).toNat + 8) a = false := by
    intro a
    have hv0 : Arch.amd64.varp (s.regs 4).toNat ((s.regs 4).toNat + 8) = (s.regs 4).toNat := by
      simp [Arch.varp]
    simp only [frameCls, hv0, Arch.argp, Arch.minLocals, hargs, hob, List.any_nil, Bool.or_false]
    have e1 : decide ((s.regs 4).toNat + 8 = (s.regs 4).toNat + 16) = false := by simp
    have e2 : decide (0 + (s.regs 4).toNat < (s.regs 4).toNat) = false := by simp
    rw [e1, e2]; simp [bitsAt]
  have hr3 : (S.regs 4).toNat + 8 = (s.regs 4).toNat := by omega
  refine grow_branch FT pool rt H reloc hms ⟨hv, hst, hinj, hspd, hmx, hargs, hob⟩ x i ret hret
    (s.regs 14).toNat lo hi S ⟨hstub, by simp only [regG]; rw [h14], ?_, hgo, ?_, ?_,
      ⟨hinp, hpok.of_accessible haccm⟩, ?_, ?_, ⟨hcode, hal⟩, ?_, ?_⟩ hglue (by omega) ?_ ?_ ?_ ?_
  · refine ⟨hg24, by rw [haccm]; exact hgacc, ?_, ?_, ?_⟩ <;>
      simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero] <;>
      rw [hrdm _ _ (by omega) (by omega)]
    · exact hglo
    · exact hghi
    · exact hgg
  · simp only [regSP]; rw [hS4]; omega
  · simp only [regSP]; rw [hS4]; omega
  · rw [hglue, hfspS]; exact ⟨_, hchain⟩
  · rw [hglue, hfspS, hmx]; exact ⟨hfit1, by omega⟩
  · rw [hmem, stubMem, rtView_writeLE (Outside.of_sub hrt (by omega) (by omega)),
      rtView_writeLE (Outside.of_sub hrt (by omega) (by omega)),
      rtView_writeLE (Outside.of_sub hrt (by omega) (by omega))]
    exact hH
  · rw [hmem, stubMem]
    exact ((hNP.writeLE _ (hinp.sub (by omega) (by omega))).writeLE _ (hinp.sub (by omega) (by omega))).writeLE _
      (hinp.sub (by omega) (by omega))
  · rw [hr3, hrdm _ _ (by omega) (by omega)]; exact h_ret
  · rw [show (S.regs 4).toNat + 16 = (s.regs 4).toNat + 8 by omega, hmem, stubMem,
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt x.isLt
  · rw [show (S.regs 4).toNat + 24 = (s.regs 4).toNat + 16 by omega, hmem, stubMem,
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt i.isLt
  · intro fs' hfs' j hj
    rw [hglue, hfspS] at hfs'
    rw [Chain.unique hfs' hchain, hr3]
    simp only [framesCls_cons, hf0, Bool.false_or]
    rcases hj with rfl | rfl | rfl
    · exact hc0
    · exact hc8
    · exact hc16

/-- **`BigLocal` is correct on a stack of any size, stack growth included** (amd64). -/
theorem correctness (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (hA : FT.Agrees Extracted.frames) (x i : BitVec 64) :
    EnsuresGrow64 Extracted.program reloc Extracted.entry [x, i] (GPre FT pool rt H)
      (fun _ s' => s'.regs 0 = if i.toNat % 16 = 0 then x else 0) := by
  have hFT := tableOK_of hA
  intro ret hret s hs hpre
  have hpre' := hpre
  janus64_intro hs
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hinp, hpok, hrt,
    -, hfit1, hfit2, hcode, hal, hH, -⟩ := hpre
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
  have hacc : s.mem.accessible lo (hi - lo) true = true := hpok.accessible hinp
  have hret47 : ret < 2 ^ 47 := hret.user
  by_cases hroom : lo + 928 + 40 < (s.regs 4).toNat
  · apply GrownReturns64.done
    refine Summary.returns summary hret (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret])
      ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, h_x15⟩ ?_
    · exact Arm64.Memory.accessible_read_of_write _ (Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
    · rw [h_ret]; exact hret47
    · simp only [regG, stackguard0Offset]; omega
    · simp only [regG, stackguard0Offset]; exact Arm64.Memory.accessible_mono _ hgacc (by omega) (by omega)
    · simp only [stackguard0, regG, regSP, stackguard0Offset]; rw [hgg]; omega
    · simp only [regSP]; omega
    · simp only [regSP]; omega
    · simp only [regSP]; exact Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
    · intro s' hs'; show s'.regs 0 = _; rw [hs', h_a0, h_a1]
  · apply GrownReturns64.of_reaches_stub
    janus64_run
    exact grow_entry FT pool rt H reloc hms hFT x i ret hret s hpre' h_ret _ ⟨_, rfl⟩
      (by simp [setRegF]) (by simp [setRegF]) rfl

/-! ## The theorem is not vacuous -/

namespace Witness

open Janus.Contracts.StackSat (G0 SL SH BL BH pool rt H mem0 mem0_desc mem0_noptr)
open Janus.Contracts.StackSatAmd64 (reloc contract64)

/-- The caller's return address. -/
def ret : Nat := 0x200000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The witness frame table: the binary's frame record of `BigLocal` and the caller, which stops
the walk. -/
def extraT : FrameTable :=
  { valid := fun pc => pc == ret, entry := id, spdelta := fun _ => 0, maxspd := fun _ => 0,
    stop := fun pc => pc == ret, injected := fun _ => false, locals := fun _ => [],
    args := fun _ => [], objs := fun _ => [] }

def FTb : FrameTable := FrameTable.ofRecs Extracted.frames extraT

theorem agrees : FTb.Agrees Extracted.frames :=
  FrameTable.ofRecs_agrees _ _ fun r hr pc h1 h2 => by
    replace hr := List.mem_singleton.1 hr
    subst hr
    exact List.find?_cons_of_pos (l := []) (by simpa using And.intro h1 h2)

theorem laws : FTb.Aligned ∧ FTb.InFrame Arch.amd64 :=
  FrameTable.ofRecs_laws_amd64 Extracted.frames extraT (fun r hr => by
    replace hr := List.mem_singleton.1 hr
    subst hr
    exact ⟨rfl, by decide⟩) (fun _ => rfl) (fun _ => rfl)

theorem code : FTb.CodeOutside pool := by
  intro pc hv
  unfold FTb FrameTable.ofRecs at hv
  dsimp only at hv
  cases h : Extracted.frames.find? (fun r => decide (r.entry ≤ pc ∧ pc < r.entry + r.size)) with
  | none =>
    rw [h] at hv
    simp only [extraT, beq_iff_eq] at hv
    subst hv
    exact ⟨by simp only [pool, outside_cons, outside_nil, and_true]; decide, by decide⟩
  | some r =>
    have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    replace hm := List.mem_singleton.1 hm
    subst hm
    simp only at hp
    refine ⟨?_, by omega⟩
    simp only [pool, outside_cons, outside_nil, and_true, SL, SH, BL, BH]; omega

/-- The stack pointer: 64 bytes above the small slot's bottom, so the frame does **not** fit. -/
def spw : Nat := SL + 64

/-- The memory: `StackSat`'s (the small slot's descriptor, the two slots writable), with the
return address at `[RSP]`. -/
def memw : Memory := mem0.writeLE spw 8 ret

/-- The call state `BigLocal(7, 0)` on the small 4 KiB stack of `StackSat`. -/
def s0 : State :=
  { regs := fun i => if i = 14 then BitVec.ofNat 64 G0 else if i = 4 then BitVec.ofNat 64 spw
      else if i = 0 then 7#64 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := memw }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [7#64, 0#64] s0 :=
  ⟨rfl, by decide, rfl, by decide,
    by intro i h; simp at h; rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl, rfl⟩

theorem memw_desc : memw.readLE G0 8 = SL ∧ memw.readLE (G0 + 8) 8 = SH ∧
    memw.readLE (G0 + 16) 8 = SL + stackGuard := by
  obtain ⟨d1, d2, d3⟩ := mem0_desc
  refine ⟨?_, ?_, ?_⟩ <;> unfold memw <;>
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by simp [G0, spw, SL])] <;> assumption

/-- The frame does not fit: the prologue's check fails, so the call can only return through a
stack growth. -/
theorem no_room : ¬ StackGuardOK s0 40 := by
  intro ⟨_, _, h⟩
  have hg : (s0.regs 14).toNat = G0 := by decide
  simp only [stackguard0, regG, regSP, stackguard0Offset] at h
  rw [hg, show s0.mem = memw from rfl, memw_desc.2.2, show (s0.regs 4).toNat = spw by decide] at h
  simp only [stackGuard, spw] at h; omega

theorem pre : GPre FTb pool rt H s0 := by
  obtain ⟨d1, d2, d3⟩ := memw_desc
  have hin0 : InRanges G0 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hin8 : InRanges (G0 + 8) 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hg : (s0.regs 14).toNat = G0 := by decide
  have hsp : (s0.regs 4).toNat = spw := by decide
  have hr : s0.mem.readLE spw 8 = ret := by decide
  refine ⟨SL, SH, ?_, ?_, by decide, ?_, ?_, by decide, by decide, by decide, ?_,
    ⟨(SL, SH), by simp [pool], Nat.le_refl _, by decide⟩, ?_, ?_⟩
  · rw [hg]; exact ⟨by decide, by decide, by simp only [gStackLo, Nat.add_zero]; exact d1, d2, d3⟩
  · rw [hg]; simp [pool, G0, SL, SH, BL, BH]
  · rw [hsp]; decide
  · rw [hsp]; decide
  · rw [hsp]; decide
  · intro r hr
    simp only [pool, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  · have el : FTb.locals ret = [] := rfl
    have ea : FTb.args ret = [] := rfl
    have eo : FTb.objs ret = [] := rfl
    have e : Arch.amd64.fp FTb ret (spw + 8) = spw + 16 := by
      show spw + 8 + FTb.spdelta ret + 8 = spw + 16; rw [show FTb.spdelta ret = 0 from rfl]
    refine ⟨by simp [rt, SL, SH, G0], ⟨[⟨ret, spw + 8, spw + 16⟩], ?_, ?_, ?_, ?_, ?_⟩, by decide, by decide, code,
      laws.1, ?_, mem0_noptr.writeLE _ ⟨(SL, SH), by simp [pool], by decide, by decide⟩⟩
    · rw [hsp, hr]
      have := Chain.stop (A := Arch.amd64) (FT := FTb) (m := s0.mem) (hi := SH) (pc := ret) (sp := spw + 8)
        (lr0 := none) rfl rfl rfl (by decide) (by rw [e]; decide)
      rw [e] at this; exact this
    · intro f hf hst; simp at hf; subst hf; exact absurd hst (by decide)
    · rw [hsp]; simp [frameCls, el, ea, eo, bitsAt, Arch.varp, Arch.argp, Arch.minLocals]
    · rw [hsp]; simp [frameCls, el, ea, eo, bitsAt, Arch.varp, Arch.argp, Arch.minLocals]
    · rw [hsp]; simp [frameCls, el, ea, eo, bitsAt, Arch.varp, Arch.argp, Arch.minLocals]
    · rw [hg]; refine ⟨rfl, .inl ⟨?_, ?_⟩⟩
      · rw [readLE_rtView hin0]; exact d1
      · rw [readLE_rtView hin8]; exact d2

/-- All hypotheses of `correctness` hold together, for a call whose frame does not fit. -/
theorem nonvacuous : ∃ (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (ret : Nat) (s : State),
    MorestackContract64 Extracted.program FT pool rt H reloc ∧ FT.Agrees Extracted.frames ∧
    RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [7#64, 0#64] s ∧
    GPre FT pool rt H s ∧ ¬ StackGuardOK s 40 :=
  ⟨FTb, pool, rt, H, reloc FTb, ret, s0, contract64 _ FTb, agrees, hret, setup, pre, no_room⟩

/-- So the guarantee is reached: from a stack where the frame does not fit, `BigLocal(7, 0)`
grows the stack and returns `7`. -/
theorem returns : GrownReturns64 (Extracted.program.withExit ret) (reloc FTb) s0
    (fun s' => s'.regs 0 = 7#64) :=
  (correctness FTb pool rt H (reloc FTb) (contract64 _ FTb) agrees 7#64 0#64 ret hret s0 setup pre).mono
    (fun s' h => by simpa using h)

end Witness

end Proof
