import Extracted

/-!
# `Chain(dst, src, bx, n)`: `memmove`, `makeslice`, `memmove` and a barrier store, one runtime hypothesis (arm64)

```go
type Box struct{ P *uint64; N uint64 }
func Chain(dst, src []uint64, bx *Box, n int) {
	copy(dst, src)
	t := make([]uint64, n)
	bx.N = uint64(n)
	copy(t, src)
	bx.P = &t[0]
}
```

`runtime.memmove`, `runtime.makeslice` and `runtime.gcWriteBarrier2` are the live contracts of
`Janus/Contracts/Live.lean`, about ONE runtime hypothesis `R`. The caller's objects (`dst`, `src`,
`bx`) are in the live set `L` at the entry: the first `memmove` writes into one of them (a live
destination: the view does not change), `makeslice` returns a new array outside `L` and keeps all
three unchanged, the second `memmove` writes into the new array (live after `makeslice`), and the
barrier store goes through the buffer the barrier returns.

**Guarantee.** For every runtime satisfying the three contracts and every state in which `dst`,
`src` are disjoint live arrays, `bx` a live 16-byte object apart from both, `0 < n < 2^40`, and the
budget covers the new array: the call returns; `bx.N = n`; `bx.P = t` for an array `t` inside
`R.rt` that is disjoint from `dst`, `src` and `bx`; the runtime invariant holds for the live set
with `t`; memory changed only in `R.rt`, the stack window, the first `min(len dst, len src)` words of
`dst` and `bx`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The type descriptor `Chain` passes to `makeslice` (`ADRP`+`ADD` at `Chain+0x4c`) and the address of
the write-barrier flag (`ADRP`+`MOVWU` at `Chain+0xa0`), recomputed from the extracted words. -/
def u64Type : Nat :=
  adrpLdTarget (Extracted.entry + 0x4c) (segWord Extracted.program "example.com/rtmisc/live.Chain" 19)
    (segWord Extracted.program "example.com/rtmisc/live.Chain" 20) 0
def flagAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0xa0) (segWord Extracted.program "example.com/rtmisc/live.Chain" 40)
    (segWord Extracted.program "example.com/rtmisc/live.Chain" 41) 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (dp dl dc sp sl sc bx n : BitVec 64)
    (hmv : MemmoveLive (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hwb : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Ensures (Extracted.program.link impl) Extracted.entry [dp, dl, dc, sp, sl, sc, bx, n]
      (fun s => GuardOK s 4144 ∧ StackOK s 4152 72 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4152) 4224 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4152) 4224 ∧
        Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ s.mem.accessible flagAddr 4 false = true ∧
        Outside u64Type 16 R.rt ∧
        0 < n.toNat ∧ n.toNat < 2 ^ 40 ∧ 0 < dl.toNat ∧ 0 < sl.toNat ∧ dl.toNat < 2 ^ 40 ∧ sl.toNat < 2 ^ 40 ∧
        R.ok (Extracted.program.contractAddr "runtime.makeslice") [u64Type, n.toNat, n.toNat] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
        R.ok (Extracted.program.contractAddr "runtime.memmove") [dp.toNat, sp.toNat, 8 * min sl.toNat dl.toNat] ∧
        (∀ t, R.ok (Extracted.program.contractAddr "runtime.memmove") [t, sp.toNat, 8 * min sl.toNat n.toNat]) ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4152, s.sp.toNat + 72)]) ∧
        InRanges dp.toNat (8 * dl.toNat) L ∧ InRanges sp.toNat (8 * sl.toNat) L ∧ InRanges bx.toNat 16 L ∧
        s.mem.accessible dp.toNat (8 * dl.toNat) true = true ∧ s.mem.accessible sp.toNat (8 * sl.toNat) false = true ∧
        s.mem.accessible bx.toNat 16 true = true ∧
        dp.toNat + 8 * dl.toNat ≤ 2 ^ 48 ∧ sp.toNat + 8 * sl.toNat ≤ 2 ^ 48 ∧ bx.toNat + 16 ≤ 2 ^ 48 ∧
        Apart dp.toNat (8 * dl.toNat) sp.toNat (8 * sl.toNat) ∧
        Apart bx.toNat 16 dp.toNat (8 * dl.toNat) ∧ Apart bx.toNat 16 sp.toNat (8 * sl.toNat) ∧
        Apart ((s.regs 28).toNat + 16) 8 dp.toNat (8 * dl.toNat) ∧ Apart ((s.regs 28).toNat + 16) 8 bx.toNat 16 ∧
        blockSize (8 * n.toNat) true ≤ b)
      (fun s s' => ∃ t : Nat, s'.mem.readLE bx.toNat 8 = t ∧ s'.mem.readLE (bx.toNat + 8) 8 = n.toNat ∧
        InRanges t (blockSize (8 * n.toNat) true) R.rt ∧
        Apart t (blockSize (8 * n.toNat) true) dp.toNat (8 * dl.toNat) ∧
        Apart t (blockSize (8 * n.toNat) true) sp.toNat (8 * sl.toNat) ∧
        Apart t (blockSize (8 * n.toNat) true) bx.toNat 16 ∧
        ∃ b' L', b - blockSize (8 * n.toNat) true ≤ b' ∧
          R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
          InRanges t (blockSize (8 * n.toNat) true) L' ∧ InRanges dp.toNat (8 * dl.toNat) L' ∧
          InRanges sp.toNat (8 * sl.toNat) L' ∧ InRanges bx.toNat 16 L' ∧
          MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4152, s.sp.toNat + 72),
            (dp.toNat, dp.toNat + 8 * min sl.toNat dl.toNat), (bx.toNat, bx.toNat + 16)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty1, hn, hn2, hdl0, hsl0, hdl, hsl, hok1, hok2, hok3, hok4, hinv, hLs, hind, hins, hinb, hacd, hacs, hacb, hbd, hbs, hbb, hap1, hap2, hap3, hgd, hgb, hbud⟩
  have hOut : ∀ a k, InRanges a k L → (a + k ≤ s.sp.toNat - 4152 ∨ s.sp.toNat + 72 ≤ a) := by
    intro a k h
    obtain ⟨r, hr, h3, h4⟩ := h
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  have hblk := Janus.Contracts.AllocSat.le_blockSize (8 * n.toNat) true
  unfold Apart at hap1 hap2 hap3 hgd hgb
  have hobx := hOut _ _ hinb
  have hodp := hOut _ _ hind
  have hosp := hOut _ _ hins
  janus_intro hs
  janus_data hd [hw, hacd, hacb]
  janus_eval_nat h_u : u64Type
  janus_eval_nat h_f : flagAddr
  rw [h_u] at hty1 hok1
  rw [h_f] at hflag
  janus_run calls [hmv, hmk.pos, hmv, hwb]
  all_goals (refine ⟨_, rfl, ?_⟩)
  all_goals janus_split_and
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals first
    | (refine ⟨b - blockSize (8 * n.toNat) true, L ++ [(?t, ?t + blockSize (8 * n.toNat) true)],
        Nat.le_refl _, ?_⟩)
    | skip
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals first
    | (with_reducible assumption)
    | (unfold Apart; with_reducible assumption)
    | janus_live
    | exact InRanges.append_right _ (InRanges.cons_head [] (Nat.le_refl _) (Nat.le_refl _))
    | exact InRanges.append_left hind _
    | exact InRanges.append_left hins _
    | exact InRanges.append_left hinb _
    | (janus_simp; done)
    | janus_frame

end Proof

namespace Proof

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat

def mvA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memmove")
def mkA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
def wbA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")

def implAt : List Segment :=
  [{ name := "witness.memmove", base := mvA, words := memmoveCode },
   { name := "witness.makeslice", base := mkA, words := makesliceCodeD },
   { name := "witness.gcWriteBarrier2", base := wbA, words := wbCode }]

/-- The caller's objects: `dst` (8 bytes), `src` (8 bytes), `bx` (16 bytes), in the heap. -/
def dstP : Nat := HEAP
def srcP : Nat := HEAP + 0x10
def bxP : Nat := HEAP + 0x20
def liveL : List (Nat × Nat) := [(dstP, dstP + 8), (srcP, srcP + 8), (bxP, bxP + 16)]

/-- The requests the witness runtime serves: `Chain(dst, src, bx, 2)` with one-word slices. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = mvA ∧ ∃ d sr, args = [d, sr, 8]) ∨ (a = mkA ∧ args = [u64Type, 2, 2]) ∨ (a = wbA ∧ args = [2])

def R : RtInv := toyR [] ok

def linked : Program := Extracted.program.link implAt

theorem addr_mv : Extracted.program.contractAddr "runtime.memmove" = mvA := by decide
theorem addr_mk : Extracted.program.contractAddr "runtime.makeslice" = mkA := by decide
theorem addr_wb : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wbA := by decide

set_option maxRecDepth 20000 in
theorem model_mv : MemmoveLive linked mvA 4096 R := by
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
  have h8 : (s.regs 2).toNat = 8 := by
    rcases hLm.1 with ⟨_, d, sr, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · simp only [List.cons.injEq, and_true] at h; exact h.2.2
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  rw [h8] at hs2 hd2 hd4
  change ReachesRet linked _ s _
  janus_run
  rw [h8]
  refine liveMemRet_store rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hd4 hLm.2.1 ?_
  intro i hi
  exact IfaceModel.bytes_writeLE_readLE _ _ _ _ _ hi

set_option maxRecDepth 20000 in
theorem model_mk : MakesliceLiveContract linked mkA 4096 R := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, hq1, hq2, hq3, hq4, hq5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  change ReachesRet linked _ s _
  janus_run
  exact finish_makesliceD (tys := []) (by intro t ht; simp at ht) pre

set_option maxRecDepth 20000 in
theorem model_wb : WbLiveContract linked wbA 4096 R 2 := by
  intro L b s hpc pre
  have ⟨⟨h30a, h30b, _⟩, _⟩ := pre
  change ReachesRet linked _ s _
  janus_run
  have h := wb_post (tys := []) (ok := ok) (by intro t ht; simp at ht) (n := 2) (b := b) (L := L) (s := s) (by omega) pre.2.2.1 pre.2.2.2.2
  simp only [wbFinal, wbRetX, apartAll_cons, apartAll_nil, and_true, show 8 * 2 = 16 from rfl] at h
  exact h

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

/-- The bump cell holds `HEAP + 0x30` (past the three caller objects); `src[0] = 0x55`. -/
def bytes0 (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP then 0x30 else if a = BUMP + 2 then 0x50 else if a = srcP then 0x55 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4152, 4224, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, 0x10000, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 dstP else if i = 1 then 1 else if i = 2 then 1
      else if i = 3 then BitVec.ofNat 64 srcP else if i = 4 then 1 else if i = 5 then 1
      else if i = 6 then BitVec.ofNat 64 bxP else if i = 7 then 2 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 dstP, 1, 1, BitVec.ofNat 64 srcP, 1, 1,
    BitVec.ofNat 64 bxP, 2] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

theorem dataByte_none (a : Nat) (ha : 0x500000 ≤ a) : dataByte a = none := by
  unfold dataByte
  have : Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have h2 : d.base + d.bytes.length < 0x500000 := by
      have : ∀ d' ∈ Extracted.data, d'.base + d'.bytes.length < 0x500000 := by decide
      exact this d hd
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; omega
  rw [this]

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP + 0x30 := by decide

theorem inv0 : R.inv 0x100 liveL (s0.regs 28).toNat (view R.rt liveL s0.mem) := by
  refine toyInv_init_live (m := mem0) (g := (s0.regs 28).toNat) (p0 := HEAP + 0x30) (by decide) (by decide) (by decide)
    (by intro r hr; simp only [liveL, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [dstP, srcP, bxP, HEAP] <;> omega)
    bytes0_bump (fun i hi hi' => ?_) (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [BUMP, HEAP] at *; omega),
    if_neg (by simp only [srcP, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : GuardOK s0 4144 ∧ StackOK s0 4152 72 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4152) 4224 R.rt ∧ Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 4152) 4224 ∧
    Outside ((s0.regs 28).toNat + 16) 8 R.rt ∧ s0.mem.accessible flagAddr 4 false = true ∧
    Outside u64Type 16 R.rt ∧
    0 < (2 : BitVec 64).toNat ∧ (2 : BitVec 64).toNat < 2 ^ 40 ∧ 0 < (1 : BitVec 64).toNat ∧ 0 < (1 : BitVec 64).toNat ∧
    (1 : BitVec 64).toNat < 2 ^ 40 ∧ (1 : BitVec 64).toNat < 2 ^ 40 ∧
    R.ok (Extracted.program.contractAddr "runtime.makeslice") [u64Type, (2 : BitVec 64).toNat, (2 : BitVec 64).toNat] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.ok (Extracted.program.contractAddr "runtime.memmove") [dstP, srcP, 8 * min (1 : BitVec 64).toNat (1 : BitVec 64).toNat] ∧
    (∀ t, R.ok (Extracted.program.contractAddr "runtime.memmove") [t, srcP, 8 * min (1 : BitVec 64).toNat (2 : BitVec 64).toNat]) ∧
    R.inv 0x100 liveL (s0.regs 28).toNat (view R.rt liveL s0.mem) ∧
    (∀ r ∈ liveL, Outside r.1 (r.2 - r.1) [(s0.sp.toNat - 4152, s0.sp.toNat + 72)]) ∧
    InRanges dstP (8 * (1 : BitVec 64).toNat) liveL ∧ InRanges srcP (8 * (1 : BitVec 64).toNat) liveL ∧ InRanges bxP 16 liveL ∧
    s0.mem.accessible dstP (8 * (1 : BitVec 64).toNat) true = true ∧ s0.mem.accessible srcP (8 * (1 : BitVec 64).toNat) false = true ∧
    s0.mem.accessible bxP 16 true = true ∧
    dstP + 8 * (1 : BitVec 64).toNat ≤ 2 ^ 48 ∧ srcP + 8 * (1 : BitVec 64).toNat ≤ 2 ^ 48 ∧ bxP + 16 ≤ 2 ^ 48 ∧
    Apart dstP (8 * (1 : BitVec 64).toNat) srcP (8 * (1 : BitVec 64).toNat) ∧
    Apart bxP 16 dstP (8 * (1 : BitVec 64).toNat) ∧ Apart bxP 16 srcP (8 * (1 : BitVec 64).toNat) ∧
    Apart ((s0.regs 28).toNat + 16) 8 dstP (8 * (1 : BitVec 64).toNat) ∧ Apart ((s0.regs 28).toNat + 16) 8 bxP 16 ∧
    blockSize (8 * (2 : BitVec 64).toNat) true ≤ 0x100 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_,
    by decide, ?_, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, inv0, ?_,
    ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_mk]; exact Or.inr (Or.inl ⟨rfl, by decide⟩)
  · rw [addr_wb]; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rw [addr_mv]; exact Or.inl ⟨rfl, dstP, srcP, by decide⟩
  · intro t; rw [addr_mv]; exact Or.inl ⟨rfl, t, srcP, rfl⟩
  · intro r hr; simp only [liveL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [Outside, outside_cons, outside_nil, and_true] <;> decide
  · exact ⟨(dstP, dstP + 8), by simp [liveL], by decide, by decide⟩
  · exact ⟨(srcP, srcP + 8), by simp [liveL], by decide, by decide⟩
  · exact ⟨(bxP, bxP + 16), by simp [liveL], by decide, by decide⟩
  all_goals (simp only [Apart]; decide)

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a live set, a budget and a
call of `Chain(dst, src, bx, 2)` (one-word slices) satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State),
    MemmoveLive (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 dstP, 1, 1,
      BitVec.ofNat 64 srcP, 1, 1, BitVec.ofNat 64 bxP, 2] s ∧
    (GuardOK s 4144 ∧ StackOK s 4152 72 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4152) 4224 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4152) 4224 ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ s.mem.accessible flagAddr 4 false = true ∧
    Outside u64Type 16 R.rt ∧
    0 < (2 : BitVec 64).toNat ∧ (2 : BitVec 64).toNat < 2 ^ 40 ∧ 0 < (1 : BitVec 64).toNat ∧ 0 < (1 : BitVec 64).toNat ∧
    (1 : BitVec 64).toNat < 2 ^ 40 ∧ (1 : BitVec 64).toNat < 2 ^ 40 ∧
    R.ok (Extracted.program.contractAddr "runtime.makeslice") [u64Type, (2 : BitVec 64).toNat, (2 : BitVec 64).toNat] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.ok (Extracted.program.contractAddr "runtime.memmove") [dstP, srcP, 8 * min (1 : BitVec 64).toNat (1 : BitVec 64).toNat] ∧
    (∀ t, R.ok (Extracted.program.contractAddr "runtime.memmove") [t, srcP, 8 * min (1 : BitVec 64).toNat (2 : BitVec 64).toNat]) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4152, s.sp.toNat + 72)]) ∧
    InRanges dstP (8 * (1 : BitVec 64).toNat) L ∧ InRanges srcP (8 * (1 : BitVec 64).toNat) L ∧ InRanges bxP 16 L ∧
    s.mem.accessible dstP (8 * (1 : BitVec 64).toNat) true = true ∧ s.mem.accessible srcP (8 * (1 : BitVec 64).toNat) false = true ∧
    s.mem.accessible bxP 16 true = true ∧
    dstP + 8 * (1 : BitVec 64).toNat ≤ 2 ^ 48 ∧ srcP + 8 * (1 : BitVec 64).toNat ≤ 2 ^ 48 ∧ bxP + 16 ≤ 2 ^ 48 ∧
    Apart dstP (8 * (1 : BitVec 64).toNat) srcP (8 * (1 : BitVec 64).toNat) ∧
    Apart bxP 16 dstP (8 * (1 : BitVec 64).toNat) ∧ Apart bxP 16 srcP (8 * (1 : BitVec 64).toNat) ∧
    Apart ((s.regs 28).toNat + 16) 8 dstP (8 * (1 : BitVec 64).toNat) ∧ Apart ((s.regs 28).toNat + 16) 8 bxP 16 ∧
    blockSize (8 * (2 : BitVec 64).toNat) true ≤ b) :=
  ⟨implAt, R, 0x100, liveL, ret, s0, by rw [addr_mv]; exact model_mv, by rw [addr_mk]; exact model_mk,
    by rw [addr_wb]; exact model_wb, hret, setup, pre⟩

/-- So the guarantee is reached: `Chain(dst, src, bx, 2)` stores a fresh array `t` (apart from the three
caller objects) in `bx.P` and `2` in `bx.N`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ ∃ t : Nat, s'.mem.readLE bxP 8 = t ∧ s'.mem.readLE (bxP + 8) 8 = 2 ∧
      Apart t 16 dstP 8 ∧ Apart t 16 srcP 8 ∧ Apart t 16 bxP 16 :=
  (correctness implAt R 0x100 liveL (BitVec.ofNat 64 dstP) 1 1 (BitVec.ofNat 64 srcP) 1 1 (BitVec.ofNat 64 bxP) 2
    (by rw [addr_mv]; exact model_mv) (by rw [addr_mk]; exact model_mk)
    (by rw [addr_wb]; exact model_wb) ret hret s0 setup pre).mono
    fun _ ⟨habi, t, h1, h2, h3, h4, h5, h6, _⟩ => by
      have hbs : blockSize (8 * (2 : BitVec 64).toNat) true = 16 := by decide
      rw [hbs] at h3 h4 h5 h6
      exact ⟨habi, t, h1, h2, h4, h5, h6⟩

end Witness

end Proof
