import Janus
import Extracted

/-!
# `NewPair(a, b uint64) *Pair` built with `GOEXPERIMENT=sizespecializedmalloc` (amd64)

As on arm64: the allocation is `runtime.mallocgcSmallNoScanSC2(16, type:Pair, true)`, left out
(`--contract 'runtime.mallocgcSmallNoScanSC*'`) and assumed as `MallocgcSmallNoScanSCContract64 2`
(`Janus/Contracts/MallocSCAmd64.lean`). The call returns a 16-byte-aligned, writable object
inside `rt` holding `a` and `b`; memory changes only in `rt` and the stack window
`[RSP-4144, RSP+24)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Proof

/-- `Pair`'s type descriptor (the `LEAQ` at `NewPair+0x1d`): the extraction's only data object. -/
def pairType : Nat := dataBase Extracted.program 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (a b : BitVec 64)
    (hsc : MallocgcSmallNoScanSCContract64 2 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgcSmallNoScanSC2") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4144) 4168 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        H [16, pairType, 1] (s.regs 14).toNat ((s.regs 4).toNat - 48) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 16 true = true ∧
        s'.mem.readLE ptr 8 = a.toNat ∧ s'.mem.readLE (ptr + 8) 8 = b.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, hH⟩
  janus64_intro hs
  janus_eval_nat h_pt : pairType
  rw [h_pt] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal ⊢
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x2e] calls [hsc]
  have hdj := InRanges.disjoint ‹InRanges _ 16 rt› hout
  janus64_run
  rename_i ptr junk f x yh m zh kr hfr hin hle hacc h8 h16 hz htrue
  have hp := ptr.isLt
  refine ⟨_, rfl, hin, h16, hacc, ?_, ?_, ?_⟩
  · rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt a.isLt
  · rw [Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt b.isLt
  · refine MemFrame.writeLE_inRanges ?_ _ (InRanges.append_left (hin.sub (by omega) (by omega)) _)
    refine MemFrame.writeLE_inRanges ?_ _ (InRanges.append_left (hin.sub (Nat.le_refl _) (by omega)) _)
    refine MemFrame.trans (rs := [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 24)]) (by janus_frame) hfr
      fun x n hx => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true] at hx ⊢
    obtain ⟨hr, hw'⟩ := hx
    exact ⟨hw', hr, by omega⟩


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The toy allocator of `Janus.Contracts.AllocSatAmd64` (`mov $0x10000, %eax; ret`) at
`runtime.mallocgcSmallNoScanSC2`'s address, its `rt` and readiness `AllocSat.Hmalloc`, and a
concrete call of `NewPair(3, 5)` satisfying the precondition. -/

namespace Witness

open Janus.Contracts.AllocSat (heap rt Hmalloc HeapReady fresh_heap le_blockSize)

def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.mallocgcSmallNoScanSC2")
def implAt : List Amd64.Segment :=
  [{ name := "witness.mallocgcSmallNoScanSC2", base := cA, bytes := AllocSatAmd64.heapCode }]
def linked : Amd64.Program := Extracted.program.link implAt

theorem addr : Extracted.program.contractAddr "runtime.mallocgcSmallNoScanSC2" = cA := by decide

theorem model : MallocgcSmallNoScanSCContract64 2 (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.mallocgcSmallNoScanSC2") rt 4096 Hmalloc := by
  rw [addr]
  intro s hpc ⟨⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, sz, typ, nz, hargs, hsz⟩, _⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, -, -⟩ := hargs
  change ReachesRet linked _ s _
  janus64_run
  refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, _, _, AllocSatAmd64.ret_of s _ [BitVec.ofNat 64 heap]
    (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
  rw [show (BitVec.ofNat 64 heap).toNat = heap from rfl]
  exact fresh_heap _ _ hr (le_blockSize _ _)
    (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def dat : DataSegment := Extracted.data.head!
def dA : Nat := janus_eval% dat.base
def dlen : Nat := janus_eval% dat.bytes.length

/-- The data bytes, and the return address `ret = 0x1000` at `[RSP]`. -/
def bytes (a : Nat) : Arm64.Byte :=
  if dA ≤ a ∧ a < dA + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - dA) 0)
  else if a = sp0 + 1 then 0x10 else 0

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then 3 else if i = 3 then 5 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4144, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨dA, dlen, false⟩,
      ⟨heap, 0x10000, true⟩]⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [3, 5] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide

theorem hH : Hmalloc [16, pairType, 1] (s0.regs 14).toNat ((s0.regs 4).toNat - 48) (rtView rt s0.mem) := by
  refine ⟨⟨by decide, fun i hi => ?_⟩, 16, pairType, 1, rfl, by decide⟩
  show (if _ then bytes (heap + i) else 0) = 0
  split
  · have h1 : ¬(dA ≤ heap + i ∧ heap + i < dA + dlen) := by simp only [dA, heap, dlen]; omega
    simp only [bytes]; rw [ite_cond_eq_false _ _ (eq_false h1), ite_cond_eq_false _ _ (eq_false (by simp only [heap, sp0]; omega))]
  · rfl

theorem pre : StackGuardOK s0 0 ∧ StackWritable s0 4144 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4144) 4168 rt ∧ (s0.regs 4).toNat % 8 = 0 ∧
    Hmalloc [16, pairType, 1] (s0.regs 14).toNat ((s0.regs 4).toNat - 48) (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, by decide, hH⟩

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat)
    (s : Amd64.State), MallocgcSmallNoScanSCContract64 2 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgcSmallNoScanSC2") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 5] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside ((s.regs 4).toNat - 4144) 4168 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
      H [16, pairType, 1] (s.regs 14).toNat ((s.regs 4).toNat - 48) (rtView rt s.mem)) :=
  ⟨implAt, rt, Hmalloc, ret, s0, model, hret, setup, pre⟩

/-- So the guarantee is reached: `NewPair(3, 5)` returns a fresh object holding 3 and 5. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧
      s'.mem.readLE ptr 8 = 3 ∧ s'.mem.readLE (ptr + 8) 8 = 5 :=
  (correctness implAt rt Hmalloc 3 5 model ret hret s0 setup pre).mono
    fun _ ⟨habi, ptr, h0, hin, _, _, ha, hb, _⟩ => ⟨habi, ptr, h0, hin, ha, hb⟩

end Witness

end Proof
