import Janus
import Extracted

/-!
# `NewPair(a, b uint64) *Pair` on amd64: a fresh heap object holding `a` and `b`

**Guarantee.** For all `a`, `b`, every list `rt` of runtime-owned ranges and **every**
implementation of `runtime.newobject` satisfying `NewobjectContract64`
(`Janus/Contracts/AllocAmd64.lean`), and every Go call state in which the stack-growth prologue
falls through, `RSP` is 8-aligned, the stack window `[RSP-4128, RSP+24)` (frame, return-address
slot, 4096 bytes for the runtime, two spill slots) is writable and outside `rt`, and memory holds
the read-only data (the `Pair` type descriptor): the call returns, obeys the ABI, and `RAX` is a
pointer `ptr` with `[ptr, ptr+16)` inside `rt` (fresh: disjoint from all caller data outside it),
writable and 16-byte aligned, holding `a` and `b`; memory outside `rt` and the stack window is
unchanged.

**What is assumed.** Only the contract hypothesis `hnew` for the code linked at
`runtime.newobject`, which is not extracted (`--contract`); see docs/RUNTIME-CONTRACTS.md.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Proof

/-- The address of `Pair`'s type descriptor, the argument NewPair passes to `runtime.newobject`
(the `LEA` at `NewPair+0x18` loads it): the extraction's only data object. -/
def pairType : Nat := dataBase Extracted.program 0

set_option maxRecDepth 20000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (a b : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4128 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4128) 4152 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        H [pairType] (s.regs 14).toNat ((s.regs 4).toNat - 32) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 16 true = true ∧
        s'.mem.readLE ptr 8 = a.toNat ∧ s'.mem.readLE (ptr + 8) 8 = b.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 24)])) := by
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
  janus64_run until [Extracted.entry + 0x25] calls [hnew.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 16 rt› hout
  janus64_run
  refine ⟨_, rfl, ‹_›, ‹_›, ‹_›, ?_, ?_, ?_⟩
  · janus64_simp
  · janus64_simp
  · janus_frame

/-! ## Non-vacuity witness

`janus64_alloc_witness` (`Janus/Contracts/AllocWitness.lean`) builds a concrete allocator at
`runtime.newobject`'s address, the runtime-owned ranges `rt` (the heap and `Pair`'s type descriptor),
the readiness predicate `H`, and proves the contract `hnew` for them. Below, a concrete call state
of `NewPair(3, 5)` satisfies the whole precondition and the call returns the object the theorem
describes. -/

namespace Witness

janus64_alloc_witness types := [pairType]

open AllocW (impl rt H linked hnew)
open Janus.Contracts.AllocWitness (heap)

def tyA : Nat := janus_eval% pairType
def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then 3 else if i = 3 then 5 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4128, 4128 + 24, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [3, 5] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [pairType] (s0.regs 14).toNat ((s0.regs 4).toNat - 32) (rtView rt s0.mem) := by
  have hpt : pairType = tyA := by unfold tyA; decide
  rw [hpt]
  have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
  refine Janus.Contracts.AllocWitness.allocH64_intro
    (Janus.Contracts.AllocWitness.inRanges_ty (tys := AllocW.tys) (a := tyA) (by decide)) (by decide)
    (by rw [rtView_accessible]; decide) ?_
  refine Janus.Contracts.AllocWitness.heapZero_of_bytes _ _ fun i hi => ?_
  have h1 : dsegs.find? (fun d => decide (d.base ≤ heap + i ∧ heap + i < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have := hbase d hd
    have hh : heap + i < 0x20000 := by simp only [heap]; omega
    simp only [decide_eq_true_eq]
    omega
  have h3 : heap + i ≠ sp0 + 2 := by simp only [heap, sp0]; omega
  show bytes (heap + i) = 0
  simp only [bytes, if_neg h3, h1]

set_option maxRecDepth 100000 in
theorem pre : StackGuardOK s0 0 ∧ StackWritable s0 4128 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4128) 4152 rt ∧ (s0.regs 4).toNat % 8 = 0 ∧
    H [pairType] (s0.regs 14).toNat ((s0.regs 4).toNat - 32) (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, AllocW.rt, Janus.Contracts.AllocWitness.allocRt, AllocW.tys, outside_cons, outside_nil, List.map]; decide,
    by decide, hH⟩

/-- The hypotheses are satisfiable: an allocator meeting the contract (`hnew`), runtime ranges, a
readiness predicate, and a call state of `NewPair(3, 5)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat)
    (s : Janus.Amd64.State),
    NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 5] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 4128 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside ((s.regs 4).toNat - 4128) 4152 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
      H [pairType] (s.regs 14).toNat ((s.regs 4).toNat - 32) (rtView rt s.mem)) :=
  ⟨impl, rt, H, ret, s0, hnew, hret, setup, pre⟩

/-- The theorem fires: for this call and this allocator, `NewPair(3, 5)` returns a fresh object in
`rt` holding 3 and 5. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
      s'.mem.accessible ptr 16 true = true ∧
      s'.mem.readLE ptr 8 = (3 : BitVec 64).toNat ∧ s'.mem.readLE (ptr + 8) 8 = (5 : BitVec 64).toNat ∧
      MemFrame s0.mem s'.mem (rt ++ [((s0.regs 4).toNat - 4128, (s0.regs 4).toNat + 24)]) :=
  correctness impl rt H 3 5 hnew ret hret s0 setup pre

end Witness

end Proof
