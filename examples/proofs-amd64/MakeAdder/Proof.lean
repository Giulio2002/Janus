import Janus
import Extracted

/-!
# `MakeAdder(a uint64) func(uint64) uint64` on amd64: creating an escaping closure

**Guarantee.** For every `a`, every list `rt` of runtime-owned ranges and **every**
implementation of `runtime.newobject` satisfying `NewobjectContract64`
(`Janus/Contracts/AllocAmd64.lean`), and every Go call state in which the stack-growth prologue
falls through, `RSP` is 8-aligned, the stack window `[RSP-4128, RSP+24)` is writable and outside
`rt`, and memory holds the read-only data (the closure struct's type descriptor): the call
returns, obeys the ABI, and `fv = RAX` is a fresh funcval: `[fv, fv+16)` inside `rt`, writable,
16-byte aligned, whose code word is `MakeAdder.func1` (`FuncvalIs`) and whose captured variable
is `a` (`ClosureCtx`); memory outside `rt` and the stack window is unchanged. The closure
escapes (it is the result), so its funcval comes from `runtime.newobject`, not the frame.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Spec

namespace Proof

/-- The address of the closure's type descriptor, the argument MakeAdder passes to
`runtime.newobject` (the `LEA` before the call loads it): the extraction's only data object. -/
def fvType : Nat := dataBase Extracted.program 0

set_option maxRecDepth 20000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (a : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4128 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4128) 4152 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        H [fvType] (s.regs 14).toNat ((s.regs 4).toNat - 32) (rtView rt s.mem))
      (fun s s' => InRanges (s'.regs 0).toNat 16 rt ∧ (s'.regs 0).toNat % 16 = 0 ∧
        s'.mem.accessible (s'.regs 0).toNat 16 true = true ∧
        FuncvalIs s'.mem (s'.regs 0) (segAddr Extracted.program "example.com/basic.MakeAdder.func1") ∧
        ClosureCtx s'.mem (s'.regs 0) [a] ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, hH⟩
  janus64_intro hs
  janus_eval_nat h_ft : fvType
  rw [h_ft] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal ⊢
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x1f] calls [hnew.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 16 rt› hout
  janus64_run
  refine ⟨‹_›, ‹_›, ‹_›, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · janus64_simp
    exact accessible_sub ‹Arm64.Memory.accessible s.mem _ 16 true = true› (by simp) (by omega) (by omega)
  · janus64_simp
  · janus64_simp
    simp only [List.length_cons, List.length_nil]
    exact accessible_sub ‹Arm64.Memory.accessible s.mem _ 16 true = true› (by simp) (by omega) (by omega)
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    obtain rfl : i = 0 := by omega
    janus64_simp
    rfl
  · janus_frame


/-! ## Non-vacuity witness

`janus64_alloc_witness` (`Janus/Contracts/AllocWitness.lean`) builds a concrete allocator at
`runtime.newobject`'s address, the runtime-owned ranges `rt` (the heap and the closure's type descriptor),
the readiness predicate `H`, and proves the contract `hnew` for them. Below, a concrete call state
of `MakeAdder(7)` satisfies the whole precondition and the call returns the object the theorem
describes. -/

namespace Witness

janus64_alloc_witness types := [fvType]

open AllocW (impl rt H linked hnew)
open Janus.Contracts.AllocWitness (heap)

def tyA : Nat := janus_eval% fvType
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
  { regs := fun i => if i = 0 then 7 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4128, 4128 + 24, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [7] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; obtain rfl : i = 0 := by omega
                                      rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [fvType] (s0.regs 14).toNat ((s0.regs 4).toNat - 32) (rtView rt s0.mem) := by
  have hpt : fvType = tyA := by unfold tyA; decide
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
    H [fvType] (s0.regs 14).toNat ((s0.regs 4).toNat - 32) (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, AllocW.rt, Janus.Contracts.AllocWitness.allocRt, AllocW.tys, outside_cons, outside_nil, List.map]; decide,
    by decide, hH⟩

def cAddr : Nat := Extracted.program.contractAddr "runtime.newobject"

/-- The call state at `runtime.newobject`'s entry (argument `fvType`, callee `SP` 32 below). -/
def wsCall : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 4 then BitVec.ofNat 64 (sp0 - 32)
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 cAddr, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := s0.mem }

@[reducible] def nwSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : Janus.Amd64.State) : Prop :=
  NewobjectPre64 4096 s_c ∧ Contracts.Ready64 H rt [(s_c.regs 0).toNat] s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : nwSite rt H wsCall := by
  have h := hH
  have hpt : fvType = tyA := by unfold tyA; decide
  rw [hpt] at h
  refine ⟨⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, by decide⟩, ?_⟩
  exact h

/-- The theorem fires: for this call and this allocator, `MakeAdder(7)` returns a fresh closure
in `rt`. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    InRanges (s'.regs 0).toNat 16 rt ∧ (s'.regs 0).toNat % 16 = 0 ∧
    s'.mem.accessible (s'.regs 0).toNat 16 true = true ∧
    FuncvalIs s'.mem (s'.regs 0) (segAddr Extracted.program "example.com/basic.MakeAdder.func1") ∧
    ClosureCtx s'.mem (s'.regs 0) [(7 : BitVec 64)] ∧
    MemFrame s0.mem s'.mem (rt ++ [((s0.regs 4).toNat - 4128, (s0.regs 4).toNat + 24)]) :=
  correctness impl rt H 7 hnew ret hret s0 setup pre

/-- The hypotheses are satisfiable: an allocator meeting the contract (`hnew`), runtime ranges, a
readiness predicate, and a call state of `MakeAdder(7)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat)
    (s : Janus.Amd64.State),
    NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [7] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 4128 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside ((s.regs 4).toNat - 4128) 4152 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
      H [fvType] (s.regs 14).toNat ((s.regs 4).toNat - 32) (rtView rt s.mem)) ∧
    (∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      nwSite rt H s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
    InRanges (s'.regs 0).toNat 16 rt ∧ (s'.regs 0).toNat % 16 = 0 ∧
    s'.mem.accessible (s'.regs 0).toNat 16 true = true ∧
    FuncvalIs s'.mem (s'.regs 0) (segAddr Extracted.program "example.com/basic.MakeAdder.func1") ∧
    ClosureCtx s'.mem (s'.regs 0) [(7 : BitVec 64)] ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 24)]) :=
  ⟨impl, rt, H, ret, s0, hnew, hret, setup, pre, ⟨wsCall, rfl, wsCall_pre⟩, returns⟩

end Witness

end Proof
