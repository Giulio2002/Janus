import Janus
import Extracted

/-!
# `AppendOne(s []uint64, x uint64) []uint64` on amd64: `append(s, x)`

**Guarantee.** As for arm64 (`examples/proofs/AppendOne.lean`), with the slice in `RAX, RBX, RCX`,
`x` in `RDI`, the stack window `[RSP-4176, RSP+40)`, and `runtime.growslice` given by
`GrowsliceContract64`: with room left, word `len` becomes `x` and nothing else changes; when full
(also for a nil slice), the result is a fresh array of capacity `growCap8 (len+1) cap` inside `rt`
holding the old elements, then `x`, then zeros.

**What is assumed.** Only the contract hypothesis `hg` (docs/RUNTIME-CONTRACTS.md).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Proof

/-- The address of `uint64`'s type descriptor, the element type AppendOne passes to
`runtime.growslice` (the `LEA` before the call loads it): the extraction's only data object. -/
def u64Type : Nat := dataBase Extracted.program 0

/-- The precondition. When the slice is full, the runtime is ready (`H`) for the call
`growslice(ptr, len+1, cap, 1, uint64)` from AppendOne's frame (`RSP - 80` at the callee). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (ptr len cap : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 4176 40 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4176) 4216 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
    len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 39 ∧
    ptr.toNat + 8 * cap.toNat ≤ 2 ^ 48 ∧
    Spec.Disjoint ptr.toNat (8 * cap.toNat) ((s.regs 4).toNat - 4176) 4216 ∧
    (len.toNat < cap.toNat → s.mem.accessible ptr.toNat (8 * cap.toNat) true = true) ∧
    (0 < len.toNat → s.mem.accessible ptr.toNat (8 * len.toNat) false = true) ∧
    (cap.toNat ≤ len.toNat →
      H [ptr.toNat, len.toNat + 1, cap.toNat, 1, u64Type] (s.regs 14).toNat ((s.regs 4).toNat - 80)
        (rtView rt s.mem))

/-- Word `i` past the appended one is still zero after the store of word `L`. -/
theorem zero_after_store {m : Arm64.Memory} {P L C x i A : Nat}
    (hz : ZeroBytes m (P + 8 * (L + 1)) (8 * C - 8 * (L + 1))) (hA : A = P + 8 * L) (h1 : L < i)
    (h2 : i < C) : (m.writeLE A 8 x).readLE (P + 8 * i) 8 = 0 := by
  rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    show P + 8 * i = P + 8 * (L + 1) + 8 * (i - (L + 1)) by omega]
  exact hz.readLE (by omega)

/-- Word `i < L` of the copy is the old word, after the store of word `L`. -/
theorem copy_after_store {m m₀ : Arm64.Memory} {P Q L x i A : Nat}
    (hcp : ∀ j, j < 8 * L → m.bytes (P + j) = m₀.bytes (Q + j)) (hA : A = P + 8 * L) (hi : i < L) :
    (m.writeLE A 8 x).readLE (P + 8 * i) 8 = m₀.readLE (Q + 8 * i) 8 := by
  rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  exact readLE_of_copy hcp (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (ptr len cap x : BitVec 64)
    (hg : GrowsliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [ptr, len, cap, x]
      (Pre rt H ptr len cap)
      (fun s s' => (s'.regs 3).toNat = len.toNat + 1 ∧
        (len.toNat < cap.toNat → s'.regs 0 = ptr ∧ s'.regs 1 = cap ∧
          s'.mem.readLE (ptr.toNat + 8 * len.toNat) 8 = x.toNat ∧
          MemFrame s.mem s'.mem [(ptr.toNat + 8 * len.toNat, ptr.toNat + 8 * len.toNat + 8),
            ((s.regs 4).toNat - 4176, (s.regs 4).toNat + 40)]) ∧
        (cap.toNat ≤ len.toNat →
          (s'.regs 1).toNat = growCap8 (len.toNat + 1) cap.toNat ∧
          InRanges (s'.regs 0).toNat (8 * growCap8 (len.toNat + 1) cap.toNat) rt ∧
          (s'.regs 0).toNat % 8 = 0 ∧
          s'.mem.accessible (s'.regs 0).toNat (8 * growCap8 (len.toNat + 1) cap.toNat) true = true ∧
          (∀ i, i < len.toNat →
            s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = s.mem.readLE (ptr.toNat + 8 * i) 8) ∧
          s'.mem.readLE ((s'.regs 0).toNat + 8 * len.toNat) 8 = x.toNat ∧
          (∀ i, len.toNat < i → i < growCap8 (len.toNat + 1) cap.toNat →
            s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
          MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4176, (s.regs 4).toNat + 40)]))) := by
  intro ret hret s hs ⟨hsg, ⟨hb, ha, hw⟩, hd, hout, hal, hlc, hc, hpb, hdj, hwr, hrd, hHf⟩
  janus64_intro hs
  janus_eval_nat h_ut : u64Type
  have hgl := hsg.load
  have hgb := hsg.below
  have hnw2 := hsg.noWrap
  have hgr := hsg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hb ha hw hout hal hdj ⊢
  janus64_data hd [hw]
  by_cases hl : len.toNat < cap.toNat
  · have hw' := hwr hl
    janus64_run
    exact ⟨fun _ => by janus_frame, fun h => absurd h (by omega)⟩
  · have hle := le_growCap8 (len.toNat + 1) cap.toNat
    have hH := hHf (by omega)
    rw [h_ut] at hH
    clear hHf
    by_cases h0 : len.toNat = 0
    · janus64_run until [Extracted.entry + 0x31] calls [hg.empty]
      have hdj2 := InRanges.disjoint ‹InRanges _ _ rt› hout
      janus64_run
      have hin := ‹InRanges _ (8 * growCap8 _ _) rt›
      have hacc := ‹s.mem.accessible _ (8 * growCap8 _ _) true = true›
      have h8 := ‹16 ≤ 8 * growCap8 _ _ ∨ _ → _›
      have hz := ‹ZeroBytes _ _ (8 * growCap8 _ _ - _)›
      refine ⟨fun h => absurd h hl, fun _ => ⟨hin, h8 (Or.inr (by omega)), hacc,
        fun i hi => absurd hi (by omega), fun i h1 h2 => ?_, by janus_frame⟩⟩
      exact zero_after_store hz (by omega) h1 h2
    · have hr := hrd (by omega)
      janus64_run until [Extracted.entry + 0x31] calls [hg.withOld]
      have hdj2 := InRanges.disjoint ‹InRanges _ _ rt› hout
      janus64_run
      have hin := ‹InRanges _ (8 * growCap8 _ _) rt›
      have hacc := ‹s.mem.accessible _ (8 * growCap8 _ _) true = true›
      have h8 := ‹16 ≤ 8 * growCap8 _ _ ∨ _ → _›
      have hz := ‹ZeroBytes _ _ (8 * growCap8 _ _ - _)›
      have hcp := ‹∀ i, i < 8 * _ → _›
      refine ⟨fun h => absurd h hl, fun _ => ⟨hin, h8 (Or.inr (by omega)), hacc,
        fun i hi => ?_, fun i h1 h2 => ?_, by janus_frame⟩⟩
      · rw [copy_after_store hcp (by omega) hi]
        janus64_simp
      · exact zero_after_store hz (by omega) h1 h2

/-! ## Non-vacuity witness

`janus64_growslice_witness` (`Janus/Contracts/AllocWitness.lean`) builds a concrete
`runtime.growslice` at the contract address (for `append` to an empty `[]uint64`), the
runtime-owned ranges `rt` (the heap), the readiness predicate `H`, and proves the contract `hgrow`
for them. Below, a concrete call state of `AppendOne(nil, 0, 0, 5)` satisfies the whole
precondition and the call returns the grown slice the theorem describes. -/

namespace Witness

janus64_growslice_witness

open GrowW (impl rt H linked hgrow)
open Janus.Contracts.AllocWitness (heap)

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
  { regs := fun i => if i = 7 then 5 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4176, 4176 + 40, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [0, 0, 0, 5] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [(0 : BitVec 64).toNat, (0 : BitVec 64).toNat + 1, (0 : BitVec 64).toNat, 1, u64Type]
    (s0.regs 14).toNat ((s0.regs 4).toNat - 80) (rtView rt s0.mem) := by
  have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
  refine ⟨⟨by rw [rtView_accessible]; decide, Janus.Contracts.AllocWitness.heapZero_of_bytes _ _ fun i hi => ?_⟩,
    0, u64Type, rfl⟩
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
theorem pre : Pre rt H 0 0 0 s0 :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, GrowW.rt, Janus.Contracts.AllocWitness.allocRt, outside_cons, outside_nil, List.map]; decide,
    by decide, by decide, by decide, by decide, by simp [Spec.Disjoint],
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => hH⟩

def cAddr : Nat := Extracted.program.contractAddr "runtime.growslice"
def tyA : Nat := janus_eval% u64Type

/-- The call state at `runtime.growslice`'s entry (`growslice(nil, 1, 0, 1, uint64)`, callee `RSP` 80 below). -/
def wsCall : Janus.Amd64.State :=
  { regs := fun i => if i = 3 then 1 else if i = 7 then 1 else if i = 6 then BitVec.ofNat 64 tyA
      else if i = 4 then BitVec.ofNat 64 (sp0 - 80) else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 cAddr, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := s0.mem }

@[reducible] def grSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : Janus.Amd64.State) : Prop :=
  GrowslicePre64 4096 s_c ∧ Contracts.Ready64 H rt (growsliceArgs64 s_c) s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : grSite rt H wsCall := by
  have h := hH
  have hpt : u64Type = tyA := by unfold tyA; decide
  rw [hpt] at h
  refine ⟨⟨⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, (by simp only [calleeStack64, outside_cons, outside_nil]; decide)⟩,
    fun h => absurd h (by decide)⟩, ?_⟩
  exact h

/-- The theorem fires: `AppendOne(nil, 0, 0, 5)` returns a slice of length 1 and capacity
`growCap8 1 0` in `rt`, holding `5` first. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    (s'.regs 3).toNat = (0 : BitVec 64).toNat + 1 ∧
        ((0 : BitVec 64).toNat < (0 : BitVec 64).toNat → s'.regs 0 = (0 : BitVec 64) ∧ s'.regs 1 = (0 : BitVec 64) ∧
          s'.mem.readLE ((0 : BitVec 64).toNat + 8 * (0 : BitVec 64).toNat) 8 = (5 : BitVec 64).toNat ∧
          MemFrame s0.mem s'.mem [((0 : BitVec 64).toNat + 8 * (0 : BitVec 64).toNat, (0 : BitVec 64).toNat + 8 * (0 : BitVec 64).toNat + 8),
            ((s0.regs 4).toNat - 4176, (s0.regs 4).toNat + 40)]) ∧
        ((0 : BitVec 64).toNat ≤ (0 : BitVec 64).toNat →
          (s'.regs 1).toNat = growCap8 ((0 : BitVec 64).toNat + 1) (0 : BitVec 64).toNat ∧
          InRanges (s'.regs 0).toNat (8 * growCap8 ((0 : BitVec 64).toNat + 1) (0 : BitVec 64).toNat) rt ∧
          (s'.regs 0).toNat % 8 = 0 ∧
          s'.mem.accessible (s'.regs 0).toNat (8 * growCap8 ((0 : BitVec 64).toNat + 1) (0 : BitVec 64).toNat) true = true ∧
          (∀ i, i < (0 : BitVec 64).toNat →
            s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = s0.mem.readLE ((0 : BitVec 64).toNat + 8 * i) 8) ∧
          s'.mem.readLE ((s'.regs 0).toNat + 8 * (0 : BitVec 64).toNat) 8 = (5 : BitVec 64).toNat ∧
          (∀ i, (0 : BitVec 64).toNat < i → i < growCap8 ((0 : BitVec 64).toNat + 1) (0 : BitVec 64).toNat →
            s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
          MemFrame s0.mem s'.mem (rt ++ [((s0.regs 4).toNat - 4176, (s0.regs 4).toNat + 40)])) :=
  correctness impl rt H 0 0 0 5 hgrow ret hret s0 setup pre

/-- The hypotheses are satisfiable: a `growslice` meeting the contract (`hgrow`), runtime ranges, a
readiness predicate, and a call state of `AppendOne(nil, 0, 0, 5)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat)
    (s : Janus.Amd64.State),
    GrowsliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 0, 0, 5] s ∧
    Pre rt H 0 0 0 s ∧
    (∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite rt H s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
    (s'.regs 3).toNat = (0 : BitVec 64).toNat + 1 ∧
        ((0 : BitVec 64).toNat < (0 : BitVec 64).toNat → s'.regs 0 = (0 : BitVec 64) ∧ s'.regs 1 = (0 : BitVec 64) ∧
          s'.mem.readLE ((0 : BitVec 64).toNat + 8 * (0 : BitVec 64).toNat) 8 = (5 : BitVec 64).toNat ∧
          MemFrame s.mem s'.mem [((0 : BitVec 64).toNat + 8 * (0 : BitVec 64).toNat, (0 : BitVec 64).toNat + 8 * (0 : BitVec 64).toNat + 8),
            ((s.regs 4).toNat - 4176, (s.regs 4).toNat + 40)]) ∧
        ((0 : BitVec 64).toNat ≤ (0 : BitVec 64).toNat →
          (s'.regs 1).toNat = growCap8 ((0 : BitVec 64).toNat + 1) (0 : BitVec 64).toNat ∧
          InRanges (s'.regs 0).toNat (8 * growCap8 ((0 : BitVec 64).toNat + 1) (0 : BitVec 64).toNat) rt ∧
          (s'.regs 0).toNat % 8 = 0 ∧
          s'.mem.accessible (s'.regs 0).toNat (8 * growCap8 ((0 : BitVec 64).toNat + 1) (0 : BitVec 64).toNat) true = true ∧
          (∀ i, i < (0 : BitVec 64).toNat →
            s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = s.mem.readLE ((0 : BitVec 64).toNat + 8 * i) 8) ∧
          s'.mem.readLE ((s'.regs 0).toNat + 8 * (0 : BitVec 64).toNat) 8 = (5 : BitVec 64).toNat ∧
          (∀ i, (0 : BitVec 64).toNat < i → i < growCap8 ((0 : BitVec 64).toNat + 1) (0 : BitVec 64).toNat →
            s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
          MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4176, (s.regs 4).toNat + 40)])) :=
  ⟨impl, rt, H, ret, s0, hgrow, hret, setup, pre, ⟨wsCall, rfl, wsCall_pre⟩, returns⟩

end Witness

end Proof
