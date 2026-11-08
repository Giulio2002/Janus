import Janus
import Extracted

/-!
# `MakeSlice(n int) []uint64` on amd64: a fresh zeroed slice of `n` words

**Guarantee.** For every `n ≤ 2^45`, every `rt` and **every** implementation of
`runtime.makeslice` satisfying `MakesliceContract64`, and every Go call state in which the
prologue falls through, `RSP` is 8-aligned, `[RSP-4136, RSP+16)` is writable and outside `rt`, and
the read-only data is loaded: the call returns, obeys the ABI, `RBX = RCX = n` (length and
capacity), and for `n > 0` the array `[RAX, RAX+8n)` lies inside `rt` (fresh), is writable,
8-byte aligned and all zero. Memory outside `rt` and the stack window is unchanged.

**What is assumed.** Only the contract hypothesis `hmk` (docs/RUNTIME-CONTRACTS.md).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Proof

/-- The address of `uint64`'s type descriptor, the element type MakeSlice passes to
`runtime.makeslice` (the `LEA` before the call loads it): the extraction's only data object. -/
def u64Type : Nat := dataBase Extracted.program 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (n : BitVec 64)
    (hmk : MakesliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [n]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4136 16 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4152 rt ∧ (s.regs 4).toNat % 8 = 0 ∧ n.toNat ≤ 2 ^ 45 ∧
        H [u64Type, n.toNat, n.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem))
      (fun s s' => s'.regs 3 = n ∧ s'.regs 1 = n ∧
        (0 < n.toNat → InRanges (s'.regs 0).toNat (8 * n.toNat) rt ∧ (s'.regs 0).toNat % 8 = 0 ∧
          s'.mem.accessible (s'.regs 0).toNat (8 * n.toNat) true = true ∧
          ∀ i, i < n.toNat → s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 16)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, hn, hH⟩
  janus64_intro hs
  janus_eval_nat h_ut : u64Type
  rw [h_ut] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal ⊢
  janus64_data hd [hw]
  by_cases h0 : n.toNat = 0
  · janus64_run calls [hmk]
    exact ⟨fun h => absurd h (by omega), by janus_frame⟩
  · janus64_run calls [hmk.pos]
    have hin := ‹InRanges _ (blockSize _ _) rt›
    have hacc := ‹Arm64.Memory.accessible s.mem _ (blockSize _ _) true = true›
    have h8 := ‹16 ≤ _ ∨ _ → _›
    have hz := ‹ZeroBytes _ _ (8 * n.toNat)›
    have hge := ‹8 * n.toNat ≤ blockSize _ _›
    refine ⟨fun _ => ⟨hin.sub (Nat.le_refl _) (by omega), h8 (Or.inr (by omega)),
      Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), fun i hi => ?_⟩, by janus_frame⟩
    simpa using hz.readLE (k := 8 * i) (j := 8) (by omega)

/-! ## Non-vacuity witness

`janus64_makeslice_witness` (`Janus/Contracts/AllocWitness.lean`) builds a concrete
`runtime.makeslice` at the contract address (it returns the 64 KiB heap), the runtime-owned ranges
`rt` (the heap and the `uint64` type descriptor), the readiness predicate `H`, and proves the
contract `hmk` for them. Below, a concrete call state of `MakeSlice(4)` satisfies the whole
precondition and the call returns the zeroed slice the theorem describes. -/

namespace Witness

janus64_makeslice_witness types := [u64Type]

open MakeW (impl rt H linked hmk)
open Janus.Contracts.AllocWitness (heap)

def tyA : Nat := janus_eval% u64Type
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
  { regs := fun i => if i = 0 then 4 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4136, 4136 + 16, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [4] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; obtain rfl : i = 0 := by omega
                                      rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [u64Type, (4 : BitVec 64).toNat, (4 : BitVec 64).toNat] (s0.regs 14).toNat
    ((s0.regs 4).toNat - 40) (rtView rt s0.mem) := by
  have hpt : u64Type = tyA := by unfold tyA; decide
  rw [hpt]
  have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
  refine Janus.Contracts.AllocWitness.makeH_intro
    (Janus.Contracts.AllocWitness.inRanges_ty (tys := MakeW.tys) (a := tyA) (by decide)) (by decide) ?_
  refine ⟨by rw [rtView_accessible]; decide, Janus.Contracts.AllocWitness.heapZero_of_bytes _ _ fun i hi => ?_⟩
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
theorem pre : StackGuardOK s0 0 ∧ StackWritable s0 4136 16 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4136) 4152 rt ∧ (s0.regs 4).toNat % 8 = 0 ∧
    (4 : BitVec 64).toNat ≤ 2 ^ 45 ∧
    H [u64Type, (4 : BitVec 64).toNat, (4 : BitVec 64).toNat] (s0.regs 14).toNat
      ((s0.regs 4).toNat - 40) (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, MakeW.rt, Janus.Contracts.AllocWitness.allocRt, MakeW.tys, outside_cons, outside_nil, List.map]; decide,
    by decide, by decide, hH⟩

def cAddr : Nat := Extracted.program.contractAddr "runtime.makeslice"

/-- The call state at `runtime.makeslice`'s entry (arguments `u64Type, 4, 4`, callee `SP` 40 below). -/
def wsCall : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 3 then 4 else if i = 1 then 4
      else if i = 4 then BitVec.ofNat 64 (sp0 - 40) else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 cAddr, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := s0.mem }

@[reducible] def mkSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : Janus.Amd64.State) : Prop :=
  MakeslicePre64 4096 s_c ∧
    Contracts.Ready64 H rt [(s_c.regs 0).toNat, (s_c.regs 3).toNat, (s_c.regs 1).toNat] s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : mkSite rt H wsCall := by
  have h := hH
  have hpt : u64Type = tyA := by unfold tyA; decide
  rw [hpt] at h
  refine ⟨⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, by decide, by decide, by decide⟩, ?_⟩
  exact h

/-- The theorem fires: `MakeSlice(4)` returns a zeroed slice of length and capacity 4 inside `rt`. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    s'.regs 3 = 4 ∧ s'.regs 1 = 4 ∧
    (0 < (4 : BitVec 64).toNat → InRanges (s'.regs 0).toNat (8 * (4 : BitVec 64).toNat) rt ∧
      (s'.regs 0).toNat % 8 = 0 ∧
      s'.mem.accessible (s'.regs 0).toNat (8 * (4 : BitVec 64).toNat) true = true ∧
      ∀ i, i < (4 : BitVec 64).toNat → s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
    MemFrame s0.mem s'.mem (rt ++ [((s0.regs 4).toNat - 4136, (s0.regs 4).toNat + 16)]) :=
  correctness impl rt H 4 hmk ret hret s0 setup pre

/-- The hypotheses are satisfiable: a `makeslice` meeting the contract (`hmk`), runtime ranges, a
readiness predicate, and a call state of `MakeSlice(4)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat)
    (s : Janus.Amd64.State),
    MakesliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [4] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 4136 16 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside ((s.regs 4).toNat - 4136) 4152 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
      (4 : BitVec 64).toNat ≤ 2 ^ 45 ∧
      H [u64Type, (4 : BitVec 64).toNat, (4 : BitVec 64).toNat] (s.regs 14).toNat
        ((s.regs 4).toNat - 40) (rtView rt s.mem)) ∧
    (∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite rt H s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
    s'.regs 3 = 4 ∧ s'.regs 1 = 4 ∧
    (0 < (4 : BitVec 64).toNat → InRanges (s'.regs 0).toNat (8 * (4 : BitVec 64).toNat) rt ∧
      (s'.regs 0).toNat % 8 = 0 ∧
      s'.mem.accessible (s'.regs 0).toNat (8 * (4 : BitVec 64).toNat) true = true ∧
      ∀ i, i < (4 : BitVec 64).toNat → s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 16)]) :=
  ⟨impl, rt, H, ret, s0, hmk, hret, setup, pre, ⟨wsCall, rfl, wsCall_pre⟩, returns⟩

end Witness

end Proof
