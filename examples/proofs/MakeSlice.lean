import Extracted

/-!
# `MakeSlice(n int) []uint64` returns a fresh zeroed slice of `n` words

**Guarantee.** For every `n ≤ 2^45`, every list `rt` of runtime-owned memory ranges and
**every** implementation of `runtime.makeslice` satisfying `MakesliceContract`
(`Janus/Contracts/Alloc.lean`), and every Go call state of `example.com/basic.MakeSlice` in which
the stack-growth prologue falls through, the stack window `[SP-4144, SP+16)` is writable and
outside `rt`, and memory holds the program's read-only data (the `uint64` type descriptor): the
call returns, obeys the ABI, and the result slice `(X0, X1, X2)` has length and capacity `n`
(`X1 = X2 = n`); for `n > 0` its array `[X0, X0 + 8n)` lies inside the runtime-owned ranges (so it
is fresh: disjoint from all caller data outside them), is writable and 8-byte aligned, and every
word of it is `0`. Memory outside `rt` and the stack window is unchanged. For `n = 0` the pointer
is not specified (Go returns `&runtime.zerobase`).

**What is assumed.** The contract for `runtime.makeslice` (hypothesis `hmk`), stated for the code
linked at its address; the allocator is not executed (docs/RUNTIME-CONTRACTS.md). `n ≤ 2^45` keeps
`8n` within `maxAlloc`, so no panic path of `makeslice` is taken.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The address of `uint64`'s type descriptor, the element type MakeSlice passes to
`runtime.makeslice` (the `ADRP` + `ADD` pair at `MakeSlice+0x24`), recomputed from the extracted
words. -/
def u64Type : Nat :=
  adrpLdTarget (Extracted.entry + 0x24) (segWord Extracted.program "example.com/basic.MakeSlice" 9)
    (segWord Extracted.program "example.com/basic.MakeSlice" 10) 0

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (n : BitVec 64)
    (hmk : MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [n]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 16 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4160 rt ∧ n.toNat ≤ 2 ^ 45 ∧
        H [u64Type, n.toNat, n.toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => s'.regs 1 = n ∧ s'.regs 2 = n ∧
        (0 < n.toNat → InRanges (s'.regs 0).toNat (8 * n.toNat) rt ∧ (s'.regs 0).toNat % 8 = 0 ∧
          s'.mem.accessible (s'.regs 0).toNat (8 * n.toNat) true = true ∧
          ∀ i, i < n.toNat → s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 16)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hn, hH⟩
  janus_intro hs
  janus_eval_nat h_ut : u64Type
  rw [h_ut] at hH
  janus_data hd [hw]
  by_cases h0 : n.toNat = 0
  · janus_run calls [hmk]
    exact ⟨fun h => absurd h (by omega), by janus_frame⟩
  · janus_run calls [hmk.pos]
    rename_i hin _ hacc h8 _ hz hge
    refine ⟨fun _ => ⟨hin.sub (Nat.le_refl _) (by omega), h8 (Or.inr (by omega)),
      Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), fun i hi => ?_⟩, by janus_frame⟩
    simpa using hz.readLE (k := 8 * i) (j := 8) (by omega)

/-! ## Non-vacuity witness

`janus_makeslice_witness` (`Janus/Contracts/AllocWitness.lean`) builds a concrete `runtime.makeslice`
at the contract address (it returns the 64 KiB heap), the runtime-owned ranges `rt` (the heap and the
`uint64` type descriptor), the readiness predicate `H`, and proves the contract `hmk` for them.
Below, a concrete call state of `MakeSlice(4)` satisfies the whole precondition, `H` included, and
the call returns the zeroed slice the theorem describes. -/

namespace Witness

janus_makeslice_witness types := [u64Type]

open MakeW (impl rt H linked hmk)
open Janus.Contracts.AllocWitness (heap)

def tyA : Nat := janus_eval% u64Type
def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def dat : DataSegment := Extracted.data.head!
def dlen : Nat := janus_eval% dat.bytes.length
def dbase : Nat := janus_eval% dat.base

def bytes (a : Nat) : Byte :=
  if dbase ≤ a ∧ a < dbase + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - dbase) 0) else 0

def s0 : State :=
  { regs := fun i => if i = 0 then 4 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4144, 4160, true⟩, ⟨g0, 0x100, false⟩, ⟨dbase, dlen, false⟩,
      ⟨heap, 0x10000, true⟩]⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [4] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [u64Type, (4 : BitVec 64).toNat, (4 : BitVec 64).toNat] (s0.regs 28).toNat (s0.sp.toNat - 48)
    (rtView rt s0.mem) := by
  have hpt : u64Type = tyA := by unfold tyA; decide
  rw [hpt]
  refine Janus.Contracts.AllocWitness.makeH_intro
    (Janus.Contracts.AllocWitness.inRanges_ty (tys := MakeW.tys) (a := tyA) (by decide)) ?_ ?_
  · decide
  · refine ⟨by decide, Janus.Contracts.AllocWitness.heapZero_of_bytes _ _ fun i hi => ?_⟩
    have h1 : ¬(dbase ≤ heap + i ∧ heap + i < dbase + dlen) := by
      simp only [dbase, heap, dlen]; omega
    show bytes (heap + i) = 0
    simp only [bytes]; rw [if_neg h1]

theorem pre : GuardOK s0 0 ∧ StackOK s0 4144 16 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4144) 4160 rt ∧ (4 : BitVec 64).toNat ≤ 2 ^ 45 ∧
    H [u64Type, (4 : BitVec 64).toNat, (4 : BitVec 64).toNat] (s0.regs 28).toNat (s0.sp.toNat - 48)
      (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, MakeW.rt, Janus.Contracts.AllocWitness.allocRt, MakeW.tys, outside_cons, outside_nil, List.map]; decide,
    by decide, hH⟩

/-- The hypotheses are satisfiable: a `makeslice` meeting the contract (`hmk`), runtime ranges, a
readiness predicate, and a call state of `MakeSlice(4)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat)
    (s : State),
    MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [4] s ∧
    (GuardOK s 0 ∧ StackOK s 4144 16 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4144) 4160 rt ∧ (4 : BitVec 64).toNat ≤ 2 ^ 45 ∧
      H [u64Type, (4 : BitVec 64).toNat, (4 : BitVec 64).toNat] (s.regs 28).toNat (s.sp.toNat - 48)
        (rtView rt s.mem)) :=
  ⟨impl, rt, H, ret, s0, hmk, hret, setup, pre⟩

/-- The theorem fires: for this call and this `makeslice`, `MakeSlice(4)` returns a zeroed slice of
length and capacity 4 inside `rt`. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    s'.regs 1 = 4 ∧ s'.regs 2 = 4 ∧
    (0 < (4 : BitVec 64).toNat → InRanges (s'.regs 0).toNat (8 * (4 : BitVec 64).toNat) rt ∧
      (s'.regs 0).toNat % 8 = 0 ∧
      s'.mem.accessible (s'.regs 0).toNat (8 * (4 : BitVec 64).toNat) true = true ∧
      ∀ i, i < (4 : BitVec 64).toNat → s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
    MemFrame s0.mem s'.mem (rt ++ [(s0.sp.toNat - 4144, s0.sp.toNat + 16)]) :=
  correctness impl rt H 4 hmk ret hret s0 setup pre

end Witness

end Proof
