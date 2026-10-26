import Extracted

/-!
# `NewPair(a, b uint64) *Pair` built with `GOEXPERIMENT=sizespecializedmalloc` (arm64)

```go
type Pair struct{ A, B uint64 }
func NewPair(a, b uint64) *Pair { return &Pair{a, b} }
```

With the experiment the allocation is a direct call of the size-specialised entry point of
`Pair`'s size class, `runtime.mallocgcSmallNoScanSC2(16, type:Pair, true)`, instead of
`runtime.newobject`. It is left out (`--contract 'runtime.mallocgcSmallNoScanSC*'`) and its
behaviour is the hypothesis `MallocgcSmallNoScanSCContract 2` (`Janus/Contracts/MallocSC.lean`:
`mallocgc`'s contract, readiness `H` included, for the calls of class 2).

**Guarantee.** As for `NewPair` with `newobject` (`examples/proofs/NewPair.lean`): for every
`rt`, `H` and every implementation meeting the contract, and every call state in which the
prologue falls through, the stack window is writable and outside `rt`, the program's read-only
data is loaded (`Pair`'s descriptor: 16 bytes, no pointers) and the runtime is ready for the call
(`H [16, pairType, 1] …`), the call returns a 16-byte-aligned, writable object inside `rt` holding
`a` and `b`, and memory changes only in `rt` and the stack window.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- `Pair`'s type descriptor (`ADRP`+`ADD` at `NewPair+0x24`). -/
def pairType : Nat :=
  adrpLdTarget (Extracted.entry + 0x24) (segWord Extracted.program "example.com/rtmisc/sc.NewPair" 9)
    (segWord Extracted.program "example.com/rtmisc/sc.NewPair" 10) 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hsc : MallocgcSmallNoScanSCContract 2 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgcSmallNoScanSC2") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0 ∧ StackOK s 4168 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4168) 4192 rt ∧
        H [16, pairType, 1] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 16 true = true ∧
        s'.mem.readLE ptr 8 = a.toNat ∧ s'.mem.readLE (ptr + 8) 8 = b.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4168, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : pairType
  rw [h_pt] at hH
  janus_data hd [hw]
  janus_run until [Extracted.entry + 0x34] calls [hsc]
  have hdj := InRanges.disjoint ‹InRanges _ 16 rt› hout
  janus_run
  rename_i ptr junk f v m hfr hin hle hacc h8 h16 hz htrue
  have hp := ptr.isLt
  refine ⟨_, rfl, hin, h16, hacc, ?_, ?_, ?_⟩
  rotate_left 2
  · refine MemFrame.writeLE_inRanges ?_ _ (InRanges.append_left (hin.sub (by omega) (by omega)) _)
    refine MemFrame.writeLE_inRanges ?_ _ (InRanges.append_left (hin.sub (Nat.le_refl _) (by omega)) _)
    refine MemFrame.trans (rs := [(BitVec.toNat s.sp - 4168, BitVec.toNat s.sp + 24)]) (by janus_frame) hfr
      fun x n hx => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true] at hx ⊢
    obtain ⟨hr, hw'⟩ := hx
    exact ⟨hw', hr, by omega⟩
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt a.isLt
  · rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt b.isLt


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A two-instruction allocator at `runtime.mallocgcSmallNoScanSC2`'s address (`MOVZ X0, #0x10000;
RET`), `rt` a 64 KiB heap at `0x10000`, and `H`: the request is at most 32 KiB and the heap is
writable and zero (as the runtime sees it). `model` proves the contract for them by running the
code; `s0` is a concrete call of `NewPair(3, 5)` (stack, a readable `g`, the read-only data, the
heap) satisfying the precondition, and `returns` reaches the conclusion. -/

namespace Witness

def heap : Nat := 0x10000
def rt : List (Nat × Nat) := [(heap, heap + 0x10000)]
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.mallocgcSmallNoScanSC2")
def implAt : List Segment :=
  [{ name := "witness.mallocgcSmallNoScanSC2", base := cA, words := [0xd2a00020, 0xd65f03c0] }]

def H : RtReady := fun args _ _ v =>
  (∃ sz typ nz, args = [sz, typ, nz] ∧ sz ≤ 32768) ∧
    v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

def linked : Program := Extracted.program.link implAt

theorem addr : Extracted.program.contractAddr "runtime.mallocgcSmallNoScanSC2" = cA := by decide

theorem callRegs_eq (r : Nat → W64) :
    callRegs r r [BitVec.ofNat 64 heap] = setReg r 0 (BitVec.ofNat 64 heap) := by
  funext i
  simp only [callRegs, setReg]
  rcases i with _ | i
  · rfl
  · simp only [List.getD_cons_succ, List.getD_nil]
    split <;> rfl

theorem model : MallocgcSmallNoScanSCContract 2 (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.mallocgcSmallNoScanSC2") rt 4096 H := by
  rw [addr]
  intro s hpc ⟨⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, ⟨sz, typ, nz, hargs, hsz⟩, hacc, hz⟩, _⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨hsz', -, -⟩ := hargs
  change ReachesRet linked _ s _
  janus_run
  refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
  · simp only [retStateX]; rw [callRegs_eq]; rfl
  · have hs : (s.regs 0).toNat ≤ 32768 := by omega
    have hb := blockSize_le_maxSmallSize (s.regs 0).toNat
      ((s.regs 1).toNat == 0 || typNoscan s.mem (s.regs 1).toNat) hs
    have hle : (s.regs 0).toNat ≤ blockSize (s.regs 0).toNat
        ((s.regs 1).toNat == 0 || typNoscan s.mem (s.regs 1).toNat) := by
      unfold blockSize; split
      · exact Nat.le_refl _
      · exact le_roundupsize _ _
    simp only [maxSmallSize] at hb
    have hheap : (BitVec.ofNat 64 heap).toNat = heap := by decide
    rw [hheap]
    refine ⟨⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, by simp only [heap]; omega⟩,
      by simp only [heap]; omega, ?_, fun _ => by decide, fun _ _ => by decide, fun _ => ?_, hle⟩
    · rw [rtView_accessible] at hacc
      exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
    · have := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
      exact fun i hi => this i (by omega)

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def dat : DataSegment := Extracted.data.head!
def dA : Nat := janus_eval% dat.base
def dlen : Nat := janus_eval% dat.bytes.length

def bytes (a : Nat) : Byte :=
  if dA ≤ a ∧ a < dA + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - dA) 0) else 0

def s0 : State :=
  { regs := fun i => if i = 0 then 3 else if i = 1 then 5 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4168, 4192, true⟩, ⟨g0, 0x100, false⟩, ⟨dA, dlen, false⟩,
      ⟨heap, 0x10000, true⟩]⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [3, 5] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

theorem hH : H [16, pairType, 1] (s0.regs 28).toNat (s0.sp.toNat - 64) (rtView rt s0.mem) := by
  refine ⟨⟨16, pairType, 1, rfl, by decide⟩, by decide, ?_⟩
  intro i hi
  have h1 : ¬(dA ≤ heap + i ∧ heap + i < dA + dlen) := by
    simp only [dA, heap, dlen]; omega
  show (if _ then bytes (heap + i) else 0) = 0
  split
  · simp only [bytes]; rw [if_neg h1]
  · rfl

theorem pre : GuardOK s0 0 ∧ StackOK s0 4168 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4168) 4192 rt ∧
    H [16, pairType, 1] (s0.regs 28).toNat (s0.sp.toNat - 64) (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, hH⟩

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat)
    (s : State), MallocgcSmallNoScanSCContract 2 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgcSmallNoScanSC2") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 5] s ∧
    (GuardOK s 0 ∧ StackOK s 4168 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4168) 4192 rt ∧
      H [16, pairType, 1] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem)) :=
  ⟨implAt, rt, H, ret, s0, model, hret, setup, pre⟩

/-- So the guarantee is reached: `NewPair(3, 5)` returns a fresh object holding 3 and 5. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧
      s'.mem.readLE ptr 8 = 3 ∧ s'.mem.readLE (ptr + 8) 8 = 5 :=
  (correctness implAt rt H 3 5 model ret hret s0 setup pre).mono fun _ ⟨habi, ptr, h0, hin, _, _, ha, hb, _⟩ =>
    ⟨habi, ptr, h0, hin, ha, hb⟩

end Witness

end Proof
