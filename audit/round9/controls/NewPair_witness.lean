import Extracted
import «Proof»
/-! Round 9 C1 positive control: the (fixed) allocation contract is satisfiable, and so is the
whole hypothesis set of `examples/proofs/NewPair.lean`.

* `impl` is a two-instruction allocator placed at `runtime.newobject`'s address
  (`MOVZ X0, #0x10000; RET`), `rt` is a 64 KiB heap at `0x10000` plus `Pair`'s type descriptor,
  and `H` says: the argument is a type descriptor inside `rt` of at most 32 KiB and the heap is
  writable and zero (as the runtime sees it, `rtView`). `hnew` proves `NewobjectContract` for
  them by running the code (`janus_run`).
* `s0` is a concrete call state of `NewPair` (stack window, a readable `g`, the read-only data,
  the heap) that satisfies the theorem's precondition, including `H`.
* `fires` instantiates `Proof.correctness`: its conclusion is reached for this call.

Before round 9 no such witness existed: the contract had no readiness hypothesis and was false
for every program, address and `rt` (`audit/round9/model/Unsat.lean`). -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace NewPairWitness

def heap : Nat := 0x10000
def tyA : Nat := 0xb2f40
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

/-- `MOVZ X0, #1, LSL #16` (`X0 = 0x10000`); `RET`. -/
def impl : List Segment :=
  [{ name := "witness.newobject", base := 0x28440, words := [0xd2a00020, 0xd65f03c0] }]

/-- The runtime is ready: the argument is a type descriptor inside `rt` whose size is at most
32 KiB, and the heap is writable and zero. -/
def H : RtReady := fun args _ _ v =>
  ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768 ∧
    v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

/-- The linked program, as one closed constant (the executor evaluates its facts directly). -/
def linked : Program := Extracted.program.link impl

theorem addr : Extracted.program.contractAddr "runtime.newobject" = 0x28440 := by decide

theorem callRegs_eq (r : Nat → W64) :
    callRegs r r [BitVec.ofNat 64 heap] = setReg r 0 (BitVec.ofNat 64 heap) := by
  funext i
  simp only [callRegs, setReg]
  rcases i with _ | i
  · rfl
  · simp only [List.getD_cons_succ, List.getD_nil]
    split <;> rfl

theorem hnew : NewobjectContract (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.newobject") rt 4096 H := by
  rw [addr]
  intro s hpc ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, typ, hargs, hin, hsz, hacc, hz⟩
  simp only [List.cons.injEq, and_true] at hargs
  subst hargs
  change ReachesRet linked _ s _
  janus_run
  refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, ?_, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩,
    fun hpos => ?_⟩
  · simp only [retState]; rw [callRegs_eq]; rfl
  · unfold typSize at hsz
    rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
    change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
    have hb := blockSize_le_maxSmallSize (typSize s.mem (s.regs 0).toNat)
      (typNoscan s.mem (s.regs 0).toNat) hsz
    have hle : typSize s.mem (s.regs 0).toNat ≤
        blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat) := by
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

/-! ## A concrete call of `NewPair` satisfying the whole precondition -/

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def dat : DataSegment := Extracted.data.head!

def bytes (a : Nat) : Byte :=
  if tyA ≤ a ∧ a < tyA + 256 then BitVec.ofNat 8 (dat.bytes.getD (a - tyA) 0) else 0

def s0 : State :=
  { regs := fun i => if i = 0 then 3 else if i = 1 then 5 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4144, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨tyA, 256, false⟩,
      ⟨heap, 0x10000, true⟩]⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [3, 5] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [Proof.pairType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) := by
  have hpt : Proof.pairType = tyA := by decide
  rw [hpt]
  refine ⟨tyA, rfl, ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩, by decide,
    by decide, ?_⟩
  intro i hi
  have h1 : ¬(tyA ≤ heap + i ∧ heap + i < tyA + 256) := by
    simp only [tyA, heap]; omega
  show (if _ then bytes (heap + i) else 0) = 0
  split
  · simp only [bytes]; rw [if_neg h1]
  · rfl

theorem pre : GuardOK s0 0 ∧ StackOK s0 4144 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4144) 4168 rt ∧
    H [Proof.pairType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, hH⟩

/- **The theorem fires**: for this call, with this allocator, `NewPair(3, 5)` returns a fresh
16-aligned object in `rt` holding 3 and 5. -/
example := Proof.correctness impl rt H 3 5 hnew ret hret s0 setup pre

end NewPairWitness
