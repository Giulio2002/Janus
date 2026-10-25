import Janus.Contracts.MallocSC
import Janus.Contracts.AllocSat

/-!
# The size-specialised allocation contracts are satisfiable (arm64)

The toy allocator of `Janus.Contracts.AllocSat` (it returns the heap `heap`) meets `mallocgc`'s
contract, hence every specialised one (`MallocgcContract.smallNoScanSC`, …), and a call state
satisfies each contract's whole precondition: `new` of a 16-byte pointer-free type (class 2), of
an 8-byte one (`mallocgcTinySize8`), and of a 16-byte type with pointers (class 2, the memory
`wmemS` with a pointerful descriptor at `tyA`).
-/

namespace Janus.Contracts.MallocSCSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.AllocSat

theorem mallocgcSmallNoScanSC_satisfiable : ∃ (n : Nat) (impl : List Segment) (rt : List (Nat × Nat))
    (H : RtReady), MallocgcSmallNoScanSCContract n (toy.link impl) A0 rt 4096 H ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ MallocgcSCPre (NoScanArgs n) rt 4096 H s :=
  ⟨2, _, _, _, mallocgc_impl.smallNoScanSC,
    wstate (fun i => if i = 0 then 16 else if i = 1 then BitVec.ofNat 64 tyA else if i = 2 then 1 else 0),
    rfl, ⟨⟨callOK_w _ 3 (by omega), by decide, Or.inr ⟨typeOK_w, fun h => by simp at h; decide⟩⟩,
      heapReady_w, 16, tyA, 1, rfl, by decide⟩, by unfold NoScanArgs; decide⟩

theorem mallocgcTinySize_satisfiable : ∃ (n : Nat) (impl : List Segment) (rt : List (Nat × Nat))
    (H : RtReady), MallocgcTinySizeContract n (toy.link impl) A0 rt 4096 H ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ MallocgcSCPre (TinyArgs n) rt 4096 H s :=
  ⟨8, _, _, _, mallocgc_impl.tinySize,
    wstate (fun i => if i = 0 then 8 else if i = 1 then BitVec.ofNat 64 tyA else if i = 2 then 1 else 0),
    rfl, ⟨⟨callOK_w _ 3 (by omega), by decide, Or.inr ⟨typeOK_w, fun h => by simp at h; decide⟩⟩,
      heapReady_w, 8, tyA, 1, rfl, by decide⟩, by unfold TinyArgs; decide⟩

/-- `AllocSat.wmem` with a pointerful 16-byte descriptor at `tyA` (`PtrBytes = 8`). -/
def wmemS : Memory :=
  ⟨fun a => if a = tyA then 16 else if a = tyA + 8 then 8 else 0, AllocSat.wmem.regions⟩

def wstateS (r : Nat → W64) : State := { wstate r with mem := wmemS }

theorem heapReady_s : HeapReady (rtView rt wmemS) := by
  refine ⟨by decide, fun i hi => ?_⟩
  show (if _ then wmemS.bytes (heap + i) else 0) = 0
  split
  · show (if heap + i = tyA then (16 : Byte) else if heap + i = tyA + 8 then 8 else 0) = 0
    rw [ite_eq_right_iff.mpr (fun h => by simp only [heap, tyA] at h; omega),
      ite_eq_right_iff.mpr (fun h => by simp only [heap, tyA] at h; omega)]
  · rfl

theorem callOK_s (r : Nat → W64) : CallOK (wstateS r) 4096 3 := by
  have h := callOK_w r 3 (by omega)
  exact h

theorem mallocgcSmallScanNoHeaderSC_satisfiable : ∃ (n : Nat) (impl : List Segment)
    (rt : List (Nat × Nat)) (H : RtReady),
    MallocgcSmallScanNoHeaderSCContract n (toy.link impl) A0 rt 4096 H ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ MallocgcSCPre (ScanArgs n) rt 4096 H s :=
  ⟨2, _, _, _, mallocgc_impl.smallScanNoHeaderSC,
    wstateS (fun i => if i = 0 then 16 else if i = 1 then BitVec.ofNat 64 tyA else if i = 2 then 1 else 0),
    rfl, ⟨⟨callOK_s _, by decide, Or.inr ⟨⟨by decide, by decide⟩, fun _ => by decide⟩⟩,
      heapReady_s, 16, tyA, 1, rfl, by decide⟩, by unfold ScanArgs; decide⟩

end Janus.Contracts.MallocSCSat
