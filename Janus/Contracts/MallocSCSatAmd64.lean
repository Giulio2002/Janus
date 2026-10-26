import Janus.Contracts.MallocSCAmd64
import Janus.Contracts.AllocSatAmd64
import Janus.Contracts.MallocSCSat

/-!
# The size-specialised allocation contracts are satisfiable (amd64)

As `Janus.Contracts.MallocSCSat`, with the toy allocator of `Janus.Contracts.AllocSatAmd64`.
-/

namespace Janus.Contracts.MallocSCSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.AllocSatAmd64
open Janus.Contracts.AllocSat (heap tyA rt HeapReady)

theorem mallocgcSmallNoScanSC64_satisfiable : ∃ (n : Nat) (impl : List Janus.Amd64.Segment)
    (rt : List (Nat × Nat)) (H : RtReady), MallocgcSmallNoScanSCContract64 n (toy.link impl) A0 rt 4096 H ∧
    ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧ MallocgcSCPre64 (NoScanArgs n) rt 4096 H s :=
  ⟨2, _, _, _, mallocgc64_impl.smallNoScanSC,
    wstate 16 (fun i => if i = 0 then 16 else if i = 3 then BitVec.ofNat 64 tyA else if i = 1 then 1 else 0),
    rfl, ⟨⟨callOK_w _ _ 3 (by omega), by decide, Or.inr ⟨⟨by decide, by decide⟩, fun h => by simp at h; decide⟩⟩,
      heapReady_w 16 (by decide), 16, tyA, 1, rfl, by decide⟩, by unfold NoScanArgs; decide⟩

theorem mallocgcTinySize64_satisfiable : ∃ (n : Nat) (impl : List Janus.Amd64.Segment)
    (rt : List (Nat × Nat)) (H : RtReady), MallocgcTinySizeContract64 n (toy.link impl) A0 rt 4096 H ∧
    ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧ MallocgcSCPre64 (TinyArgs n) rt 4096 H s :=
  ⟨8, _, _, _, mallocgc64_impl.tinySize,
    wstate 16 (fun i => if i = 0 then 8 else if i = 3 then BitVec.ofNat 64 tyA else if i = 1 then 1 else 0),
    rfl, ⟨⟨callOK_w _ _ 3 (by omega), by decide, Or.inr ⟨⟨by decide, by decide⟩, fun h => by simp at h; decide⟩⟩,
      heapReady_w 16 (by decide), 8, tyA, 1, rfl, by decide⟩, by unfold TinyArgs; decide⟩

/-- `AllocSatAmd64.wmem 16` with a pointerful descriptor at `tyA` (`PtrBytes = 8`). -/
def wmemS : Janus.Arm64.Memory :=
  ⟨fun a => if a = tyA then 16 else if a = tyA + 8 then 8 else 0, (wmem 16).regions⟩

def wstateS (r : Nat → W64) : Janus.Amd64.State := { wstate 16 r with mem := wmemS }

theorem heapReady_s : HeapReady (Janus.Contracts.rtView rt wmemS) := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [rtView_accessible, show wmemS.accessible heap 0x10000 true =
      (wmem 0).accessible heap 0x10000 true from rfl]
    decide
  show (if _ then wmemS.bytes (heap + i) else 0) = 0
  split
  · show (if heap + i = tyA then (16 : Janus.Arm64.Byte) else if heap + i = tyA + 8 then 8 else 0) = 0
    rw [ite_eq_right_iff.mpr (fun h => by simp only [heap, tyA] at h; omega),
      ite_eq_right_iff.mpr (fun h => by simp only [heap, tyA] at h; omega)]
  · rfl

theorem mallocgcSmallScanNoHeaderSC64_satisfiable : ∃ (n : Nat) (impl : List Janus.Amd64.Segment)
    (rt : List (Nat × Nat)) (H : RtReady),
    MallocgcSmallScanNoHeaderSCContract64 n (toy.link impl) A0 rt 4096 H ∧
    ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧ MallocgcSCPre64 (ScanArgs n) rt 4096 H s :=
  ⟨2, _, _, _, mallocgc64_impl.smallScanNoHeaderSC,
    wstateS (fun i => if i = 0 then 16 else if i = 3 then BitVec.ofNat 64 tyA else if i = 1 then 1 else 0),
    rfl, ⟨⟨callOK_w 16 (fun i => if i = 0 then 16 else if i = 3 then BitVec.ofNat 64 tyA else if i = 1 then 1 else 0) 3 (by omega), by decide, Or.inr ⟨⟨by decide, by decide⟩, fun _ => by decide⟩⟩,
      heapReady_s, 16, tyA, 1, rfl, by decide⟩, by unfold ScanArgs; decide⟩

end Janus.Contracts.MallocSCSatAmd64
