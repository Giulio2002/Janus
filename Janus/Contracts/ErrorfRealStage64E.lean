import Janus.Contracts.ErrorfRealStageDefs64

/-!
# Stage E of the real-format `fmt.errorf` stub (amd64): the literal `", want "` and the copy of number 2
-/

namespace Janus.Contracts.ErrorfRealStages64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops64
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfRealCode64 (code64)
open Janus.Contracts.ErrorfRealStages

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stageE64 (s : State) (tp tl len2 st2 dst2 p : Nat) (R : Nat → W64) (F : Flags) (m : Janus.Arm64.Memory)
    (hP : Pers64 s R tp tl) (h8 : R 8 = BitVec.ofNat 64 p) (h11 : R 11 = BitVec.ofNat 64 dst2)
    (h15 : R 15 = BitVec.ofNat 64 len2) (h13 : R 13 = BitVec.ofNat 64 st2)
    (hd : dst2 + 7 + len2 ≤ 2 ^ 48) (hs : st2 + len2 ≤ 2 ^ 48) (hlen2 : len2 < 2 ^ 32) (hdl : dst2 + 7 ≤ 2 ^ 48)
    (hlit : m.accessible dst2 7 true = true)
    (hdis : st2 + len2 ≤ dst2 + 7 ∨ dst2 + 7 + len2 ≤ st2)
    (hsrc : len2 = 0 ∨ m.accessible st2 len2 false = true) (hdst : len2 = 0 ∨ m.accessible (dst2 + 7) len2 true = true)
    (Q : State → Prop)
    (htail : ∀ (R' : Nat → W64) (F' : Flags) (m' : Janus.Arm64.Memory), Pers64 s R' tp tl → R' 8 = BitVec.ofNat 64 p →
      R' 11 = BitVec.ofNat 64 (dst2 + 7 + len2) →
      m' = putBytes (putBytes m dst2 [44, 32, 119, 97, 110, 116, 32]) (dst2 + 7)
        (strBytes (putBytes m dst2 [44, 32, 119, 97, 110, 116, 32]) st2 len2) →
      ReachesRet (withCode code64) (retAddrOf s) { s with regs := R', flags := F', mem := m', rip := 0x1001a9#64 } Q) :
    ReachesRet (withCode code64) (retAddrOf s) { s with regs := R, flags := F, mem := m, rip := 0x100168#64 } Q := by
  obtain ⟨hP9, hP10, hP4, hP5, hP14⟩ := hP
  janus64_run [h8, h11, h15, h13, hP4] until [0x100194]
  refine cpy64_c3 s len2 _ _ _ st2 (dst2 + 7) (by omega) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]) (by omega) (by omega) hdis ?_ ?_ _ ?_
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hsrc
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hdst
  · intro c F'
    refine htail _ _ _ ?_ ?_ ?_ rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [setRegF, hP9, hP10, hP4, hP5, hP14]
    · simp [setRegF, h8]
    · simp [setRegF]

end Janus.Contracts.ErrorfRealStages64
