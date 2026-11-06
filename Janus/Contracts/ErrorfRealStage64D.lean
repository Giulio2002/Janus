import Janus.Contracts.ErrorfRealStageDefs64

/-!
# Stage D of the real-format `fmt.errorf` stub (amd64): the literal `": have "` and the copy of number 1
-/

namespace Janus.Contracts.ErrorfRealStages64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops64
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfRealCode64 (code64)
open Janus.Contracts.ErrorfRealStages

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stageD64 (s : State) (tp tl len1 st1 len2 st2 dst1 p : Nat) (R : Nat → W64) (F : Flags) (m : Janus.Arm64.Memory)
    (hP : Pers64 s R tp tl) (h8 : R 8 = BitVec.ofNat 64 p) (h11 : R 11 = BitVec.ofNat 64 dst1)
    (h3 : R 3 = BitVec.ofNat 64 len1) (h6 : R 6 = BitVec.ofNat 64 st1) (h15 : R 15 = BitVec.ofNat 64 len2)
    (h13 : R 13 = BitVec.ofNat 64 st2)
    (hd : dst1 + 7 + len1 ≤ 2 ^ 48) (hs : st1 + len1 ≤ 2 ^ 48) (hlen1 : len1 < 2 ^ 32) (hdl : dst1 + 7 ≤ 2 ^ 48)
    (hlit : m.accessible dst1 7 true = true)
    (hdis : st1 + len1 ≤ dst1 + 7 ∨ dst1 + 7 + len1 ≤ st1)
    (hsrc : len1 = 0 ∨ m.accessible st1 len1 false = true) (hdst : len1 = 0 ∨ m.accessible (dst1 + 7) len1 true = true)
    (Q : State → Prop)
    (htail : ∀ (R' : Nat → W64) (F' : Flags) (m' : Janus.Arm64.Memory), Pers64 s R' tp tl → R' 8 = BitVec.ofNat 64 p →
      R' 15 = BitVec.ofNat 64 len2 → R' 13 = BitVec.ofNat 64 st2 →
      R' 11 = BitVec.ofNat 64 (dst1 + 7 + len1) →
      m' = putBytes (putBytes m dst1 [58, 32, 104, 97, 118, 101, 32]) (dst1 + 7)
        (strBytes (putBytes m dst1 [58, 32, 104, 97, 118, 101, 32]) st1 len1) →
      ReachesRet (withCode code64) (retAddrOf s) { s with regs := R', flags := F', mem := m', rip := 0x100168#64 } Q) :
    ReachesRet (withCode code64) (retAddrOf s) { s with regs := R, flags := F, mem := m, rip := 0x100127#64 } Q := by
  obtain ⟨hP9, hP10, hP4, hP5, hP14⟩ := hP
  janus64_run [h8, h11, h3, h6, h15, h13, hP4] until [0x100153]
  refine cpy64_c2 s len1 _ _ _ st1 (dst1 + 7) (by omega) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]) (by omega) (by omega) hdis ?_ ?_ _ ?_
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hsrc
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hdst
  · intro c F'
    refine htail _ _ _ ?_ ?_ ?_ ?_ ?_ rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [setRegF, hP9, hP10, hP4, hP5, hP14]
    · simp [setRegF, h8]
    · simp [setRegF, h15]
    · simp [setRegF, h13]
    · simp [setRegF]

end Janus.Contracts.ErrorfRealStages64
