import Janus.Contracts.ErrorfRealStageDefs

/-!
# Stage D of the real-format `fmt.errorf` stub (arm64): the literal `": have "` and the copy of number 1
-/

namespace Janus.Contracts.ErrorfRealStages

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops
open Janus.Contracts.AllocSat (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfRealCode (code)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- From the exit of the text copy to the exit of the copy of number 1. -/
theorem stageD (s : State) (h30b : (s.regs 30).toNat < 2 ^ 48) (h30a : (s.regs 30).toNat % 4 = 0)
    (e tp tl len1 st1 len2 st2 dst1 : Nat) (R : Nat → W64) (F : Flags) (m : Memory)
    (hP : Pers s R e tp tl) (h11 : R 11 = BitVec.ofNat 64 dst1) (h25 : R 25 = BitVec.ofNat 64 len1)
    (h26 : R 26 = BitVec.ofNat 64 st1) (h21 : R 21 = BitVec.ofNat 64 len2) (h22 : R 22 = BitVec.ofNat 64 st2)
    (hd : dst1 + 7 + len1 ≤ 2 ^ 48) (hs : st1 + len1 ≤ 2 ^ 48) (hlen1 : len1 < 2 ^ 32)
    (hdl : dst1 + 7 ≤ 2 ^ 48)
    (hlit : m.accessible dst1 7 true = true)
    (hdis : st1 + len1 ≤ dst1 + 7 ∨ dst1 + 7 + len1 ≤ st1)
    (hsrc : len1 = 0 ∨ m.accessible st1 len1 false = true) (hdst : len1 = 0 ∨ m.accessible (dst1 + 7) len1 true = true)
    (Q : State → Prop)
    (htail : ∀ (R' : Nat → W64) (F' : Flags) (m' : Memory), Pers s R' e tp tl →
      R' 21 = BitVec.ofNat 64 len2 → R' 22 = BitVec.ofNat 64 st2 →
      R' 11 = BitVec.ofNat 64 (dst1 + 7 + len1) →
      m' = putBytes (putBytes m dst1 [58, 32, 104, 97, 118, 101, 32]) (dst1 + 7)
        (strBytes (putBytes m dst1 [58, 32, 104, 97, 118, 101, 32]) st1 len1) →
      ReachesRet (withCode code) (s.regs 30) { s with regs := R', flags := F', mem := m', pc := 0x10016c#64 } Q) :
    ReachesRet (withCode code) (s.regs 30) { s with regs := R, flags := F, mem := m, pc := 0x100118#64 } Q := by
  obtain ⟨hP5, hP6, hP7, hP15, hP18, hP28, hP29, hP30⟩ := hP
  janus_run [h11, h25, h26, h21, h22, hP30] until [0x100158]
  refine cpy_c2 s h30b h30a len1 _ _ _ st1 (dst1 + 7) (by omega) (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat])
    (by simp [setReg, hP30]) (by omega) (by omega) hdis ?_ ?_ _ ?_
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hsrc
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hdst
  · intro c
    refine htail _ _ _ ?_ ?_ ?_ ?_ rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [setReg, hP5, hP6, hP7, hP15, hP18, hP28, hP29, hP30]
    · simp [setReg, h21]
    · simp [setReg, h22]
    · simp [setReg]

end Janus.Contracts.ErrorfRealStages
