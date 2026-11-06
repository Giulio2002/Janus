import Janus.Contracts.ErrorfRealStageDefs

/-!
# Stage E of the real-format `fmt.errorf` stub (arm64): the literal `", want "` and the copy of number 2
-/

namespace Janus.Contracts.ErrorfRealStages

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops
open Janus.Contracts.AllocSat (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfRealCode (code)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- From the exit of the copy of number 1 to the exit of the copy of number 2. -/
theorem stageE (s : State) (h30b : (s.regs 30).toNat < 2 ^ 48) (h30a : (s.regs 30).toNat % 4 = 0)
    (e tp tl len2 st2 dst2 p : Nat) (R : Nat → W64) (F : Flags) (m : Memory)
    (hP : Pers s R e tp tl) (h1 : R 1 = BitVec.ofNat 64 p) (h11 : R 11 = BitVec.ofNat 64 dst2) (h21 : R 21 = BitVec.ofNat 64 len2)
    (h22 : R 22 = BitVec.ofNat 64 st2)
    (hd : dst2 + 7 + len2 ≤ 2 ^ 48) (hs : st2 + len2 ≤ 2 ^ 48) (hlen2 : len2 < 2 ^ 32)
    (hdl : dst2 + 7 ≤ 2 ^ 48)
    (hlit : m.accessible dst2 7 true = true)
    (hdis : st2 + len2 ≤ dst2 + 7 ∨ dst2 + 7 + len2 ≤ st2)
    (hsrc : len2 = 0 ∨ m.accessible st2 len2 false = true) (hdst : len2 = 0 ∨ m.accessible (dst2 + 7) len2 true = true)
    (Q : State → Prop)
    (htail : ∀ (R' : Nat → W64) (F' : Flags) (m' : Memory), Pers s R' e tp tl → R' 1 = BitVec.ofNat 64 p →
      R' 11 = BitVec.ofNat 64 (dst2 + 7 + len2) →
      m' = putBytes (putBytes m dst2 [44, 32, 119, 97, 110, 116, 32]) (dst2 + 7)
        (strBytes (putBytes m dst2 [44, 32, 119, 97, 110, 116, 32]) st2 len2) →
      ReachesRet (withCode code) (s.regs 30) { s with regs := R', flags := F', mem := m', pc := 0x1001c0#64 } Q) :
    ReachesRet (withCode code) (s.regs 30) { s with regs := R, flags := F, mem := m, pc := 0x10016c#64 } Q := by
  obtain ⟨hP5, hP6, hP7, hP15, hP18, hP28, hP29, hP30⟩ := hP
  janus_run [h1, h11, h21, h22, hP30] until [0x1001ac]
  refine cpy_c3 s h30b h30a len2 _ _ _ st2 (dst2 + 7) (by omega) (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat])
    (by simp [setReg, hP30]) (by omega) (by omega) hdis ?_ ?_ _ ?_
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hsrc
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hdst
  · intro c
    refine htail _ _ _ ?_ ?_ ?_ rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [setReg, hP5, hP6, hP7, hP15, hP18, hP28, hP29, hP30]
    · simp [setReg, h1]
    · simp [setReg]

end Janus.Contracts.ErrorfRealStages
