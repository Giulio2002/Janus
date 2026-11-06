import Janus.Contracts.ErrorfRealStageDefs

/-!
# Stage F of the real-format `fmt.errorf` stub (arm64): the literal `" bytes"`, the result `x0`, and the return
-/

namespace Janus.Contracts.ErrorfRealStages

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops
open Janus.Contracts.AllocSat (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfRealCode (code)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- From the exit of the copy of number 2 to the return. -/
theorem stageF (s : State) (h30b : (s.regs 30).toNat < 2 ^ 48) (h30a : (s.regs 30).toNat % 4 = 0)
    (e tp tl p dst3 : Nat) (R : Nat → W64) (F : Flags) (m : Memory)
    (hP : Pers s R e tp tl) (h11 : R 11 = BitVec.ofNat 64 dst3) (h1 : R 1 = BitVec.ofNat 64 p)
    (hd : dst3 + 6 < 2 ^ 48) (hlit : m.accessible dst3 6 true = true)
    (Q : State → Prop)
    (hQ : ∀ (R' : Nat → W64) (F' : Flags) (m' : Memory), R' 0 = BitVec.ofNat 64 0x4444 → R' 1 = BitVec.ofNat 64 p →
      R' 18 = s.regs 18 → R' 28 = s.regs 28 → R' 29 = s.regs 29 → m' = putBytes m dst3 [32, 98, 121, 116, 101, 115] →
      Q { s with regs := R', flags := F', mem := m', pc := s.regs 30 }) :
    ReachesRet (withCode code) (s.regs 30) { s with regs := R, flags := F, mem := m, pc := 0x1001c0#64 } Q := by
  obtain ⟨hP5, hP6, hP7, hP15, hP18, hP28, hP29, hP30⟩ := hP
  janus_run [h11, h1, hP30]
  exact hQ _ _ _ (by simp [setReg]) (by simp [setReg, h1]) (by simp [setReg, hP18]) (by simp [setReg, hP28])
    (by simp [setReg, hP29]) rfl

end Janus.Contracts.ErrorfRealStages
