import Janus.Contracts.ErrorfRealStageDefs64

/-!
# Stage F of the real-format `fmt.errorf` stub (amd64): the literal `" bytes"`, the result registers and the return
-/

namespace Janus.Contracts.ErrorfRealStages64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops64
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfRealCode64 (code64)
open Janus.Contracts.ErrorfRealStages

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stageF64 (s : State) (tp tl p dst3 : Nat) (R : Nat → W64) (F : Flags) (m : Janus.Arm64.Memory)
    (hP : Pers64 s R tp tl) (h8 : R 8 = BitVec.ofNat 64 p) (h11 : R 11 = BitVec.ofNat 64 dst3)
    (hd : dst3 + 6 ≤ 2 ^ 48) (hlit : m.accessible dst3 6 true = true)
    (hdisR : dst3 + 6 ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 8 ≤ dst3)
    (hret : m.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (h48 : (s.regs 4).toNat + 8 ≤ 2 ^ 48)
    (hrs : m.accessible (s.regs 4).toNat 8 false = true)
    (Q : State → Prop)
    (hQ : ∀ (R' : Nat → W64) (F' : Flags) (m' : Janus.Arm64.Memory), R' 0 = BitVec.ofNat 64 0x4444 → R' 3 = BitVec.ofNat 64 p →
      R' 4 = s.regs 4 + 8#64 → R' 5 = s.regs 5 → R' 14 = s.regs 14 → m' = putBytes m dst3 [32, 98, 121, 116, 101, 115] →
      Q { s with regs := R', flags := F', mem := m', rip := retAddrOf s }) :
    ReachesRet (withCode code64) (retAddrOf s) { s with regs := R, flags := F, mem := m, rip := 0x1001a9#64 } Q := by
  obtain ⟨hP9, hP10, hP4, hP5, hP14⟩ := hP
  have hm : m.readLE (R 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by rw [hP4]; exact hret
  janus64_run [h8, h11, hP4, hm]
  exact hQ _ _ _ (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF, hP5]) (by simp [setRegF, hP14]) rfl

end Janus.Contracts.ErrorfRealStages64
