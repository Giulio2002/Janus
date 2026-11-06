import Janus.Contracts.ErrorfRealStageDefs64

/-!
# Stage F of the real-format `fmt.errorf` stub (amd64): the literal `" bytes"`, the result registers and the return
-/

namespace Janus.Contracts.ErrorfRealStages64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops64
open Janus.Contracts.RelocAmd64 (codeProg64)
open Janus.Contracts.ErrorfRealCode64 (code64 E0)
open Janus.Contracts.ErrorfRealStages

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stageF64 (s : State) (tp tl p dst3 iW : Nat) (R : Nat → W64) (F : Flags) (m : Janus.Arm64.Memory)
    (hP : Pers64 s R tp tl) (h8 : R 8 = BitVec.ofNat 64 p) (h11 : R 11 = BitVec.ofNat 64 dst3)
    (hd : dst3 + 6 ≤ 2 ^ 48) (hlit : m.accessible dst3 6 true = true)
    (hiW : iW < 2 ^ 64) (hW : m.readLE 4194696 8 = iW) (hWa : m.accessible 4194696 8 false = true)
    (hdc : dst3 + 6 ≤ 4194696 ∨ 4194704 ≤ dst3)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (Q : State → Prop)
    (hQ : ∀ (R' : Nat → W64) (F' : Flags) (m' : Janus.Arm64.Memory), R' 0 = BitVec.ofNat 64 iW → R' 3 = BitVec.ofNat 64 p →
      R' 4 = s.regs 4 + 8#64 → R' 5 = s.regs 5 → R' 14 = s.regs 14 → m' = putBytes m dst3 [32, 98, 121, 116, 101, 115] →
      Q { s with regs := R', flags := F', mem := m', rip := retAddrOf s }) :
    ReachesRet (codeProg64 E0 code64) (retAddrOf s) { s with regs := R, flags := F, mem := m, rip := 0x4000000001af#64 } Q := by
  obtain ⟨hP9, hP10, hP4, hP5, hP14, hP15⟩ := hP
  have hr15' : (R 15).toNat < 2 ^ 47 := by
    rw [hP15]; simp only [retAddrOf, BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hra
  janus64_run [h8, h11, hP4, hP15, hW]
  exact hQ _ _ _ (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF, hP5]) (by simp [setRegF, hP14]) rfl

end Janus.Contracts.ErrorfRealStages64
