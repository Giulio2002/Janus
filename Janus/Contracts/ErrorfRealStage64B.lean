import Janus.Contracts.ErrorfRealStageDefs64

/-!
# Stage B of the real-format `fmt.errorf` stub (amd64): sign byte of number 1, number 2 up to its decimal loop
-/

namespace Janus.Contracts.ErrorfRealStages64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops64
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfRealCode64 (code64)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stageB64 (s : State) (e tp tl v2 n1 x13v : Nat) (R : Nat → W64) (F : Flags) (m : Janus.Arm64.Memory)
    (hP : Pers64 s R tp tl) (h8 : R 8 = BitVec.ofNat 64 e) (h12 : R 12 = BitVec.ofNat 64 v2) (hv2 : v2 < 2 ^ 64)
    (h7 : R 7 = BitVec.ofNat 64 n1) (hn1 : n1 ≤ 1) (h13 : R 13 = BitVec.ofNat 64 x13v)
    (hsp : 4096 ≤ (s.regs 4).toNat) (hsp' : (s.regs 4).toNat + 48 ≤ 2 ^ 48)
    (hx1 : (s.regs 4).toNat - 4096 + 1 ≤ x13v) (hx2 : x13v ≤ (s.regs 4).toNat - 16)
    (hscr : m.accessible ((s.regs 4).toNat - 4096) (4096 + 8 + 8 * 5) true = true)
    (Q : State → Prop)
    (htail : ∀ (R' : Nat → W64) (F' : Flags) (m' : Janus.Arm64.Memory), Pers64 s R' tp tl → R' 8 = BitVec.ofNat 64 e →
      R' 3 = BitVec.ofNat 64 ((s.regs 4).toNat - 16 - (x13v - n1)) → R' 6 = BitVec.ofNat 64 (x13v - n1) →
      R' 7 = BitVec.ofNat 64 (sgn v2) →
      R' 13 = BitVec.ofNat 64 ((s.regs 4).toNat - 48 - (natBytes (absn v2)).length) →
      m' = putBytes (m.writeLE (x13v - 1) 1 (48 - 3 * n1)) ((s.regs 4).toNat - 48 - (natBytes (absn v2)).length)
        (natBytes (absn v2)) →
      ReachesRet (withCode code64) (retAddrOf s) { s with regs := R', flags := F', mem := m', rip := 0x1000a7#64 } Q) :
    ReachesRet (withCode code64) (retAddrOf s) { s with regs := R, flags := F, mem := m, rip := 0x100051#64 } Q := by
  obtain ⟨hP9, hP10, hP4, hP5, hP14⟩ := hP
  have hlen2 := natBytes_length_le (absn v2) 19 (by omega) (by have := natAbs_lt _ hv2; unfold absn; omega)
  have hlenp2 := natBytes_length_pos (absn v2)
  janus64_run [h12, h13, h7, hP4] until [0x100093]
  have e : (4294967296 - (n1 + n1 * 2) % 4294967296 + 48) % 256 = 48 - 3 * n1 := by omega
  rw [e]
  refine dig64_n2 s (absn v2) _ _ _ ((s.regs 4).toNat - 48) (by have := natAbs_lt _ hv2; unfold absn; omega) ?_ ?_
    (by simp [setRegF]) (by omega) (by omega) ?_ _ ?_
  · simp [setRegF]; exact abs64 _ hv2
  · simp [setRegF]; exact bv_sub_lit _ 48 (by omega) (by omega)
  · simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_mono _ hscr (by omega) (by omega)
  · intro c F'
    refine htail _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [setRegF, hP9, hP10, hP4, hP5, hP14]
    · simp [setRegF, h8]
    · simp [setRegF]
      apply BitVec.eq_of_toNat_eq
      have := (s.regs 4).isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · simp [setRegF]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · simp [setRegF]; simpa [sgn] using neg64 _ hv2
    · simp [setRegF]

end Janus.Contracts.ErrorfRealStages64
