import Janus.Contracts.ErrorfRealStageDefs

/-!
# Stage B of the real-format `fmt.errorf` stub (arm64): sign byte of number 1, number 2 up to its decimal loop
-/

namespace Janus.Contracts.ErrorfRealStages

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops
open Janus.Contracts.AllocSat (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfRealCode (code)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- From the exit of the decimal loop of number 1 to the exit of that of number 2. -/
theorem stageB (s : State) (h30b : (s.regs 30).toNat < 2 ^ 48) (h30a : (s.regs 30).toNat % 4 = 0)
    (e tp tl v2 n1 x13v : Nat) (R : Nat → W64) (F : Flags) (m : Memory)
    (hP : Pers s R e tp tl) (h9 : R 9 = BitVec.ofNat 64 v2) (hv2 : v2 < 2 ^ 64)
    (h12 : R 12 = BitVec.ofNat 64 n1) (hn1 : n1 ≤ 1) (h13 : R 13 = BitVec.ofNat 64 x13v)
    (hsp : 4096 ≤ s.sp.toNat) (hsp' : s.sp.toNat + 48 ≤ 2 ^ 48)
    (hx1 : s.sp.toNat - 4096 + 1 ≤ x13v) (hx2 : x13v + 20 ≤ s.sp.toNat)
    (hscr : m.accessible (s.sp.toNat - 4096) (4096 + 8 + 8 * 5) true = true)
    (Q : State → Prop)
    (htail : ∀ (R' : Nat → W64) (F' : Flags) (m' : Memory), Pers s R' e tp tl →
      R' 25 = BitVec.ofNat 64 (s.sp.toNat - 16 - (x13v - n1)) → R' 26 = BitVec.ofNat 64 (x13v - n1) →
      R' 12 = BitVec.ofNat 64 (sgn v2) →
      R' 13 = BitVec.ofNat 64 (s.sp.toNat - 48 - (natBytes (absn v2)).length) →
      m' = putBytes (m.writeLE (x13v - 1) 1 (48 - 3 * n1)) (s.sp.toNat - 48 - (natBytes (absn v2)).length)
        (natBytes (absn v2)) →
      ReachesRet (withCode code) (s.regs 30) { s with regs := R', flags := F', mem := m', pc := 0x100090#64 } Q) :
    ReachesRet (withCode code) (s.regs 30) { s with regs := R, flags := F, mem := m, pc := 0x100048#64 } Q := by
  obtain ⟨hP5, hP6, hP7, hP15, hP18, hP28, hP29, hP30⟩ := hP
  have hlen2 := natBytes_length_le (absn v2) 19 (by omega) (by have := natAbs_lt _ hv2; unfold absn; omega)
  have hlenp2 := natBytes_length_pos (absn v2)
  janus_run [h9, h12, h13, hP30] until [0x100078]
  have hx13 : x13v < 2 ^ 48 := by omega
  refine dig_n2 s h30b h30a (absn v2) _ _ _ (s.sp.toNat - 48) (by have := natAbs_lt _ hv2; unfold absn; omega) ?_ ?_
    (by simp [setReg, hP15]) (by simp [setReg, hP30]) (by omega) (by omega) ?_ _ ?_
  · simp only [setReg, if_true]; exact abs_bv _ hv2
  · simp [setReg]
    exact bv_sub_lit _ 48 (by omega) (by omega)
  · simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact Memory.accessible_mono _ hscr (by omega) (by omega)
  · intro c
    have e : (18446744073709551616 - (n1 + n1 * 2) + 48) % 18446744073709551616 = 48 - 3 * n1 := by omega
    refine htail _ _ _ ?_ ?_ ?_ ?_ ?_ (by rw [e])
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [setReg, hP5, hP6, hP7, hP15, hP18, hP28, hP29, hP30]
    · simp [setReg]
      apply BitVec.eq_of_toNat_eq
      have := s.sp.isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · simp [setReg]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · simp [setReg, sgn]; exact neg_bv _ hv2
    · simp [setReg]

end Janus.Contracts.ErrorfRealStages
