import Janus.Contracts.ErrorfRealStageDefs64

/-!
# Stage A of the real-format `fmt.errorf` stub (amd64): the loads, number 1 up to the exit of its decimal loop
-/

namespace Janus.Contracts.ErrorfRealStages64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops64
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfRealCode64 (code64)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stageA64 (s : State) (hpc : s.rip = 0x100000#64)
    (e tp tl q1 q2 v1 v2 : Nat)
    (hS48 : s.mem.accessible (s.regs 1).toNat 48 false = true) (hS48' : (s.regs 1).toNat + 48 ≤ 2 ^ 48)
    (he : s.mem.readLE ((s.regs 1).toNat + 8) 8 = e)
    (hE : s.mem.accessible e 16 false = true) (hE' : e + 16 ≤ 2 ^ 48)
    (htp : s.mem.readLE e 8 = tp) (htl : s.mem.readLE (e + 8) 8 = tl)
    (hq1 : s.mem.readLE ((s.regs 1).toNat + 24) 8 = q1) (hQ1 : s.mem.accessible q1 8 false = true)
    (hQ1' : q1 + 8 ≤ 2 ^ 48) (hv1 : s.mem.readLE q1 8 = v1)
    (hq2 : s.mem.readLE ((s.regs 1).toNat + 40) 8 = q2) (hQ2 : s.mem.accessible q2 8 false = true)
    (hQ2' : q2 + 8 ≤ 2 ^ 48) (hv2 : s.mem.readLE q2 8 = v2)
    (hsp : 4096 ≤ (s.regs 4).toNat) (hsp' : (s.regs 4).toNat + 48 ≤ 2 ^ 48)
    (hscr : s.mem.accessible ((s.regs 4).toNat - 4096) (4096 + 8 + 8 * 5) true = true)
    (Q : State → Prop)
    (htail : ∀ (R : Nat → W64) (F : Flags) (m : Janus.Arm64.Memory), Pers64 s R tp tl → R 8 = BitVec.ofNat 64 e →
      R 12 = BitVec.ofNat 64 v2 → R 7 = BitVec.ofNat 64 (sgn v1) →
      R 13 = BitVec.ofNat 64 ((s.regs 4).toNat - 16 - (natBytes (absn v1)).length) →
      m = putBytes s.mem ((s.regs 4).toNat - 16 - (natBytes (absn v1)).length) (natBytes (absn v1)) →
      ReachesRet (withCode code64) (retAddrOf s) { s with regs := R, flags := F, mem := m, rip := 0x100051#64 } Q) :
    ReachesRet (withCode code64) (retAddrOf s) s Q := by
  subst he htp htl hq1 hv1 hq2 hv2
  have hv1' : s.mem.readLE (s.mem.readLE ((s.regs 1).toNat + 24) 8) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt s.mem (s.mem.readLE ((s.regs 1).toNat + 24) 8) 8; simpa using this
  have hlen1 := natBytes_length_le (absn (s.mem.readLE (s.mem.readLE ((s.regs 1).toNat + 24) 8) 8)) 19 (by omega)
    (by have := natAbs_lt _ hv1'; unfold absn; omega)
  have hlenp1 := natBytes_length_pos (absn (s.mem.readLE (s.mem.readLE ((s.regs 1).toNat + 24) 8) 8))
  janus64_run until [0x10003d]
  refine dig64_n1 s (absn (s.mem.readLE (s.mem.readLE ((s.regs 1).toNat + 24) 8) 8)) _ _ _
    ((s.regs 4).toNat - 16) (by have := natAbs_lt _ hv1'; unfold absn; omega) ?_ ?_ (by simp [setRegF]) (by omega) (by omega) ?_ _ ?_
  · simp [setRegF]
    exact abs64 _ hv1'
  · simp [setRegF]
    exact bv_sub_lit _ 16 (by omega) (by omega)
  · exact Janus.Arm64.Memory.accessible_mono _ hscr (by omega) (by omega)
  · intro c F'
    refine htail _ _ _ ?_ ?_ ?_ ?_ ?_ rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]; simpa [sgn] using neg64 _ hv1'
    · simp [setRegF]

end Janus.Contracts.ErrorfRealStages64
