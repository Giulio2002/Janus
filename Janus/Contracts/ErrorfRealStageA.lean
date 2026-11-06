import Janus.Contracts.ErrorfRealStageDefs

/-!
# Stages of the real-format `fmt.errorf` stub (arm64)

The run of `ErrorfRealCode.code` between loops, one lemma per stage, each with a small context: the
stage runs its straight-line code, applies the next loop lemma (`ErrorfRealLoops`) and hands the state at
the loop's exit to its continuation. `ErrorfRealSat.real_impl` chains them.
-/

namespace Janus.Contracts.ErrorfRealStages

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops
open Janus.Contracts.RelocArm64 (codeProg)
open Janus.Contracts.ErrorfRealCode (code E0)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- From the entry to the exit of the first decimal loop (`n1`). -/
theorem stageA (s : State) (h30b : (s.regs 30).toNat < 2 ^ 48) (h30a : (s.regs 30).toNat % 4 = 0)
    (hpc : s.pc = 0x1000000000000#64) (e tp tl q1 q2 v1 v2 : Nat)
    (hS48 : s.mem.accessible (s.regs 2).toNat 48 false = true) (hS48' : (s.regs 2).toNat + 48 ≤ 2 ^ 48)
    (he : s.mem.readLE ((s.regs 2).toNat + 8) 8 = e)
    (hE : s.mem.accessible e 16 false = true) (hE' : e + 16 ≤ 2 ^ 48)
    (htp : s.mem.readLE e 8 = tp) (htl : s.mem.readLE (e + 8) 8 = tl)
    (hq1 : s.mem.readLE ((s.regs 2).toNat + 24) 8 = q1) (hQ1 : s.mem.accessible q1 8 false = true)
    (hQ1' : q1 + 8 ≤ 2 ^ 48) (hv1 : s.mem.readLE q1 8 = v1)
    (hq2 : s.mem.readLE ((s.regs 2).toNat + 40) 8 = q2) (hQ2 : s.mem.accessible q2 8 false = true)
    (hQ2' : q2 + 8 ≤ 2 ^ 48) (hv2 : s.mem.readLE q2 8 = v2)
    (hsp : 4096 ≤ s.sp.toNat) (hsp' : s.sp.toNat + 48 ≤ 2 ^ 48)
    (hscr : s.mem.accessible (s.sp.toNat - 4096) (4096 + 8 + 8 * 5) true = true)
    (Q : State → Prop)
    (htail : ∀ (R : Nat → W64) (F : Flags) (m : Memory), Pers s R e tp tl → R 9 = BitVec.ofNat 64 v2 →
      R 12 = BitVec.ofNat 64 (sgn v1) →
      R 13 = BitVec.ofNat 64 (s.sp.toNat - 16 - (natBytes (absn v1)).length) →
      m = putBytes s.mem (s.sp.toNat - 16 - (natBytes (absn v1)).length) (natBytes (absn v1)) →
      ReachesRet (codeProg E0 code) (s.regs 30) { s with regs := R, flags := F, mem := m, pc := 0x1000000000048#64 } Q) :
    ReachesRet (codeProg E0 code) (s.regs 30) s Q := by
  subst he htp htl hq1 hv1 hq2 hv2
  have hv1' : s.mem.readLE (s.mem.readLE ((s.regs 2).toNat + 24) 8) 8 < 2 ^ 64 := by
    have := Memory.readLE_lt s.mem (s.mem.readLE ((s.regs 2).toNat + 24) 8) 8; simpa using this
  have hlen1 := natBytes_length_le (absn (s.mem.readLE (s.mem.readLE ((s.regs 2).toNat + 24) 8) 8)) 19 (by omega)
    (by have := natAbs_lt _ hv1'; unfold absn; omega)
  have hlenp1 := natBytes_length_pos (absn (s.mem.readLE (s.mem.readLE ((s.regs 2).toNat + 24) 8) 8))
  janus_run until [0x1000000000030]
  refine dig_n1 s h30b h30a (absn (s.mem.readLE (s.mem.readLE ((s.regs 2).toNat + 24) 8) 8)) _ _ _
    (s.sp.toNat - 16) (by have := natAbs_lt _ hv1'; unfold absn; omega) ?_ ?_ (by simp [setReg]) (by simp [setReg])
    (by omega) (by omega) ?_ _ ?_
  · simp only [setReg, if_true]; exact abs_bv _ hv1'
  · simp only [setReg]
    rw [if_neg (by decide)]
    exact bv_sub_lit _ 16 (by omega) (by omega)
  · exact Memory.accessible_mono _ hscr (by omega) (by omega)
  · intro c
    refine htail _ _ _ ?_ ?_ ?_ ?_ rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [setReg]
    · simp [setReg]
    · simp [setReg, sgn]; exact neg_bv _ hv1'
    · simp [setReg]

end Janus.Contracts.ErrorfRealStages
