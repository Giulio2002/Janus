import Janus.Contracts.ErrorfRealStageDefs

/-!
# Stage C of the real-format `fmt.errorf` stub (arm64): sign byte of number 2, lengths, allocation, the
object's fields, and the copy of the errorString's text
-/

namespace Janus.Contracts.ErrorfRealStages

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops
open Janus.Contracts.AllocSat (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfRealCode (code)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The total advance of the bump pointer for a message of `Lm` bytes. -/
def atot (Lm : Nat) : Nat := (Lm + Lm + 63) / 16 * 16

/-- From the exit of the decimal loop of number 2 to the exit of the text copy. -/
theorem stageC (s : State) (h30b : (s.regs 30).toNat < 2 ^ 48) (h30a : (s.regs 30).toNat % 4 = 0)
    (e tp tl n2 x13v2 len1 st1 p : Nat) (R : Nat → W64) (F : Flags) (m : Memory)
    (hP : Pers s R e tp tl) (h12 : R 12 = BitVec.ofNat 64 n2) (hn2 : n2 ≤ 1)
    (h13 : R 13 = BitVec.ofNat 64 x13v2) (h25 : R 25 = BitVec.ofNat 64 len1) (h26 : R 26 = BitVec.ofNat 64 st1)
    (hsp : 4096 ≤ s.sp.toNat) (hsp' : s.sp.toNat + 48 ≤ 2 ^ 48)
    (hx1 : s.sp.toNat - 4096 + 1 ≤ x13v2) (hx2 : x13v2 ≤ s.sp.toNat - 48) (hn : n2 ≤ x13v2)
    (hlen1 : len1 ≤ 20) (htl : tl < 2 ^ 32)
    (hscr : m.accessible (s.sp.toNat - 4096) (4096 + 8 + 8 * 5) true = true)
    (hscrB : s.sp.toNat ≤ 4194304 ∨ 4194312 + 4096 ≤ s.sp.toNat)
    (hscrH : s.sp.toNat ≤ 268435456 ∨ 536870912 + 4096 ≤ s.sp.toNat)
    (hacB : m.accessible 4194304 8 true = true) (hH : m.accessible 268435456 268435456 true = true)
    (hp : m.readLE 4194304 8 = p) (hp1 : 268435456 ≤ p)
    (hp2 : p + atot (tl + len1 + (s.sp.toNat - 48 - (x13v2 - n2)) + 20) ≤ 536870912)
    (hp3 : p + 32 ≤ 536870912)
    (hdisj : tp + tl ≤ p + 32 ∨ p + 32 + tl ≤ tp) (htp : tp + tl ≤ 2 ^ 48)
    (hsrc : tl = 0 ∨ m.accessible tp tl false = true)
    (Q : State → Prop)
    (htail : ∀ (R' : Nat → W64) (F' : Flags) (m' : Memory), Pers s R' e tp tl →
      R' 25 = BitVec.ofNat 64 len1 → R' 26 = BitVec.ofNat 64 st1 →
      R' 21 = BitVec.ofNat 64 (s.sp.toNat - 48 - (x13v2 - n2)) → R' 22 = BitVec.ofNat 64 (x13v2 - n2) →
      R' 11 = BitVec.ofNat 64 (p + 32 + tl) → R' 1 = BitVec.ofNat 64 p →
      m' = putBytes (allocMem m x13v2 n2 p (atot (tl + len1 + (s.sp.toNat - 48 - (x13v2 - n2)) + 20))
          (tl + len1 + (s.sp.toNat - 48 - (x13v2 - n2)) + 20) e) (p + 32)
        (strBytes (allocMem m x13v2 n2 p (atot (tl + len1 + (s.sp.toNat - 48 - (x13v2 - n2)) + 20))
          (tl + len1 + (s.sp.toNat - 48 - (x13v2 - n2)) + 20) e) tp tl) →
      ReachesRet (withCode code) (s.regs 30) { s with regs := R', flags := F', mem := m', pc := 0x100118#64 } Q) :
    ReachesRet (withCode code) (s.regs 30) { s with regs := R, flags := F, mem := m, pc := 0x100090#64 } Q := by
  obtain ⟨hP5, hP6, hP7, hP15, hP18, hP28, hP29, hP30⟩ := hP
  janus_run [h12, h13, h25, h26, hP5, hP6, hP7, hP30, hp] until [0x100104]
  have hL : tl + (18446744073709551616 - (18446744073709551616 - n2 + x13v2) % 18446744073709551616 +
      (BitVec.toNat s.sp - 48)) % 18446744073709551616 + (len1 + 20) =
      tl + len1 + (s.sp.toNat - 48 - (x13v2 - n2)) + 20 := by omega
  have hA : (BitVec.ofNat 64 ((tl + len1 + (s.sp.toNat - 48 - (x13v2 - n2)) + 20 +
      (tl + len1 + (s.sp.toNat - 48 - (x13v2 - n2)) + 20) + 63) / 16) * 16#64).toNat =
      atot (tl + len1 + (s.sp.toNat - 48 - (x13v2 - n2)) + 20) := by
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, atot]
    unfold atot at hp2
    omega
  simp only [hL, hA]
  have eb : (18446744073709551616 - (n2 + n2 * 2) + 48) % 18446744073709551616 = 48 - 3 * n2 := by omega
  rw [eb]
  have hat : 2 * (tl + len1 + (s.sp.toNat - 48 - (x13v2 - n2)) + 20) + 48 ≤ atot (tl + len1 + (s.sp.toNat - 48 - (x13v2 - n2)) + 20) := by
    unfold atot; omega
  refine cpy_c1 s h30b h30a tl _ _ _ tp (p + 32) (by omega) (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat])
    (by simp [setReg, hP30]) (by omega) (by omega) hdisj ?_ ?_ _ ?_
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hsrc
  · by_cases hz : tl = 0
    · exact Or.inl hz
    · right
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      exact Memory.accessible_mono _ hH (by omega) (by omega)
  · intro c
    refine htail _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [setReg, hP5, hP6, hP7, hP15, hP18, hP28, hP29, hP30]
    · simp [setReg, h25]
    · simp [setReg, h26]
    · simp [setReg]
      apply BitVec.eq_of_toNat_eq
      have := s.sp.isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · simp [setReg]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · simp [setReg]
    · simp [setReg]

end Janus.Contracts.ErrorfRealStages
