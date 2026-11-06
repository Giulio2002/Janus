import Janus.Contracts.ErrorfRealStageDefs64

/-!
# Stage C of the real-format `fmt.errorf` stub (amd64): sign byte of number 2, lengths, allocation, the object's fields and the copy of the text
-/

namespace Janus.Contracts.ErrorfRealStages64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Toy Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealLoops64
open Janus.Contracts.RelocAmd64 (codeProg64)
open Janus.Contracts.ErrorfRealCode64 (code64 E0)
open Janus.Contracts.ErrorfRealStages

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stageC64 (s : State) (e tp tl n2 x13v2 len1 st1 p iE : Nat) (R : Nat → W64) (F : Flags) (m : Janus.Arm64.Memory)
    (hP : Pers64 s R tp tl) (h8 : R 8 = BitVec.ofNat 64 e) (h7 : R 7 = BitVec.ofNat 64 n2) (hn2 : n2 ≤ 1)
    (h13 : R 13 = BitVec.ofNat 64 x13v2) (h3 : R 3 = BitVec.ofNat 64 len1) (h6 : R 6 = BitVec.ofNat 64 st1)
    (hsp : 4096 ≤ (s.regs 4).toNat) (hsp' : (s.regs 4).toNat + 48 ≤ 2 ^ 48)
    (hx1 : (s.regs 4).toNat - 4096 + 1 ≤ x13v2) (hx2 : x13v2 ≤ (s.regs 4).toNat - 48) (hn : n2 ≤ x13v2)
    (hlen1 : len1 ≤ 20) (htl : tl < 2 ^ 32)
    (hscr : m.accessible ((s.regs 4).toNat - 4096) (4096 + 8 + 8 * 5) true = true)
    (hscrB : (s.regs 4).toNat ≤ 4194304 ∨ 4194312 + 4096 ≤ (s.regs 4).toNat)
    (hscrH : (s.regs 4).toNat ≤ 268435456 ∨ 536870912 + 4096 ≤ (s.regs 4).toNat)
    (hacB : m.accessible 4194304 8 true = true) (hH : m.accessible 268435456 268435456 true = true)
    (hp : m.readLE 4194304 8 = p) (hp1 : 268435456 ≤ p)
    (hiE : iE < 2 ^ 64) (hI : m.readLE 4194688 8 = iE) (hIa : m.accessible 4194688 8 false = true)
    (hxc : x13v2 ≤ 4194688 ∨ 4194696 ≤ x13v2 - 1)
    (hp2 : p + atot (tl + len1 + ((s.regs 4).toNat - 48 - (x13v2 - n2)) + 20) ≤ 536870912)
    (hp3 : p + 32 ≤ 536870912)
    (hdisj : tp + tl ≤ p + 32 ∨ p + 32 + tl ≤ tp) (htp : tp + tl ≤ 2 ^ 48)
    (hsrc : tl = 0 ∨ m.accessible tp tl false = true)
    (Q : State → Prop)
    (htail : ∀ (R' : Nat → W64) (F' : Flags) (m' : Janus.Arm64.Memory), Pers64 s R' tp tl →
      R' 3 = BitVec.ofNat 64 len1 → R' 6 = BitVec.ofNat 64 st1 →
      R' 13 = BitVec.ofNat 64 (x13v2 - n2) →
      R' 11 = BitVec.ofNat 64 (p + 32 + tl) → R' 8 = BitVec.ofNat 64 p →
      m' = putBytes (allocMemC m x13v2 n2 p (atot (tl + len1 + ((s.regs 4).toNat - 48 - (x13v2 - n2)) + 20))
          (tl + len1 + ((s.regs 4).toNat - 48 - (x13v2 - n2)) + 20) e iE) (p + 32)
        (strBytes (allocMemC m x13v2 n2 p (atot (tl + len1 + ((s.regs 4).toNat - 48 - (x13v2 - n2)) + 20))
          (tl + len1 + ((s.regs 4).toNat - 48 - (x13v2 - n2)) + 20) e iE) tp tl) →
      ReachesRet (codeProg64 E0 code64) (retAddrOf s) { s with regs := R', flags := F', mem := m', rip := 0x400000000128#64 } Q) :
    ReachesRet (codeProg64 E0 code64) (retAddrOf s) { s with regs := R, flags := F, mem := m, rip := 0x4000000000ab#64 } Q := by
  obtain ⟨hP9, hP10, hP4, hP5, hP14, hP15⟩ := hP
  janus64_run [h8, h7, h13, h3, h6, hP9, hP10, hP4, hp, hI] until [0x400000000113]
  have hL : tl + (len1 + 20) + (18446744073709551616 - (18446744073709551616 - n2 + x13v2) % 18446744073709551616 +
      (BitVec.toNat (s.regs 4) - 48)) % 18446744073709551616 =
      tl + len1 + ((s.regs 4).toNat - 48 - (x13v2 - n2)) + 20 := by omega
  have hA : (BitVec.ofNat 64 ((tl + len1 + ((s.regs 4).toNat - 48 - (x13v2 - n2)) + 20 +
      (tl + len1 + ((s.regs 4).toNat - 48 - (x13v2 - n2)) + 20) + 63) / 16) * 16#64).toNat + p =
      p + atot (tl + len1 + ((s.regs 4).toNat - 48 - (x13v2 - n2)) + 20) := by
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, atot]
    unfold atot at hp2
    omega
  simp only [hL, hA]
  have eb : (4294967296 - (n2 + n2 * 2) % 4294967296 + 48) % 256 = 48 - 3 * n2 := by omega
  rw [eb]
  have hat : 2 * (tl + len1 + ((s.regs 4).toNat - 48 - (x13v2 - n2)) + 20) + 48 ≤
      atot (tl + len1 + ((s.regs 4).toNat - 48 - (x13v2 - n2)) + 20) := by
    unfold atot; omega
  refine cpy64_c1 s tl _ _ _ tp (p + 32) (by omega) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]) (by omega) (by omega) hdisj ?_ ?_ _ ?_
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hsrc
  · by_cases hz : tl = 0
    · exact Or.inl hz
    · right
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Arm64.Memory.accessible_mono _ hH (by omega) (by omega)
  · intro c F'
    refine htail _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [setRegF, hP9, hP10, hP4, hP5, hP14, hP15]
    · simp [setRegF, h3]
    · simp [setRegF, h6]
    · simp [setRegF]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · simp [setRegF]
    · simp [setRegF]

end Janus.Contracts.ErrorfRealStages64
