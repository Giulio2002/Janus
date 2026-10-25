import Janus
import Extracted

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Mem
open Janus (MemFrame Outside outside_cons outside_nil)

/-- The precondition (see the module documentation). -/
def pre (d : Nat) (p1 l1 p2 l2 : BitVec 64) (s : State) : Prop :=
  MemAmd64.CallerOK s d 40 40 ∧ Buffer s p1 l1.toNat false ∧ Buffer s p2 l2.toNat false ∧
    Outside p1.toNat l1.toNat (MemAmd64.callerWindow s d 40 40) ∧
    Outside p2.toNat l2.toNat (MemAmd64.callerWindow s d 40 40)

theorem correctness (impl : List Segment) (d : Nat)
    (hmem : MemAmd64.Memequal (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memequal") d)
    (p1 l1 p2 l2 : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p1, l1, p2, l2] (pre d p1 l1 p2 l2)
      (fun s s' => (s'.regs 0).toNat % 256 =
        (l1 == l2 && s.mem.readLE p1.toNat l1.toNat == s.mem.readLE p2.toNat l2.toNat).toNat) := by
  intro ret hret s hs ⟨hc, ⟨hP1', hP1⟩, ⟨hP2', hP2⟩, ho1, ho2⟩
  janus64_intro hs
  have hc' := hc
  obtain ⟨hg, hal, hd, hb, hst, hog⟩ := hc'
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  simp only [outside_cons, outside_nil, and_true] at hog
  by_cases hl : l1 = l2
  · subst hl
    have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
      rw [BitVec.toNat_sub]; simp; omega
    janus64_run until [Extracted.program.contractAddr "runtime.memequal"]
    have hfw : MemFrame s.mem ((((Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
        (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) + 8) 8 p1.toNat).writeLE
        (BitVec.toNat (s.regs 4) + 24) 8 p2.toNat).writeLE (BitVec.toNat (s.regs 4) - 40) 8 4740976)
        (MemAmd64.callerWindow s d 40 40) := by
      simp only [MemAmd64.callerWindow]; janus_frame
    refine Reaches.call (Summary.withExit hmem hret) rfl
      ⟨MemAmd64.EqPre.of_caller hc hfw (by simp [setRegF, hsp40]) (by simp [setRegF])
        (by simpa using hs.zero) (by simpa using hs.df)
        (by simp [setRegF, hsp40, Janus.Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide),
       MemAmd64.Input.of_caller hfw (by simp [setRegF, hsp40]) (by decide) (by omega)
         (by simpa [setRegF, h_a0] using hP1') (by simpa [setRegF, h_a0] using hP1)
         (by simpa [setRegF, h_a0] using ho1),
       MemAmd64.Input.of_caller hfw (by simp [setRegF, hsp40]) (by decide) (by omega)
         (by simpa [setRegF, h_a2] using hP2') (by simpa [setRegF, h_a2] using hP2)
         (by simpa [setRegF, h_a2] using ho2)⟩ ?_
    intro s' hpc' ⟨r, x, y, fl, mx, m', hs', hmx, hfr, hres⟩
    subst hs'
    simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte,
      Nat.reduceEqDiff, hsp40] at hfr
    simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, h_a0, h_a2, hfw.readLE _ _ ho1,
      hfw.readLE _ _ ho2] at hres
    janus64_run
    exact hres
  · have hl' : l1.toNat ≠ l2.toNat := fun h => hl (BitVec.eq_of_toNat_eq h)
    janus64_run
    simp [beq_false_of_ne hl]

end Proof
