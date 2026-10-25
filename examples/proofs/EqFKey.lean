import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Mem
  Janus.Float

namespace Proof

/-- Go's `==` on the `FKey`s at `p` and `q` in `m`: the floats `feq`, then the strings. -/
def keyEq (m : Memory) (p q : Nat) : Bool :=
  feq binary64 (m.readLE p 8) (m.readLE q 8) && strEq m (p + 8) (q + 8)

/-- The stack window of the equality function and its `memequal` call. -/
def window (d : Nat) (s : State) : List (Nat × Nat) := callerWindow s d 16 0

/-- A key at `p` is an input: its 24 bytes and its string's bytes readable and outside the
window. -/
def KeyInput (d : Nat) (s : State) (p : Nat) : Prop :=
  p + 24 ≤ 2 ^ 48 ∧ s.mem.accessible p 24 false = true ∧ Outside p 24 (window d s) ∧
    strPtr s.mem (p + 8) + strLen s.mem (p + 8) ≤ 2 ^ 48 ∧
    s.mem.accessible (strPtr s.mem (p + 8)) (strLen s.mem (p + 8)) false = true ∧
    Outside (strPtr s.mem (p + 8)) (strLen s.mem (p + 8)) (window d s)

theorem correctness (impl : List Segment) (d : Nat)
    (hmem : Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d)
    (p q : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p, q]
      (fun s => CallerOK s d 16 0 ∧ s.fpcr = 0 ∧ KeyInput d s p.toNat ∧ KeyInput d s q.toNat)
      (fun s s' => (s'.regs 0).toNat % 256 = (keyEq s.mem p.toNat q.toNat).toNat) := by
  intro ret hret s hs ⟨hc, hfp, ⟨hpb, hpa, hpo, hpsb, hpsa, hpso⟩, ⟨hqb, hqa, hqo, hqsb, hqsa, hqso⟩⟩
  have hc' := hc
  obtain ⟨⟨hg1, hg2, hg3⟩, hal, hd8, hdd, hb, hst, hog⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  simp only [window, callerWindow, outside_cons, outside_nil, and_true] at hog hpo hqo hpso hqso
  have hm : ∀ a, s.mem.readLE a 8 % 340282366920938463463374607431768211456 = s.mem.readLE a 8 :=
    fun a => Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Memory.readLE_lt _ _ 8) (by decide))
  have hsp : (s.sp - 16#64).toNat = s.sp.toNat - 16 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; try simp
  janus_run until [Extracted.program.contractAddr "runtime.memequal"]
  all_goals simp only [hm] at *
  · simp [keyEq, hbr]
  · rename_i hlen
    have hptrp : s.mem.readLE (p.toNat + 8) 8 = strPtr s.mem (p.toNat + 8) := rfl
    have hptrq : s.mem.readLE (q.toNat + 8) 8 = strPtr s.mem (q.toNat + 8) := rfl
    have hlp : s.mem.readLE (p.toNat + 16) 8 = strLen s.mem (p.toNat + 8) := rfl
    have hfw : MemFrame s.mem ((s.mem.writeLE (BitVec.toNat s.sp - 16) 8 ret).writeLE
        (BitVec.toNat s.sp - 24) 8 (BitVec.toNat (s.regs 29))) (callerWindow s d 16 0) := by
      simp only [callerWindow]; janus_frame
    have hfw0 := hfw
    simp only [callerWindow, outside_cons, outside_nil, and_true] at hfw
    refine Reaches.call (Summary.withExit hmem hret) rfl ⟨?_, ?_, ?_⟩ ?_
    · exact EqPre.of_caller hc hfw0 (by simp [hsp]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
        (by decide) (by decide)
    · refine Input.of_caller (s := s) (d := d) (frame := 16) (above := 0) hfw0 (by simp [hsp]) (by decide)
        (by omega) ?_ ?_ ?_ <;> dsimp only <;>
        simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hptrp, hlp, hlen,
          Nat.mod_eq_of_lt (show strPtr s.mem (p.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8),
          Nat.mod_eq_of_lt (show strLen s.mem (p.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8)]
      · exact hpsb
      · exact hpsa
      · simp only [callerWindow, outside_cons, outside_nil, and_true]; exact hpso
    · have hlq : strLen s.mem (p.toNat + 8) = strLen s.mem (q.toNat + 8) := hlen.symm
      refine Input.of_caller (s := s) (d := d) (frame := 16) (above := 0) hfw0 (by simp [hsp]) (by decide)
        (by omega) ?_ ?_ ?_ <;> dsimp only <;>
        simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hptrq, hlp, hlq,
          Nat.mod_eq_of_lt (show strPtr s.mem (q.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8),
          Nat.mod_eq_of_lt (show strLen s.mem (q.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8)]
      · exact hqsb
      · exact hqsa
      · simp only [callerWindow, outside_cons, outside_nil, and_true]; exact hqso
    · intro s' hpc' ⟨r, v, fl, fs, m', hs', hfr, hres⟩
      subst hs'
      simp only [calleeStack, hsp] at hfr
      janus_run
      have hb1 := hfw.readLE (strPtr s.mem (p.toNat + 8)) (strLen s.mem (p.toNat + 8))
        (by simp only [outside_cons, outside_nil, and_true]; exact hpso)
      have hb2 := hfw.readLE (strPtr s.mem (q.toNat + 8)) (strLen s.mem (q.toNat + 8))
        (by simp only [outside_cons, outside_nil, and_true]; exact hqso)
      have hlq : strLen s.mem (q.toNat + 8) = strLen s.mem (p.toNat + 8) := hlen
      simp only [BoolRes, setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hptrp, hptrq, hlp,
        Nat.mod_eq_of_lt (show strPtr s.mem (p.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8),
        Nat.mod_eq_of_lt (show strPtr s.mem (q.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8),
        Nat.mod_eq_of_lt (show strLen s.mem (p.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8)] at hres
      rw [hb1, ← hlq, hb2, hlq] at hres
      have hf' : feq binary64 (s.mem.readLE p.toNat 8) (s.mem.readLE q.toNat 8) = true := by
        simpa using hbr
      simp only [keyEq, strEq, hf', hlq, beq_self_eq_true, Bool.true_and]
      exact hres
  · rename_i hlen
    have hne : (strLen s.mem (p.toNat + 8) == strLen s.mem (q.toNat + 8)) = false := by
      simp only [strLen, Nat.add_assoc, Nat.reduceAdd, beq_eq_false_iff_ne, ne_eq]
      exact fun h => hlen h.symm
    simp [keyEq, strEq, hne]

end Proof
