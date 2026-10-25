import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem

namespace Proof

/-- The stack window of `ClearTrees` and the runtime call. -/
def window (d : Nat) (s : State) : List (Nat × Nat) := callerWindow s d 32 32

/-- The precondition: see the module documentation. -/
def pre (M : MemModel) (wb d : Nat) (p n : BitVec 64) (s : State) : Prop :=
  CallerOK s d 32 32 ∧ M.Env s.mem (s.regs 28) ∧ Outside (s.sp.toNat - (d + 32)) (d + 64) M.priv ∧
    wb + 4 ≤ 2 ^ 48 ∧ s.mem.accessible wb 4 false = true ∧ Outside wb 4 (window d s) ∧
    WriteBarrierOff s.mem wb ∧ n.toNat < 2 ^ 45 ∧ p.toNat % 8 = 0 ∧
    Ptr s.mem p (8 * n.toNat) true ∧ Outside p.toNat (8 * n.toNat) (window d s) ∧
    Outside p.toNat (8 * n.toNat) M.priv

theorem correctness (impl : List Segment) (M : MemModel) (hl : M.Laws) (wb d : Nat)
    (hclr : MemclrHasPointers (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrHasPointers") M wb d)
    (p n c : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p, n, c] (pre M wb d p n)
      (fun s s' => Zeroed s'.mem p.toNat (8 * n.toNat) ∧
        MemFrame s.mem s'.mem (M.priv ++ window d s ++ [(p.toNat, p.toNat + 8 * n.toNat)])) := by
  intro ret hret s hs ⟨hc, henv, hpriv, hwb1, hwb2, hwbo, hwb, hn, hal8, ⟨hP, hP'⟩, hpo, hpp⟩
  have hc' := hc
  obtain ⟨⟨hg1, hg2, hg3⟩, hal, hd8, hdd, hb, hst, hog⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  simp only [window, callerWindow, outside_cons, outside_nil, and_true] at hog hwbo hpo
  by_cases h0 : n.toNat = 0
  · janus_run
    exact ⟨fun i hi => absurd hi (by omega),
      (show MemFrame s.mem _ (window d s) by simp only [window, callerWindow]; janus_frame).mono
        fun a n h => by simp only [outside_append] at h; exact h.1.2⟩
  · janus_run until [Extracted.program.contractAddr "runtime.memclrHasPointers"]
    have hsp : (s.sp - 32#64).toNat = s.sp.toNat - 32 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; try simp
    have h8n : (n.rotateRight 61 &&& 18446744073709551608#64 &&& 18446744073709551615#64).toNat =
        8 * n.toNat := by
      rw [BitVec.toNat_and, BitVec.toNat_and]
      simp only [BitVec.toNat_ofNat]
      rw [show (18446744073709551615 % 2 ^ 64) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        show 18446744073709551608 % 2 ^ 64 = 18446744073709551608 from rfl, Iface.lsl3_toNat]
      omega
    have hfw : MemFrame s.mem (((s.mem.writeLE (BitVec.toNat s.sp - 32) 8 ret).writeLE
        (BitVec.toNat s.sp - 40) 8 (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 8) 8 p.toNat)
        (callerWindow s d 32 32) := by
      simp only [callerWindow]; janus_frame
    obtain ⟨hsg, hcall, hgo⟩ := EqPre.of_caller (S := { s with
        regs := setReg (setReg (setReg (setReg s.regs 1
            (n.rotateRight 61 &&& 18446744073709551608#64 &&& 18446744073709551615#64)) 16
            (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 28) + 16) 8))) 29 (s.sp - 40#64)) 30 588984#64,
        sp := s.sp - 32#64, pc := 537424#64,
        flags := (addSub s.sp (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 28) + 16) 8)) true).snd,
        mem := ((s.mem.writeLE (BitVec.toNat s.sp - 32) 8 ret).writeLE (BitVec.toNat s.sp - 40) 8
          (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 8) 8 p.toNat }) (nargs := 2) hc hfw
        (by simp [hsp]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) (by decide) (by decide)
    simp only [callerWindow, outside_cons, outside_nil, and_true] at hfw
    refine Reaches.call (Summary.withExit hclr hret) rfl
      ⟨⟨?_, hsg, hcall, ?_, ?_, ?_, hgo⟩, ?_, ?_, ?_⟩ ?_
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      exact hl.env_frame _ _ _ henv (Agrees.of_window (lo := s.sp.toNat - (d + 32)) (hi := s.sp.toNat + 32)
        (by janus_frame) (Outside.of_sub hpriv (by omega) (by omega)))
    · simp only [hsp]; exact Outside.of_sub hpriv (by omega) (by omega)
    · refine ⟨hwb1, by simpa using hwb2, ?_⟩
      simp only [calleeStack, hsp, outside_cons, outside_nil, and_true]; omega
    · unfold WriteBarrierOff at hwb ⊢
      simp only; rw [hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hwb
    · simpa [setReg, h_x0] using hal8
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, h8n]; omega
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, h8n, h_x0]
      refine ⟨hP', by simpa using hP, ?_, hpp⟩
      simp only [calleeStack, hsp, outside_cons, outside_nil, and_true]; omega
    · intro s' hpc' ⟨r, v, fl, fs, m', hs', hfr, henv', hz⟩
      subst hs'
      simp only [calleeStack, hsp] at hfr
      simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, h8n, h_x0] at hz hfr
      janus_run
      refine ⟨hz, hfw.trans hfr fun a k h => ?_⟩
      simp only [window, callerWindow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨hp, hw⟩, hds⟩ := h
      exact ⟨hw, ⟨hp, by omega, by omega⟩, hds⟩

end Proof
