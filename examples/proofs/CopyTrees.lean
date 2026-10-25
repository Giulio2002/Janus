import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem

namespace Proof

/-- The type descriptor `CopyTrees` passes (`[2]Tree`, recomputed from the `ADRP`+`ADD`). -/
def treesType : Nat :=
  adrpLdTarget (Extracted.entry + 0x28) (segWord Extracted.program "example.com/basic.CopyTrees" 10)
    (segWord Extracted.program "example.com/basic.CopyTrees" 11) 0

/-- The stack window of `CopyTrees` and the runtime call. -/
def window (d : Nat) (s : State) : List (Nat × Nat) := callerWindow s d 48 24

/-- The precondition: see the module documentation. -/
def pre (M : MemModel) (wb d : Nat) (dst src : BitVec 64) (s : State) : Prop :=
  CallerOK s d 48 24 ∧ M.Env s.mem (s.regs 28) ∧ Outside ((s.regs 28).toNat + 16) 8 M.priv ∧ Outside (s.sp.toNat - (d + 48)) (d + 72) M.priv ∧
    Extracted.program.DataLoaded s.mem ∧ Outside treesType 16 (window d s) ∧
    wb + 4 ≤ 2 ^ 48 ∧ s.mem.accessible wb 4 false = true ∧ Outside wb 4 (window d s) ∧
    WriteBarrierOff s.mem wb ∧
    Ptr s.mem src 128 false ∧ Outside src.toNat 128 (window d s) ∧
    Ptr s.mem dst 128 true ∧ Outside dst.toNat 128 (window d s) ∧ Outside dst.toNat 128 M.priv

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (M : MemModel) (hl : M.Laws) (wb d : Nat)
    (hmv : TypedMemmove (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typedmemmove") M wb d)
    (dst src : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [dst, src] (pre M wb d dst src)
      (fun s s' => Copied s.mem s'.mem dst.toNat src.toNat 128 ∧
        MemFrame s.mem s'.mem (M.priv ++ window d s ++ [(dst.toNat, dst.toNat + 128)])) := by
  intro ret hret s hs ⟨hc, henv, hgp, hpriv, hd, hto, hwb1, hwb2, hwbo, hwb, ⟨hS, hS'⟩, hso, ⟨hD, hD'⟩, hdo, hdp⟩
  have hc' := hc
  obtain ⟨⟨hg1, hg2, hg3⟩, hal, hd8, hdd, hb, hst, hog⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : treesType
  rw [hT] at hto
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  simp only [window, callerWindow, outside_cons, outside_nil, and_true] at hog hto hwbo hso hdo
  janus_data hd [hst]
  janus_run until [Extracted.program.contractAddr "runtime.typedmemmove"]
  have hsp : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; try simp
  have hfw : MemFrame s.mem ((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE
      (BitVec.toNat s.sp - 56) 8 (BitVec.toNat (s.regs 29))) (callerWindow s d 48 24) := by
    simp only [callerWindow]; janus_frame
  have hsz : s.mem.readLE 703328 8 = 128 := by rw [h_rodata _ _ (by decide)]; decide
  obtain ⟨hsg, hcall, hgo⟩ := EqPre.of_caller (S := { s with
      regs := setReg (setReg (setReg (setReg (setReg (setReg (setReg s.regs 0 703328#64) 1 dst) 2 src) 16
                (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 28) + 16) 8))) 27
              (BitVec.ofNat 64 (if s.mem.readLE src.toNat 1 < 128 then s.mem.readLE src.toNat 1
                else s.mem.readLE src.toNat 1 + 18446744073709551360))) 29 (s.sp - 56#64)) 30 588900#64,
      sp := s.sp - 48#64, pc := 536976#64,
      flags := (addSub s.sp (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 28) + 16) 8)) true).snd,
      mem := (s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
        (BitVec.toNat (s.regs 29)) }) (nargs := 3) hc hfw (by simp [hsp]) (by simp [setReg])
      (by simp [setReg]) (by simp [setReg]) (by decide) (by decide)
  simp only [callerWindow, outside_cons, outside_nil, and_true] at hfw
  refine Reaches.call (Summary.withExit hmv hret) rfl
    ⟨⟨?_, hsg, hcall, ?_, ?_, ?_, hgo, by simpa [setReg] using hgp⟩, ?_, ?_, ?_, ?_⟩ ?_
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
    exact hl.env_frame _ _ _ henv (Agrees.of_window (lo := s.sp.toNat - (d + 48)) (hi := s.sp.toNat + 24)
      (by janus_frame) (Outside.of_sub hpriv (by omega) (by omega)))
  · simp only [hsp]; exact Outside.of_sub hpriv (by omega) (by omega)
  · refine ⟨hwb1, by simpa using hwb2, ?_⟩
    simp only [calleeStack, hsp, outside_cons, outside_nil, and_true]; omega
  · unfold WriteBarrierOff at hwb ⊢
    simp only; rw [hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hwb
  · refine ⟨by simp [setReg], by simpa [setReg] using Memory.accessible_mono _ h_data0 (by omega) (by omega)⟩
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, calleeStack, hsp, outside_cons, outside_nil,
      and_true, BitVec.toNat_ofNat]; omega
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, typSize]
    rw [hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hsz]
    refine ⟨hS', by simpa using hS, ?_⟩
    simp only [calleeStack, hsp, outside_cons, outside_nil, and_true]; omega
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, typSize]
    rw [hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hsz]
    refine ⟨hD', by simpa using hD, ?_, hdp⟩
    simp only [calleeStack, hsp, outside_cons, outside_nil, and_true]; omega
  · intro s' hpc' ⟨r, v, fl, fs, m', hs', hfr, henv', hcp⟩
    subst hs'
    simp only [calleeStack, hsp] at hfr
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, typSize] at hcp hfr
    rw [hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hsz] at hcp hfr
    janus_run
    refine ⟨fun i hi => ?_, hfw.trans hfr fun a n h => ?_⟩
    · rw [hcp i hi]
      have := hfw.readLE (src.toNat + i) 1 (by simp only [outside_cons, outside_nil, and_true]; omega)
      simp only [Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
    · simp only [window, callerWindow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨hp, hw⟩, hds⟩ := h
      exact ⟨hw, ⟨hp, by omega, by omega⟩, hds⟩

end Proof
