import Janus
import Extracted

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts Janus.Contracts.Mem
open Janus (MemFrame Outside outside_cons outside_nil outside_append)

namespace Proof

/-- The stack window of `ClearTrees` and the runtime call (amd64). -/
def window (d : Nat) (s : State) : List (Nat × Nat) := MemAmd64.callerWindow s d 32 32

/-- The precondition: see the module documentation. -/
def pre (M : MemModel) (wb d : Nat) (p n : BitVec 64) (s : State) : Prop :=
  MemAmd64.CallerOK s d 32 32 ∧ M.Env s.mem (s.regs 14) ∧
    Outside ((s.regs 4).toNat - (d + 32)) (d + 64) M.priv ∧
    wb + 4 ≤ 2 ^ 48 ∧ s.mem.accessible wb 4 false = true ∧ Outside wb 4 (window d s) ∧
    WriteBarrierOff s.mem wb ∧ n.toNat < 2 ^ 45 ∧ p.toNat % 8 = 0 ∧
    Buffer s p (8 * n.toNat) true ∧ Outside p.toNat (8 * n.toNat) (window d s) ∧
    Outside p.toNat (8 * n.toNat) M.priv

theorem correctness (impl : List Segment) (M : MemModel) (hl : M.Laws) (wb d : Nat)
    (hclr : MemAmd64.MemclrHasPointers (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrHasPointers") M wb d)
    (p n c : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p, n, c] (pre M wb d p n)
      (fun s s' => Zeroed s'.mem p.toNat (8 * n.toNat) ∧
        MemFrame s.mem s'.mem (M.priv ++ window d s ++ [(p.toNat, p.toNat + 8 * n.toNat)])) := by
  intro ret hret s hs ⟨hc, henv, hpriv, hwb1, hwb2, hwbo, hwb, hn, hal8, ⟨hP', hP⟩, hpo, hpp⟩
  janus64_intro hs
  have hc' := hc
  obtain ⟨hg, hal, hdd, hb, hst, hog⟩ := hc'
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  simp only [window, MemAmd64.callerWindow, outside_cons, outside_nil, and_true] at hog hwbo hpo
  by_cases h0 : n.toNat = 0
  · janus64_run
    exact ⟨fun i hi => absurd hi (by omega),
      (show MemFrame s.mem _ (window d s) by simp only [window, MemAmd64.callerWindow]; janus_frame).mono
        fun a n h => by simp only [outside_append] at h; exact h.1.2⟩
  · janus64_run until [Extracted.program.contractAddr "runtime.memclrHasPointers"]
    have hsp32 : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
      rw [BitVec.toNat_sub]; simp; omega
    have h8n : (n <<< 3).toNat = 8 * n.toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have hfw : MemFrame s.mem (((Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
        (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) + 8) 8 p.toNat).writeLE
        (BitVec.toNat (s.regs 4) - 32) 8 4741413) (MemAmd64.callerWindow s d 32 32) := by
      simp only [MemAmd64.callerWindow]; janus_frame
    have E := fun {S : State} (hf : MemFrame s.mem S.mem (MemAmd64.callerWindow s d 32 32))
        (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 32) (hg : S.regs 14 = s.regs 14) (hx : S.xmm 15 = 0)
        (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47) =>
      MemAmd64.EqPre.of_caller (nargs := 2) hc hf hsp hg hx hdf hra (by decide) (by decide)
    have hfw0 := hfw
    simp only [MemAmd64.callerWindow, outside_cons, outside_nil, and_true] at hfw
    refine Reaches.call (Summary.withExit hclr hret) rfl
      ⟨⟨?_, (E hfw0 (by simp [setRegF, hsp32]) (by simp [setRegF]) (by simpa using hs.zero) (by simpa using hs.df)
          (by simp [setRegF, hsp32, Janus.Arm64.Memory.readLE_writeLE_self])).1,
        (E hfw0 (by simp [setRegF, hsp32]) (by simp [setRegF]) (by simpa using hs.zero) (by simpa using hs.df)
          (by simp [setRegF, hsp32, Janus.Arm64.Memory.readLE_writeLE_self])).2.1, ?_, ?_, ?_,
        (E hfw0 (by simp [setRegF, hsp32]) (by simp [setRegF]) (by simpa using hs.zero) (by simpa using hs.df)
          (by simp [setRegF, hsp32, Janus.Arm64.Memory.readLE_writeLE_self])).2.2⟩, ?_, ?_, ?_⟩ ?_
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff]
      exact hl.env_frame _ _ _ henv (Agrees.of_window (lo := (s.regs 4).toNat - (d + 32))
        (hi := (s.regs 4).toNat + 32) (by janus_frame) (Outside.of_sub hpriv (by omega) (by omega)))
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32]
      exact Outside.of_sub hpriv (by omega) (by omega)
    · refine ⟨hwb1, by simpa using hwb2, ?_⟩
      simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp32,
        outside_cons, outside_nil, and_true]; omega
    · unfold WriteBarrierOff at hwb ⊢
      simp only; rw [hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hwb
    · simpa [setRegF, h_a0] using hal8
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, h8n]; omega
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, h8n, h_a0]
      refine ⟨hP', by simpa using hP, ?_, hpp, ?_⟩
      · simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp32,
          outside_cons, outside_nil, and_true]; omega
      · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32, outside_cons, outside_nil, and_true]; omega
    · intro s' hpc' ⟨r, x, y, fl, mx, m', hs', hmx, hfr, henv', hz⟩
      subst hs'
      simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp32,
        h8n, h_a0] at hfr hz
      janus64_run
      refine ⟨hz, hfw.trans hfr fun a k h => ?_⟩
      simp only [window, MemAmd64.callerWindow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨hp, hw⟩, hds⟩ := h
      exact ⟨hw, ⟨hp, by omega, by omega⟩, hds⟩

end Proof
