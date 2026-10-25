import Janus
import Extracted

/-!
# `CopyTrees(dst, src *[2]Tree)` on amd64: `*dst = *src` through `runtime.typedmemmove`

As on arm64, under `MemAmd64.TypedMemmove` with the write barrier off.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts Janus.Contracts.Mem
open Janus (MemFrame Outside outside_cons outside_nil outside_append)

namespace Proof

/-- The type descriptor `CopyTrees` passes (`[2]Tree`, from the RIP-relative `LEAQ`). -/
def treesType : Nat := ripTarget Extracted.program (Extracted.entry + 0x18)

/-- The stack window of `CopyTrees` and the runtime call (amd64). -/
def window (d : Nat) (s : State) : List (Nat × Nat) := MemAmd64.callerWindow s d 40 8

/-- The precondition: see the module documentation. -/
def pre (M : MemModel) (wb d : Nat) (dst src : BitVec 64) (s : State) : Prop :=
  MemAmd64.CallerOK s d 40 8 ∧ M.Env s.mem (s.regs 14) ∧ Outside ((s.regs 14).toNat + 16) 8 M.priv ∧
    Outside ((s.regs 4).toNat - (d + 40)) (d + 48) M.priv ∧
    Extracted.program.DataLoaded s.mem ∧ Outside treesType 16 (window d s) ∧
    wb + 4 ≤ 2 ^ 48 ∧ s.mem.accessible wb 4 false = true ∧ Outside wb 4 (window d s) ∧
    WriteBarrierOff s.mem wb ∧
    Buffer s src 128 false ∧ Outside src.toNat 128 (window d s) ∧
    Buffer s dst 128 true ∧ Outside dst.toNat 128 (window d s) ∧ Outside dst.toNat 128 M.priv

/-- The return address the call at `Extracted.entry + 0x25` pushes. -/
def ret25 : Nat := Extracted.entry + 0x25

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (M : MemModel) (hl : M.Laws) (wb d : Nat)
    (hmv : MemAmd64.TypedMemmove (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typedmemmove") M wb d)
    (dst src : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [dst, src] (pre M wb d dst src)
      (fun s s' => Copied s.mem s'.mem dst.toNat src.toNat 128 ∧
        MemFrame s.mem s'.mem (M.priv ++ window d s ++ [(dst.toNat, dst.toNat + 128)])) := by
  intro ret hret s hs ⟨hc, henv, hgp, hpriv, hd, hto, hwb1, hwb2, hwbo, hwb, ⟨hS', hS⟩, hso, ⟨hD', hD⟩, hdo, hdp⟩
  janus64_intro hs
  have hc' := hc
  obtain ⟨hg, hal, hdd, hb, hst, hog⟩ := hc'
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  janus_eval_nat hT : treesType
  rw [hT] at hto
  simp only [window, MemAmd64.callerWindow, outside_cons, outside_nil, and_true] at hog hto hwbo hso hdo
  janus64_data hd [hst]
  janus64_run until [Extracted.program.contractAddr "runtime.typedmemmove"]
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hfw : MemFrame s.mem ((Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 ret25)
      (MemAmd64.callerWindow s d 40 8) := by
    simp only [MemAmd64.callerWindow]; janus_frame
  janus_eval_nat hR25 : ret25
  simp only [hR25] at hfw
  have hsz : Janus.Arm64.Memory.readLE s.mem treesType 8 = 128 := by
    rw [hT, h_rodata _ _ (by decide)]; decide
  rw [hT] at hsz
  have E := fun {S : State} (hf : MemFrame s.mem S.mem (MemAmd64.callerWindow s d 40 8))
      (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 40) (hg : S.regs 14 = s.regs 14) (hx : S.xmm 15 = 0)
      (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47) =>
    MemAmd64.EqPre.of_caller (nargs := 3) hc hf hsp hg hx hdf hra (by decide) (by decide)
  have hfw0 := hfw
  simp only [MemAmd64.callerWindow, outside_cons, outside_nil, and_true] at hfw
  refine Reaches.call (Summary.withExit hmv hret) rfl
    ⟨⟨?_, (E hfw0 (by simp [setRegF, hsp40]) (by simp [setRegF]) (by simpa using hs.zero) (by simpa using hs.df)
        (by simp [setRegF, hsp40, Janus.Arm64.Memory.readLE_writeLE_self])).1,
      (E hfw0 (by simp [setRegF, hsp40]) (by simp [setRegF]) (by simpa using hs.zero) (by simpa using hs.df)
        (by simp [setRegF, hsp40, Janus.Arm64.Memory.readLE_writeLE_self])).2.1, ?_, ?_, ?_,
      (E hfw0 (by simp [setRegF, hsp40]) (by simp [setRegF]) (by simpa using hs.zero) (by simpa using hs.df)
        (by simp [setRegF, hsp40, Janus.Arm64.Memory.readLE_writeLE_self])).2.2, by simpa [setRegF] using hgp⟩, ?_, ?_, ?_, ?_⟩ ?_
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff]
    exact hl.env_frame _ _ _ henv (Agrees.of_window (lo := (s.regs 4).toNat - (d + 40))
      (hi := (s.regs 4).toNat + 8) (by janus_frame) (Outside.of_sub hpriv (by omega) (by omega)))
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]
    exact Outside.of_sub hpriv (by omega) (by omega)
  · refine ⟨hwb1, by simpa using hwb2, ?_⟩
    simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp40,
      outside_cons, outside_nil, and_true]; omega
  · unfold WriteBarrierOff at hwb ⊢
    simp only; rw [hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hwb
  · refine ⟨by simp [setRegF], by simpa [setRegF] using Janus.Arm64.Memory.accessible_mono _ h_data0 (by omega) (by omega)⟩
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, MemAmd64.calleeStack, MapAmd64.calleeStack, hsp40,
      outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]; omega
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, typSize]
    rw [hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hsz]
    refine ⟨hS', by simpa using hS, ?_⟩
    simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp40, outside_cons, outside_nil, and_true]; omega
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, typSize]
    rw [hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hsz]
    refine ⟨hD', by simpa using hD, ?_, hdp, ?_⟩
    · simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp40, outside_cons, outside_nil, and_true]; omega
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40, outside_cons, outside_nil, and_true]; omega
  · intro s' hpc' ⟨r, x, y, fl, mx, m', hs', hmx, hfr, henv', hcp⟩
    subst hs'
    simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, typSize] at hcp hfr
    rw [hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hsz] at hcp hfr
    janus64_run
    refine ⟨fun i hi => ?_, hfw.trans hfr fun a n h => ?_⟩
    · rw [hcp i hi]
      have := hfw.readLE (src.toNat + i) 1 (by simp only [outside_cons, outside_nil, and_true]; omega)
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
    · simp only [window, MemAmd64.callerWindow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨hp, hw⟩, hds⟩ := h
      exact ⟨hw, ⟨hp, by omega, by omega⟩, hds⟩

end Proof
