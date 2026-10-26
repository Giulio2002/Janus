import Janus
import Extracted

/-!
# `ClearTrees(s []*Tree)` on amd64: `clear(s)` through `runtime.memclrHasPointers`

As on arm64, under `MemAmd64.MemclrHasPointers` with the write barrier off.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts Janus.Contracts.Mem
open Janus (MemFrame Outside outside_cons outside_nil outside_append)

namespace Proof

/-- The stack window of `ClearTrees` and the runtime call (amd64). -/
def window (d : Nat) (s : State) : List (Nat × Nat) := MemAmd64.callerWindow s d 32 32

/-- The precondition: see the module documentation. -/
def pre (M : MemModel) (wb d : Nat) (p n : BitVec 64) (s : State) : Prop :=
  MemAmd64.CallerOK s d 32 32 ∧ M.Env s.mem (s.regs 14) ∧ Outside ((s.regs 14).toNat + 16) 8 M.priv ∧
    Outside ((s.regs 4).toNat - (d + 32)) (d + 64) M.priv ∧
    wb + 4 ≤ 2 ^ 48 ∧ s.mem.accessible wb 4 false = true ∧ Outside wb 4 (window d s) ∧
    WriteBarrierOff s.mem wb ∧ n.toNat < 2 ^ 45 ∧ p.toNat % 8 = 0 ∧
    Buffer s p (8 * n.toNat) true ∧ Outside p.toNat (8 * n.toNat) (window d s) ∧
    Outside p.toNat (8 * n.toNat) M.priv

/-- The return address the call at `Extracted.entry + 0x25` pushes. -/
def ret25 : Nat := Extracted.entry + 0x25

theorem correctness (impl : List Segment) (M : MemModel) (hl : M.Laws) (wb d : Nat)
    (hclr : MemAmd64.MemclrHasPointers (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrHasPointers") M wb d)
    (p n c : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p, n, c] (pre M wb d p n)
      (fun s s' => Zeroed s'.mem p.toNat (8 * n.toNat) ∧
        MemFrame s.mem s'.mem (M.priv ++ window d s ++ [(p.toNat, p.toNat + 8 * n.toNat)])) := by
  intro ret hret s hs ⟨hc, henv, hgp, hpriv, hwb1, hwb2, hwbo, hwb, hn, hal8, ⟨hP', hP⟩, hpo, hpp⟩
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
        (BitVec.toNat (s.regs 4) - 32) 8 ret25) (MemAmd64.callerWindow s d 32 32) := by
      simp only [MemAmd64.callerWindow]; janus_frame
    janus_eval_nat hR25 : ret25
    simp only [hR25] at hfw
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
          (by simp [setRegF, hsp32, Janus.Arm64.Memory.readLE_writeLE_self])).2.2, by simpa [setRegF] using hgp⟩, ?_, ?_, ?_⟩ ?_
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
    · intro s' hpc' ⟨r, x, y, fl, mx, m', _, _, hs', hmx, hfr, henv', hz⟩
      subst hs'
      simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp32,
        h8n, h_a0] at hfr hz
      janus64_run
      refine ⟨hz, hfw.trans hfr fun a k h => ?_⟩
      simp only [window, MemAmd64.callerWindow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨hp, hw⟩, hds⟩ := h
      exact ⟨hw, ⟨hp, by omega, by omega⟩, hds⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: the model `M0`, `MemSatAmd64.memclrCode` (`REP STOSB`) at `A0` behind a `JMP`, and a
call clearing the 8 words at `DST` with the write barrier off. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MemSatAmd64

def cAddr : Nat := Extracted.program.contractAddr "runtime.memclrHasPointers"
def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := memclrCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model (wb d : Nat) : MemAmd64.MemclrHasPointers (Extracted.program.link implAt) cAddr M0 wb d := by
  have hA : MemAmd64.MemclrHasPointers (Extracted.program.link implAt) A0 M0 wb d := by
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (memclrHasPointers_impl wb d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def p : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 8#64

def s0 : State :=
  { regs := fun i => if i = 0 then p else if i = 3 ∨ i = 1 then n
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [p, n, n] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : pre M0 WB 64 p n s0 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide,
    by simp only [outside_cons, outside_nil, and_true]; decide⟩, trivial, trivial, trivial,
    by decide, by decide, ?_, by unfold WriteBarrierOff; decide, by decide, by decide,
    ⟨by decide, by decide⟩, ?_, trivial⟩ <;>
    simp only [window, MemAmd64.callerWindow, outside_cons, outside_nil, and_true] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MemModel) (wb d ret : Nat) (s : State)
    (p n c : BitVec 64), M.Laws ∧
    MemAmd64.MemclrHasPointers (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrHasPointers") M wb d ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [p, n, c] s ∧
    pre M wb d p n s :=
  ⟨implAt, M0, WB, 64, ret, s0, p, n, n, M0_laws, model WB 64, hret, setup, hpre⟩

/-- So the guarantee is reached: the 64 bytes at `DST` are zero. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ Zeroed s'.mem DST 64 :=
  (correctness implAt M0 M0_laws WB 64 (model WB 64) p n n ret hret s0 setup hpre).mono
    fun _ h => ⟨h.1, h.2.1⟩

end Witness

end Proof
