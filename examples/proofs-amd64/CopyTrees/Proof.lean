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

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: the model `M0`, `MemSatAmd64.typedmemmoveCode` (`REP MOVSB`, backwards when
`dst > src`) at `A0` behind a `JMP`, and a copy of 128 zero bytes from `DST` to `DST + 128` with the
write barrier off and the type descriptor in memory. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MemSatAmd64

def cAddr : Nat := Extracted.program.contractAddr "runtime.typedmemmove"
def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := typedmemmoveCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model (wb d : Nat) : MemAmd64.TypedMemmove (Extracted.program.link implAt) cAddr M0 wb d := by
  have hA : MemAmd64.TypedMemmove (Extracted.program.link implAt) A0 M0 wb d := by
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (typedmemmove_impl wb d)
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

def dst : BitVec 64 := BitVec.ofNat 64 (DST + 128)
def src : BitVec 64 := BitVec.ofNat 64 DST

def mem0 : Janus.Arm64.Memory := withData Extracted.program.data wmem64

def s0 : State :=
  { regs := fun i => if i = 0 then dst else if i = 3 then src
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [dst, src] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 20000 in
theorem hpre : pre M0 WB 64 dst src s0 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide,
    by simp only [outside_cons, outside_nil, and_true]; decide⟩, trivial, trivial, trivial,
    by unfold Janus.Amd64.Program.DataLoaded; decide, ?_, by decide, by decide, ?_,
    by unfold WriteBarrierOff; decide, ⟨by decide, by decide⟩, ?_, ⟨by decide, by decide⟩, ?_, trivial⟩ <;>
    simp only [window, MemAmd64.callerWindow, treesType, outside_cons, outside_nil, and_true] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MemModel) (wb d ret : Nat) (s : State)
    (dst src : BitVec 64), M.Laws ∧
    MemAmd64.TypedMemmove (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typedmemmove") M wb d ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, src] s ∧
    pre M wb d dst src s :=
  ⟨implAt, M0, WB, 64, ret, s0, dst, src, M0_laws, model WB 64, hret, setup, hpre⟩

/-- So the guarantee is reached: `DST + 128` receives the 128 bytes of `DST`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ Copied s0.mem s'.mem (DST + 128) DST 128 :=
  (correctness implAt M0 M0_laws WB 64 (model WB 64) dst src ret hret s0 setup hpre).mono
    fun _ h => ⟨h.1, h.2.1⟩

end Witness

end Proof
