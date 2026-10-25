import Extracted

/-!
# `CopyTrees(dst, src *[2]Tree)`: `*dst = *src` through `runtime.typedmemmove` (arm64)

**Guarantee.** For every model `M` of the runtime around the typed-memory functions, every
implementation of `runtime.typedmemmove` satisfying `Mem.TypedMemmove` with the write-barrier
flag at `wb` and stack bound `d`, and every Go call state with the write barrier **off**
(`WriteBarrierOff`), the program's read-only data in memory (the type descriptor of `[2]Tree`,
128 bytes with pointers), `src` readable, `dst` writable, both outside the stack window and `dst`
outside the runtime's memory: the call returns, `dst` holds the 128 bytes of `src` (also when
they overlap), and nothing else changed except the runtime's memory and the stack window.

**Why `typedmemmove`.** The arrays may overlap partially (through slice-to-array-pointer
conversions), so the compiler copies them with `typedmemmove` instead of inline stores.
-/

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
  have hsz : s.mem.readLE treesType 8 = 128 := by rw [hT, h_rodata _ _ (by decide)]; decide
  rw [hT] at hsz
  have E := fun {S : State} (hf : MemFrame s.mem S.mem (callerWindow s d 48 24))
      (hsp : S.sp.toNat = s.sp.toNat - 48) (hg : S.regs 28 = s.regs 28)
      (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) =>
    EqPre.of_caller (nargs := 3) hc hf hsp hg hlr hlr' (by decide) (by decide)
  have hfw0 := hfw
  simp only [callerWindow, outside_cons, outside_nil, and_true] at hfw
  refine Reaches.call (Summary.withExit hmv hret) rfl
    ⟨⟨?_, (E hfw0 (by simp [hsp]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg])).1,
      (E hfw0 (by simp [hsp]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg])).2.1, ?_, ?_, ?_,
      (E hfw0 (by simp [hsp]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg])).2.2,
      by simpa [setReg] using hgp⟩, ?_, ?_, ?_, ?_⟩ ?_
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

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The model `M0`, code that meets `TypedMemmove` for every flag address and stack bound
(`MemSat.typedmemmove_impl`: reads `Size_`, copies backwards when `dst > src`) behind a branch at
the contract's address, and a call copying 128 zero bytes from `DST` to `DST + 128` with the
write barrier off (`WB`) and the type descriptor in memory (`withData`). -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MemSat

def cAddr : Nat := Extracted.program.contractAddr "runtime.typedmemmove"
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := typedmemmoveCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model (wb d : Nat) : TypedMemmove (Extracted.program.link implAt) cAddr M0 wb d := by
  have hA : TypedMemmove (Extracted.program.link implAt) A0 M0 wb d := by
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (typedmemmove_impl wb d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def dst : BitVec 64 := BitVec.ofNat 64 (DST + 128)
def src : BitVec 64 := BitVec.ofNat 64 DST

/-- The witness memory: `wmem` with the program's read-only data (the type descriptor). -/
def mem0 : Memory := withData Extracted.program.data Janus.Contracts.EqHashModel.wmem

def s0 : State :=
  { regs := fun i => if i = 0 then dst else if i = 1 then src
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [dst, src] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 20000 in
theorem hpre : pre M0 WB 64 dst src s0 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    by simp only [outside_cons, outside_nil, and_true]; decide⟩, trivial, trivial, trivial, by unfold Program.DataLoaded; decide, ?_,
    by decide, by decide, ?_, by unfold WriteBarrierOff; decide, ⟨by decide, by decide⟩, ?_,
    ⟨by decide, by decide⟩, ?_, trivial⟩ <;>
    simp only [window, callerWindow, treesType, outside_cons, outside_nil, and_true] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MemModel) (wb d ret : Nat) (s : State) (dst src : BitVec 64),
    M.Laws ∧ TypedMemmove (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typedmemmove") M wb d ∧
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
