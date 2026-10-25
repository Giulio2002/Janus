import Extracted

/-!
# `ClearTrees(s []*Tree)`: `clear(s)` through `runtime.memclrHasPointers` (arm64)

**Guarantee.** With the write barrier off and a `memclrHasPointers` satisfying
`Mem.MemclrHasPointers`, for every slice `(p, n, c)` with `p` 8-aligned, `n < 2^45`, the `8n`
bytes at `p` writable and outside the stack window and the runtime's memory: the call returns
and the `8n` bytes are zero; an empty slice makes no call.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem

namespace Proof

/-- The stack window of `ClearTrees` and the runtime call. -/
def window (d : Nat) (s : State) : List (Nat × Nat) := callerWindow s d 32 32

/-- The precondition: see the module documentation. -/
def pre (M : MemModel) (wb d : Nat) (p n : BitVec 64) (s : State) : Prop :=
  CallerOK s d 32 32 ∧ M.Env s.mem (s.regs 28) ∧ Outside ((s.regs 28).toNat + 16) 8 M.priv ∧ Outside (s.sp.toNat - (d + 32)) (d + 64) M.priv ∧
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
  intro ret hret s hs ⟨hc, henv, hgp, hpriv, hwb1, hwb2, hwbo, hwb, hn, hal8, ⟨hP, hP'⟩, hpo, hpp⟩
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
      ⟨⟨?_, hsg, hcall, ?_, ?_, ?_, hgo, by simpa [setReg] using hgp⟩, ?_, ?_, ?_⟩ ?_
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

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The model `M0`, code that meets `MemclrHasPointers` (`MemSat.memclrHasPointers_impl`, a byte
loop) behind a branch at the contract's address, and a call clearing the 8 words at `DST` with the
write barrier off. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MemSat

def cAddr : Nat := Extracted.program.contractAddr "runtime.memclrHasPointers"
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := memclrCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model (wb d : Nat) : MemclrHasPointers (Extracted.program.link implAt) cAddr M0 wb d := by
  have hA : MemclrHasPointers (Extracted.program.link implAt) A0 M0 wb d := by
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (memclrHasPointers_impl wb d)
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

def p : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 8#64

def s0 : State :=
  { regs := fun i => if i = 0 then p else if i = 1 ∨ i = 2 then n
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [p, n, n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

theorem hpre : pre M0 WB 64 p n s0 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    by simp only [outside_cons, outside_nil, and_true]; decide⟩, trivial, trivial, trivial,
    by decide, by decide, ?_, by unfold WriteBarrierOff; decide, by decide, by decide,
    ⟨by decide, by decide⟩, ?_, trivial⟩ <;>
    simp only [window, callerWindow, outside_cons, outside_nil, and_true] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MemModel) (wb d ret : Nat) (s : State) (p n c : BitVec 64),
    M.Laws ∧ MemclrHasPointers (Extracted.program.link impl)
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
