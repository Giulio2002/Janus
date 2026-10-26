import Janus
import Extracted

/-!
# `Equal(a, b any) bool` compares two interface values (amd64)

**Guarantee.** As the arm64 theorem (`examples/proofs/Equal.lean`), for the amd64 code: for all
interface values `a = (ta, pa)` (`RAX`, `RBX`) and `b = (tb, pb)` (`RCX`, `RDI`), every model `R`
satisfying its laws, every implementation of `runtime.efaceeq` satisfying `Efaceeq`
(`Janus/Contracts/IfaceAmd64.lean`) and every Go call state with `R.depth` bytes of stack below
`Equal`'s frame in which, when the type words are equal, the values can be compared and their
comparison does not depend on the stack window `Equal` writes, the call returns, obeys the ABI,
and `AL` is Go's `a == b`: `false` for different type words, `true` for two nils, otherwise
`efaceeq`'s answer, which for a `TFlagRegularMemory` type that is not direct is equality of the
`Size_` bytes of the values.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Type Janus.Contracts.Iface Janus.Contracts.IfaceAmd64

namespace Proof

/-- The stack window `Equal` and the runtime write: `R.depth` bytes below the frame (with the
pushed return address), the frame, the return-address slot and the four spill slots. -/
def window (R : IfaceModel) (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 40)]

theorem correctness (impl : List Janus.Amd64.Segment) (R : IfaceModel) (hl : R.Laws)
    (heq : Efaceeq (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.efaceeq") R)
    (ta pa tb pb : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [ta, pa, tb, pb]
      (fun s => CallerOK R s 40 40 ∧ (ta = tb →
        EqOK R s.mem ta.toNat pa.toNat pb.toNat ∧ EqFrame R ta.toNat s.mem pa.toNat pb.toNat (window R s)))
      (fun s s' => (s'.regs 0).toNat % 256 =
          (ta == tb && efaceEqual R s.mem ta.toNat pa.toNat pb.toNat).toNat ∧
        (ta = tb → ta ≠ 0 → isRegularMemory s.mem ta.toNat = true →
          isDirectIface s.mem ta.toNat = false →
          s.mem.accessible pa.toNat (tySize s.mem ta.toNat) false = true →
          s.mem.accessible pb.toNat (tySize s.mem ta.toNat) false = true →
          (s'.regs 0).toNat % 256 = (s.mem.readLE pa.toNat (tySize s.mem ta.toNat) ==
            s.mem.readLE pb.toNat (tySize s.mem ta.toNat)).toNat)) := by
  intro ret hret s hs ⟨hc, hok⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  by_cases htt : ta = tb
  · subst htt
    obtain ⟨hok1, hok2⟩ := hok rfl
    janus64_run until [Extracted.program.contractAddr "runtime.efaceeq"]
    refine Reaches.call (Summary.withExit heq hret) rfl
      ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp40]) (by simp [setRegF])
        (by simpa using hs.zero) (by simpa using hs.df)
        (by simp [setRegF, hsp40, Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide), ?_⟩ ?_
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, h_a0, h_a1, h_a3]
      exact EqFrame.eqOK hok2 hok1 (by simp only [window]; janus_frame)
    · intro s' hpc' ⟨r, x, y, fl, m', _, _, hs', hfr, henv', hres⟩
      subst hs'
      simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, List.append_nil,
        setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, h_a0, h_a1, h_a3] at hres
      rw [EqFrame.efaceEqual hok2 (by simp only [window]; janus_frame)] at hres
      janus64_run
      refine ⟨hres, fun ht0 hreg hnd hx hy => ?_⟩
      rw [← efaceEqual_regular hl henv ht0 (hok1 ht0).1 hreg hnd hx hy]
      exact hres
  · have htt' : ta.toNat ≠ tb.toNat := fun h => htt (BitVec.eq_of_toNat_eq h)
    janus64_run
    exact ⟨by simp [show (ta == tb) = false from beq_false_of_ne htt], fun h => absurd h htt⟩


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model of the runtime (`IfaceModel.R0`), code at `runtime.efaceeq`'s address that meets the
`Efaceeq` contract for it (`IfaceSatAmd64.efaceeqCode`), an admissible return address and a call
state comparing a box of the model's type `TD` with itself: `correctness` applies, and `Equal`
returns `true`. -/

namespace Witness

open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64
open Janus.Contracts (IfaceSat.itabAt_TAB IfaceSat.itabResult_R0 IfaceSat.efaceEqual_R0)

/-- `runtime.efaceeq`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.efaceeq"

/-- `IfaceSatAmd64.efaceeqCode` at `runtime.efaceeq`'s address. -/
def implAt : List Janus.Amd64.Segment := [{ name := "model", base := cAddr, bytes := efaceeqCode }]

/-- The program linked with it, as a closed program. -/
def linked : Janus.Amd64.Program :=
  { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : Efaceeq (Extracted.program.link implAt) cAddr R0 := by
  rw [linked_eq]
  intro s hpc ⟨hpre, hok⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  by_cases h0 : (s.regs 0).toNat = 0
  · janus64_run
    all_goals
      refine rtReturn_of R0 3 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
        (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
      simp [setRegF, efaceEqual, h0]
  · obtain ⟨-, htd, hx, hy⟩ := hok h0
    janus64_run
    all_goals
      refine rtReturn_of R0 3 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
        (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
      rw [htd, IfaceSat.efaceEqual_R0 (g := s.regs 14) ⟨he1, he2, hd⟩]
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, setcc_low_byte]
      have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 1).toNat 8
      have hb := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
      simp only [Nat.reducePow] at ha hb
      split
      · rename_i h
        have : Janus.Arm64.Memory.readLE s.mem (s.regs 3).toNat 8 =
            Janus.Arm64.Memory.readLE s.mem (s.regs 1).toNat 8 := by omega
        simp [this]
      · rename_i h
        have : Janus.Arm64.Memory.readLE s.mem (s.regs 3).toNat 8 ≠
            Janus.Arm64.Memory.readLE s.mem (s.regs 1).toNat 8 := by omega
        simp [beq_false_of_ne this]

/-- The witness return address. -/
def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- The witness memory: `wmem` with the return address `ret` at `[RSP]`. -/
def mem0 : Janus.Arm64.Memory :=
  ⟨fun a => BitVec.ofNat 8 ((((wsp + 2, 0x20) :: wtable).lookup a).getD 0), wmem.regions⟩

theorem mem0_env (g : W64) : Env0 mem0 g := by
  refine ⟨by decide, by decide, ?_⟩
  unfold Desc; decide

/-- `TD` and the value slot `VAL`, as words. -/
def td : BitVec 64 := BitVec.ofNat 64 TD
def val : BitVec 64 := BitVec.ofNat 64 VAL

/-- The witness call state: `Equal(a, a)` for the box `a = (TD, VAL)`. -/
def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 ∨ i = 1 then td else if i = 3 ∨ i = 7 then val
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry
    [td, val, td, val] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem pre : CallerOK R0 s0 40 40 ∧ (td = td →
    EqOK R0 s0.mem td.toNat val.toNat val.toNat ∧
      EqFrame R0 td.toNat s0.mem val.toNat val.toNat (window R0 s0)) := by
  refine ⟨⟨mem0_env (s0.regs 14), ⟨by decide, by decide, by decide⟩, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩, fun _ => ⟨fun _ => ⟨Or.inl rfl, rfl, by decide,
    by decide⟩, ?_⟩⟩
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
  · refine EqFrame.of_regular R0_laws (g := s0.regs 14) (mem0_env (s0.regs 14)) (Or.inl rfl)
      (by decide) (by decide) (by decide) (by decide) ?_ ?_ ?_
    · simp only [window, outside_cons, outside_nil, and_true]; decide
    · simp only [window, outside_cons, outside_nil, and_true]; decide
    · intro a n ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      simp at hr; subst hr
      simp only [window, outside_cons, outside_nil, and_true]
      simp [s0, wsp] at h1 h2 ⊢; omega

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : IfaceModel) (ret : Nat)
    (s : Janus.Amd64.State) (ta pa tb pb : BitVec 64),
    R.Laws ∧ Efaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.efaceeq") R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [ta, pa, tb, pb] s ∧
    (CallerOK R s 40 40 ∧ (ta = tb →
      EqOK R s.mem ta.toNat pa.toNat pb.toNat ∧ EqFrame R ta.toNat s.mem pa.toNat pb.toNat (window R s))) :=
  ⟨implAt, R0, ret, s0, td, val, td, val, R0_laws, model, hret, setup, pre⟩

/-- So the guarantee is reached: comparing the box with itself gives `true`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness implAt R0 R0_laws model td val td val ret hret s0 setup pre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2.1, show td.toNat = TD from rfl, show s0.mem = mem0 from rfl,
    IfaceSat.efaceEqual_R0 (g := s0.regs 14) (mem0_env _)]
  decide

end Witness

end Proof
