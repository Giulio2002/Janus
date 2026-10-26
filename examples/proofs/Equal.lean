import Extracted

/-!
# `Equal(a, b any) bool` compares two interface values (arm64)

**Guarantee.** For all interface values `a = (ta, pa)` and `b = (tb, pb)`, every model `R` of the
interface runtime satisfying its laws, every implementation of `runtime.efaceeq` satisfying the
`Efaceeq` contract and every Go call state with `R.depth` bytes of stack below `Equal`'s 48-byte
frame (`CallerOK`) in which, when the type words are equal, the values can be compared
(`EqOK`) and their comparison does not depend on the stack window `Equal` writes (`EqFrame`),
the call returns, obeys the ABI, and the low byte of the result is Go's `a == b`:

* `ta ≠ tb` (different dynamic types): `false`, without a runtime call;
* `ta = tb = 0` (both nil): `true`;
* otherwise `efaceeq`: for a direct-interface type the data words compare, else `R.eq ta`, the
  type's equality on the values at `pa` and `pb` at the call; for a `TFlagRegularMemory` type
  that is not direct (e.g. `uint64`, structs of integers), whose values are readable and outside
  the window, that is equality of their `Size_` bytes.

**Assumptions (all in the statement).** `R` is *any* model satisfying `R.Laws`; the code at
`runtime.efaceeq` is *any* code that behaves as `Efaceeq` says (docs/RUNTIME-CONTRACTS.md,
"Interfaces").
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Iface

namespace Proof

/-- The stack window `Equal` and the runtime write: `R.depth` bytes below the 48-byte frame, the
frame, and the four argument spill slots above `SP`. -/
def window (R : IfaceModel) (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 40)]

theorem correctness (impl : List Segment) (R : IfaceModel) (hl : R.Laws)
    (heq : Efaceeq (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.efaceeq") R)
    (ta pa tb pb : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [ta, pa, tb, pb]
      (fun s => CallerOK R s 48 40 ∧ (ta = tb →
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
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  by_cases htt : ta = tb
  · subst htt
    obtain ⟨hok1, hok2⟩ := hok rfl
    janus_run until [Extracted.program.contractAddr "runtime.efaceeq"]
    refine Reaches.call (Summary.withExit heq hret) rfl
      ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg])
        (by simp [setReg]) (by decide) (by decide), ?_⟩ ?_
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, h_x0, h_x1]
      exact EqFrame.eqOK hok2 hok1 (by simp only [window]; janus_frame)
    · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hres⟩
      subst hs'
      simp only [rtWrites, calleeStack, List.append_nil] at hfr
      simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, h_x0, h_x1] at hres
      rw [EqFrame.efaceEqual hok2 (by simp only [window]; janus_frame)] at hres
      janus_run
      refine ⟨by simpa [setReg] using hres, fun ht0 hreg hnd hx hy => ?_⟩
      rw [← efaceEqual_regular hl henv ht0 (hok1 ht0).1 hreg hnd hx hy]
      simpa [setReg] using hres
  · janus_run
    exact ⟨by simp [show (ta == tb) = false from beq_false_of_ne htt], fun h => absurd h htt⟩


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model of the runtime (`IfaceModel.R0`), code at `runtime.efaceeq`'s address that meets the
`Efaceeq` contract for it (`IfaceSat.efaceeqCode`), an admissible return address and a call
state comparing two boxes of the model's type `TD` (both the value slot `VAL`) that satisfies
the precondition: `correctness` applies, and `Equal` returns `true` from that state. -/

namespace Witness

open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat

/-- `runtime.efaceeq`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.efaceeq"

/-- `IfaceSat.efaceeqCode` at `runtime.efaceeq`'s address. -/
def implAt : List Segment := [{ name := "model", base := cAddr, words := efaceeqCode }]

/-- The program linked with it, as a closed program. -/
def linked : Program :=
  { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : Efaceeq (Extracted.program.link implAt) cAddr R0 := by
  rw [linked_eq]
  intro s hpc hpre
  obtain ⟨⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hok⟩ := hpre
  by_cases h0 : (s.regs 0).toNat = 0
  · janus_run
    refine rtReturn_of R0 3 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
    simp [setReg, efaceEqual, h0]
  · obtain ⟨-, htd, hx, hy⟩ := hok h0
    janus_run
    all_goals
      refine rtReturn_of R0 3 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
        rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
      rw [htd, efaceEqual_R0 (g := s.regs 28) ⟨he1, he2, hd⟩]
      simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      split
      · rename_i heq; simp [heq]
      · rename_i hne; simp [beq_false_of_ne hne]

/-- The witness return address. -/
def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- `TD` and the value slot `VAL`, as words. -/
def td : BitVec 64 := BitVec.ofNat 64 TD
def val : BitVec 64 := BitVec.ofNat 64 VAL

/-- The witness call state: `Equal(a, a)` for the box `a = (TD, VAL)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 2 then td else if i = 1 ∨ i = 3 then val
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry
    [td, val, td, val] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem pre : CallerOK R0 s0 48 40 ∧ (td = td →
    EqOK R0 s0.mem td.toNat val.toNat val.toNat ∧
      EqFrame R0 td.toNat s0.mem val.toNat val.toNat (window R0 s0)) := by
  refine ⟨⟨wmem_env (s0.regs 28), ⟨by decide, by decide, by decide⟩, by decide, by decide,
    by decide, by decide, by decide, ?_, ?_, ?_⟩, fun _ => ⟨fun _ => ⟨Or.inl rfl, rfl, by decide,
    by decide⟩, ?_⟩⟩
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
  · refine EqFrame.of_regular R0_laws (g := s0.regs 28) (wmem_env (s0.regs 28)) (Or.inl rfl) (by decide) (by decide)
      (by decide) (by decide) ?_ ?_ ?_
    · simp only [window, outside_cons, outside_nil, and_true]; decide
    · simp only [window, outside_cons, outside_nil, and_true]; decide
    · intro a n ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      simp at hr; subst hr
      simp only [window, outside_cons, outside_nil, and_true]
      simp [s0, wsp] at h1 h2 ⊢; omega

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : IfaceModel) (ret : Nat) (s : State) (ta pa tb pb : BitVec 64),
    R.Laws ∧ Efaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.efaceeq") R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [ta, pa, tb, pb] s ∧
    (CallerOK R s 48 40 ∧ (ta = tb →
      EqOK R s.mem ta.toNat pa.toNat pb.toNat ∧ EqFrame R ta.toNat s.mem pa.toNat pb.toNat (window R s))) :=
  ⟨implAt, R0, ret, s0, td, val, td, val, R0_laws, model, hret, setup, pre⟩

/-- So the guarantee is reached: comparing the box with itself gives `true`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness implAt R0 R0_laws model td val td val ret hret s0 setup pre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2.1, show td.toNat = TD from rfl, show s0.mem = wmem from rfl,
    efaceEqual_R0 (g := s0.regs 28) (wmem_env _)]
  decide

end Witness

end Proof
