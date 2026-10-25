import Extracted

/-!
# `Box(x uint64) any` boxes `x` into an interface (arm64)

**Guarantee.** For every `x`, every model `R` of the interface runtime satisfying its laws, every
implementation of `runtime.convT64` satisfying the `ConvT64` contract
(`Janus/Contracts/Iface.lean`) and every Go call state in which the runtime is usable and has
`R.depth` bytes of stack below `Box`'s 32-byte frame (`CallerOK`), the call returns, obeys the
ABI, and the result is the interface value `(uint64Type, ptr)`: the type word is the address of
the `uint64` type descriptor the code loads (`ADRP`+`ADD`, recomputed from the extracted words),
and the data word `ptr` points to a readable 8-byte box in the runtime's memory holding `x`.
Memory changes only in the runtime's memory and the stack window, and the runtime stays usable.

**Assumptions (all in the statement).** `R` is *any* model satisfying `R.Laws`, and the code at
`runtime.convT64` is *any* code that behaves as `ConvT64` says (docs/RUNTIME-CONTRACTS.md,
"Interfaces").

**Readiness** (round 10). The statement also quantifies over `H : RtReady`, the runtime's readiness
for the one call that may allocate (`runtime.convT64`), and assumes it at entry: the theorem says nothing
about a call the runtime cannot serve as the contract says (no room in the heap, a collection).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Iface

namespace Proof

/-- The type word of the result: the address `ADRP`+`ADD` at `Box+0x20` compute (`type:uint64`). -/
def uint64Type : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.Box" 8)
    (segWord Extracted.program "example.com/basic.Box" 9) 0

theorem correctness (impl : List Segment) (R : IfaceModel) (hl : R.Laws) (H : RtReady)
    (hconv : ConvT64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") R H)
    (x : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [x]
      (fun s => CallerOK R s 32 0 ∧ H [x.toNat] (s.regs 28).toNat (s.sp.toNat - 32) (rtView R.priv s.mem))
      (fun s s' => (s'.regs 0).toNat = uint64Type ∧ BoxHolds R s'.mem (s'.regs 1).toNat 8 x.toNat ∧
        MemFrame s.mem s'.mem (R.priv ++ [(s.sp.toNat - (R.depth + 32), s.sp.toNat)]) ∧
        R.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : uint64Type
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.convT64"]
  refine Reaches.call (Summary.withExit hconv hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg])
      (by simp [setReg]) (by decide) (by decide), ?_⟩ ?_
  · simp only [Ready, setReg_apply, reduceIte, Nat.reduceEqDiff]
    simp (disch := janus_disch) only [rtView_writeLE]
    have e1 : (s.sp - 32#64).toNat = s.sp.toNat - 32 := by bv_omega
    simpa [e1, h_x0] using hH
  intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hbox⟩
  subst hs'
  simp only [rtWrites, calleeStack, List.append_nil] at hfr
  janus_run
  refine ⟨hT.symm, ?_, ?_, ?_⟩
  · simpa [setReg, h_x0] using hbox
  · janus_frame
  · simpa [setReg] using henv'


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model of the runtime (`IfaceModel.R0`, whose laws hold), code at `runtime.convT64`'s address
that meets the `ConvT64` contract for it (`IfaceSat.convT64Code`), an admissible return address
and a call state that satisfies the precondition: so `correctness` applies (`nonvacuous`), and
`Box` returns from that state with the guarantee (`returns`). -/

namespace Witness

open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat

/-- `runtime.convT64`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.convT64"

/-- `IfaceSat.convT64Code` at `runtime.convT64`'s address. -/
def implAt : List Segment := [{ name := "model", base := cAddr, words := convT64Code }]

/-- The program linked with it, as a closed program. -/
def linked : Program :=
  { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : ConvT64 (Extracted.program.link implAt) cAddr R0 Htrue := by
  rw [linked_eq]
  intro s hpc ⟨hpre, _⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  refine rtReturn_of R0 1 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl ?_ ((show Env0 s.mem (s.regs 28) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
  · simp only [rtWrites, calleeStack, R0_priv, R0_depth, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    refine ⟨by decide, ?_, inPriv (by decide) (by decide), ?_⟩
    · rw [Memory.accessible_writeLE]
      exact acc_read_of_write (Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
    · show (s.mem.writeLE 66304 8 _).readLE 66304 8 = _
      rw [Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (s.regs 0).isLt

/-- The witness return address. -/
def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- The witness call state: `Box(42)` with the model's memory and a stack at `0x48000`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then 42#64 else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [42#64] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

theorem pre : CallerOK R0 s0 32 0 := by
  refine ⟨wmem_env (s0.regs 28), ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide,
    by decide, ?_, ?_, ?_⟩
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : IfaceModel) (H : RtReady) (ret : Nat) (s : State),
    R.Laws ∧
    ConvT64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.convT64") R H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [42#64] s ∧
    CallerOK R s 32 0 ∧ H [42] (s.regs 28).toNat (s.sp.toNat - 32) (rtView R.priv s.mem) :=
  ⟨implAt, R0, Htrue, ret, s0, R0_laws, model, hret, setup, pre, trivial⟩

/-- So the guarantee is reached: `Box(42)` returns a box holding `42`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = uint64Type ∧ BoxHolds R0 s'.mem (s'.regs 1).toNat 8 42 ∧
      MemFrame s0.mem s'.mem (R0.priv ++ [(s0.sp.toNat - (R0.depth + 32), s0.sp.toNat)]) ∧
      R0.Env s'.mem (s0.regs 28) :=
  correctness implAt R0 R0_laws Htrue model 42#64 ret hret s0 setup ⟨pre, trivial⟩

end Witness

end Proof
