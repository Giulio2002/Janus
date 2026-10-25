import Janus
import Extracted

/-!
# `Box(x uint64) any` boxes `x` into an interface (amd64)

**Guarantee.** For every `x`, every model `R` of the interface runtime satisfying its laws, every
implementation of `runtime.convT64` satisfying the `ConvT64` contract
(`Janus/Contracts/IfaceAmd64.lean`) and every Go call state in which the runtime is usable and
has `R.depth` bytes of stack below `Box`'s frame (`CallerOK`), the call returns, obeys the ABI,
and the result is the interface value `(uint64Type, ptr)` in `RAX`, `RBX`: the type word is the
address of the `uint64` type descriptor the code loads (`LEAQ`, recomputed from the extracted
bytes), and `ptr` points to a readable 8-byte box in the runtime's memory holding `x`. Memory
changes only in the runtime's memory and the stack window, and the runtime stays usable.

**Assumptions (all in the statement).** `R` is *any* model satisfying `R.Laws`, and the code at
`runtime.convT64` is *any* code that behaves as `ConvT64` says (docs/RUNTIME-CONTRACTS.md,
"Interfaces").
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Type Janus.Contracts.Iface Janus.Contracts.IfaceAmd64

namespace Proof

/-- The type word of the result: the RIP-relative `LEAQ` at `Box+0x16` (`type:uint64`). -/
def uint64Type : Nat := ripTarget Extracted.program (Extracted.entry + 0x16)

theorem correctness (impl : List Janus.Amd64.Segment) (R : IfaceModel) (hl : R.Laws)
    (hconv : ConvT64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") R)
    (x : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [x]
      (fun s => CallerOK R s 24 8)
      (fun s s' => (s'.regs 0).toNat = uint64Type ∧ BoxHolds R s'.mem (s'.regs 3).toNat 8 x.toNat ∧
        MemFrame s.mem s'.mem (R.priv ++ [((s.regs 4).toNat - (R.depth + 24), (s.regs 4).toNat + 8)]) ∧
        R.Env s'.mem (s.regs 14)) := by
  intro ret hret s hs hc
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : uint64Type
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp24 : (s.regs 4 - 24#64).toNat = (s.regs 4).toNat - 24 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.convT64"]
  refine Reaches.call (Summary.withExit hconv hret) rfl
    (RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp24]) (by simp [setRegF])
      (by simpa using hs.zero) (by simpa using hs.df)
      (by simp [setRegF, hsp24, Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide)) ?_
  intro s' hpc' ⟨r, x', y, fl, m', hs', hfr, henv', hbox⟩
  subst hs'
  simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, List.append_nil, setRegF,
    reduceIte, Nat.reduceEqDiff, hsp24] at hfr
  janus64_run
  refine ⟨hT.symm, ?_, ?_, ?_⟩
  · simpa [setRegF, h_a0] using hbox
  · janus_frame
  · simpa [setRegF] using henv'


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model of the runtime (`IfaceModel.R0`), code at `runtime.convT64`'s address that meets the
`ConvT64` contract for it (`IfaceSatAmd64.convT64Code`), an admissible return address and a call
state that satisfies the precondition: `correctness` applies, and `Box(42)` returns a box
holding `42`. -/

namespace Witness

open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64
open Janus.Contracts (IfaceSat.itabAt_TAB IfaceSat.itabResult_R0 IfaceSat.efaceEqual_R0)

/-- `runtime.convT64`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.convT64"

/-- `IfaceSatAmd64.convT64Code` at `runtime.convT64`'s address. -/
def implAt : List Janus.Amd64.Segment := [{ name := "model", base := cAddr, bytes := convT64Code }]

/-- The program linked with it, as a closed program. -/
def linked : Janus.Amd64.Program :=
  { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : ConvT64 (Extracted.program.link implAt) cAddr R0 := by
  rw [linked_eq]
  intro s hpc hpre
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  janus64_run
  refine rtReturn_of R0 1 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl rfl ?_
    ((show Env0 s.mem (s.regs 14) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
  · simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, R0_priv, R0_depth,
      List.append_nil, List.cons_append, List.nil_append]
    janus_frame
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    refine ⟨by decide, ?_, inPriv (by decide) (by decide), ?_⟩
    · rw [Janus.Arm64.Memory.accessible_writeLE]
      exact acc_read_of_write (Janus.Arm64.Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
    · show (Janus.Arm64.Memory.writeLE s.mem 66304 8 _).readLE 66304 8 = _
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (s.regs 0).isLt

/-- The witness return address. -/
def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- The witness memory: `wmem` with the return address `ret` at `[RSP]`. -/
def mem0 : Janus.Arm64.Memory :=
  ⟨fun a => BitVec.ofNat 8 ((((wsp + 2, 0x20) :: wtable).lookup a).getD 0), wmem.regions⟩

/-- The witness call state: `Box(42)`. -/
def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then 42#64 else if i = 4 then BitVec.ofNat 64 wsp
      else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [42#64] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem mem0_env (g : W64) : Env0 mem0 g := by
  refine ⟨by decide, by decide, ?_⟩
  unfold Desc; decide

theorem pre : CallerOK R0 s0 24 8 := by
  refine ⟨mem0_env (s0.regs 14), ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, ?_, ?_, ?_⟩
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : IfaceModel) (ret : Nat)
    (s : Janus.Amd64.State), R.Laws ∧
    ConvT64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.convT64") R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [42#64] s ∧
    CallerOK R s 24 8 :=
  ⟨implAt, R0, ret, s0, R0_laws, model, hret, setup, pre⟩

/-- So the guarantee is reached: `Box(42)` returns a box holding `42`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = uint64Type ∧ BoxHolds R0 s'.mem (s'.regs 3).toNat 8 42 :=
  (correctness implAt R0 R0_laws model 42#64 ret hret s0 setup pre).mono fun _ h =>
    ⟨h.1, h.2.1, h.2.2.1⟩

end Witness

end Proof
