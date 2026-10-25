import Extracted
import Janus.Contracts.InstrumentSat

/-!
# `Word(p unsafe.Pointer) uint64` built with `-d=checkptr` (arm64)

```go
func Word(p unsafe.Pointer) uint64 { return *(*uint64)(p) }
```

With `-gcflags=…=-d=checkptr` the conversion `(*uint64)(p)` is preceded by a call of
`runtime.checkptrAlignment(p, type:uint64, 1)`, which throws unless the conversion is valid. The
runtime function is left out (`--contract runtime.checkptrAlignment`, pinned to the runtime's
code) and its behaviour is the hypothesis `CheckptrAlignment` (`Janus/Contracts/InstrumentCalls.lean`)
over **every** model `C` of the runtime's `checkptrBase` satisfying its laws.

**Guarantee.** For every non-nil `p` whose 8 bytes are readable and do not straddle two Go objects
(`NoStraddle C`: `checkptrBase(p) = checkptrBase(p+7)`, the runtime's own condition for an 8-byte
pointer-free target) and every Go call state with the runtime usable and `C.depth` bytes of stack
below `Word`'s 48-byte frame (`CallerOK`), the call returns, obeys the ABI, returns the word at
`p`, changes memory only in the runtime's memory and the stack window, and keeps the runtime
usable. `uint64` has no pointers, so the alignment part of the check does not apply (the type
descriptor's `PtrBytes`, read from the extracted data, is 0).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Instrument

namespace Proof

/-- The element type: `ADRP`+`ADD` at `Word+0x1c` (`type:uint64`). -/
def elemType : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "example.com/rtmisc/checkptr.Word" 7)
    (segWord Extracted.program "example.com/rtmisc/checkptr.Word" 8) 0

theorem correctness (impl : List Segment) (C : CheckptrModel) (hl : C.Laws)
    (hc : CheckptrAlignment (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.checkptrAlignment") C)
    (p : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p]
      (fun s => CallerOK C.toRtEnv s 48 16 ∧ Extracted.program.DataLoaded s.mem ∧
        Ptr s.mem p 8 false ∧ p.toNat ≠ 0 ∧ NoStraddle C s.mem (s.regs 28) p.toNat 8 ∧
        Outside p.toNat 8 C.priv ∧ Disjoint p.toNat 8 (s.sp.toNat - (C.depth + 48)) (C.depth + 64) ∧
        Disjoint (s.regs 28).toNat 16 (s.sp.toNat - (C.depth + 48)) (C.depth + 64))
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE p.toNat 8 ∧
        MemFrame s.mem s'.mem (C.priv ++ [(s.sp.toNat - (C.depth + 48), s.sp.toNat + 16)]) ∧
        C.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hcal, hd, ⟨hp, hp'⟩, hp0, hns, hpo, hpd, hgd16⟩
  have hc' := hcal
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hdp, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : elemType
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd hpd hgd16
  janus_run until [Extracted.program.contractAddr "runtime.checkptrAlignment"]
  refine Reaches.call (Summary.withExit hc hret) rfl
    ⟨RTPre.of_caller hl.env hcal (by janus_frame) (by simp; omega) rfl (by simp [setReg])
      (by simp [setReg]) (by decide) (by decide), ?_⟩ ?_
  · right
    have hseg : SegLoaded s.mem (Extracted.program.data[0]'(by decide)) :=
      SegLoaded.of_dataLoaded hd (List.getElem_mem _)
    have hacc0 := hseg.accessible
    have hdj1 := hseg.disjoint_of_writable (a := BitVec.toNat s.sp - (C.depth + 48)) (n := C.depth + 64)
      (Memory.accessible_mono _ hst (by omega) (by omega))
    have hpb := hseg.readLE 8 8 (by decide +kernel)
    have hsz := hseg.readLE 0 8 (by decide +kernel)
    have hlen : (Extracted.program.data[0]'(by decide)).bytes.length = 256 := by decide +kernel
    have hbase : (Extracted.program.data[0]'(by decide)).base = 615680 := rfl
    have hpb0 : leOfBytes (((Extracted.program.data[0]'(by decide)).bytes.drop 8).take 8) = 0 := by decide +kernel
    have hsz8 : leOfBytes (((Extracted.program.data[0]'(by decide)).bytes.drop 0).take 8) = 8 := by decide +kernel
    rw [hlen, hbase] at hacc0 hdj1
    rw [hbase, hpb0] at hpb
    rw [hbase, hsz8] at hsz
    have hag : Agrees s.mem ((((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
        (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 8) 8 p.toNat))
        (C.priv ++ [((s.regs 28).toNat, (s.regs 28).toNat + 16)]) := by
      apply Agrees.of_window (lo := BitVec.toNat s.sp - (C.depth + 48)) (hi := BitVec.toNat s.sp + 16)
      · janus_frame
      · rw [outside_append]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by simp only [outside_cons, outside_nil, and_true]; omega⟩
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, typPtrBytes, typSize,
      Nat.reduceMod, Nat.reducePow, Memory.accessible_writeLE, h_x0]
    have e1 : (((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
        (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 8) 8 p.toNat).readLE (615680 + 8) 8 = 0 := by
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact hpb
    have e2 : (((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
        (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 8) 8 p.toNat).readLE 615680 8 = 8 := by
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; simpa using hsz
    refine ⟨by decide, Memory.accessible_mono _ hacc0 (by omega) (by omega), fun h => absurd e1 h, ?_⟩
    rw [e2]
    unfold NoStraddle
    rw [hl.base_frame _ _ _ hag]
    unfold NoStraddle at hns
    simpa using hns
  · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', _⟩
    subst hs'
    simp only [rtWrites, calleeStack] at hfr
    janus_run
    exact ⟨by janus_frame, henv'⟩


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The model `InstrumentSat.C0` (laws `C0_laws`), the implementation `RET` at
`runtime.checkptrAlignment`'s address (it meets `CheckptrAlignment` for `C0`, `model`), an
admissible return address, and a call state of `Word(&v)` for the word `v = 42` at
`IfaceModel.VAL`, in a memory with the binary's read-only data loaded. -/

namespace Witness

open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat Janus.Contracts.InstrumentSat

/-- `runtime.checkptrAlignment`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.checkptrAlignment"

def implAt : List Segment := [{ name := "model", base := cAddr, words := retCode }]

def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : CheckptrAlignment (Extracted.program.link implAt) cAddr C0 := by
  rw [linked_eq]
  intro s hpc ⟨hpre, _⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  exact RTReturn.intro C0.toRtEnv 3 s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _)
    ⟨he1, he2, hd⟩ trivial

/-- A byte of the program's read-only data, if `a` is in one of its objects. -/
def dbyte (a : Nat) : Option Nat :=
  Extracted.program.data.findSome? fun d =>
    if d.base ≤ a ∧ a < d.base + d.bytes.length then d.bytes[a - d.base]? else none

/-- The witness memory: `IfaceModel.wmem` and the read-only data in read-only regions. -/
def mem2 : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((dbyte a).getD ((wtable.lookup a).getD 0)),
    wmem.regions ++ Extracted.program.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

theorem mem2_env (g : W64) : Env0 mem2 g := by
  refine ⟨by decide, by decide, ?_⟩
  unfold Desc; decide

theorem mem2_data : Extracted.program.DataLoaded mem2 := by
  unfold Program.DataLoaded; decide +kernel

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide +kernel)

/-- `p = &v`, `v = 42`. -/
def pv : BitVec 64 := BitVec.ofNat 64 VAL

def s0 : State :=
  { regs := fun i => if i = 0 then pv else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem2 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [pv] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

theorem pre : CallerOK C0.toRtEnv s0 48 16 ∧ Extracted.program.DataLoaded s0.mem ∧
    Ptr s0.mem pv 8 false ∧ pv.toNat ≠ 0 ∧ NoStraddle C0 s0.mem (s0.regs 28) pv.toNat 8 ∧
    Outside pv.toNat 8 C0.priv ∧ Disjoint pv.toNat 8 (s0.sp.toNat - (C0.depth + 48)) (C0.depth + 64) ∧
    Disjoint (s0.regs 28).toNat 16 (s0.sp.toNat - (C0.depth + 48)) (C0.depth + 64) := by
  refine ⟨⟨mem2_env (s0.regs 28), ⟨by decide, by decide, by decide +kernel⟩, by decide, by decide, by decide, by decide,
    by decide +kernel, ?_, ?_, ?_⟩, mem2_data, ⟨by decide +kernel, by decide⟩, by decide, ?_, ?_, ?_, ?_⟩
  · simp only [C0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [C0_priv, outside_cons, outside_nil, and_true]; decide
  · right; exact ⟨by decide, rfl⟩
  · simp only [C0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · unfold Disjoint; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (C : CheckptrModel) (ret : Nat) (s : State), C.Laws ∧
    CheckptrAlignment (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.checkptrAlignment") C ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [pv] s ∧
    (CallerOK C.toRtEnv s 48 16 ∧ Extracted.program.DataLoaded s.mem ∧
      Ptr s.mem pv 8 false ∧ pv.toNat ≠ 0 ∧ NoStraddle C s.mem (s.regs 28) pv.toNat 8 ∧
      Outside pv.toNat 8 C.priv ∧ Disjoint pv.toNat 8 (s.sp.toNat - (C.depth + 48)) (C.depth + 64) ∧
      Disjoint (s.regs 28).toNat 16 (s.sp.toNat - (C.depth + 48)) (C.depth + 64)) :=
  ⟨implAt, C0, ret, s0, C0_laws, model, hret, setup, pre⟩

/-- So the guarantee is reached: `Word(&v)` returns `42`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 42 := by
  refine Returns.mono (correctness implAt C0 C0_laws model pv ret hret s0 setup pre) ?_
  intro s' ⟨habi, h0, _, _⟩
  refine ⟨habi, ?_⟩
  rw [h0]; decide +kernel

end Witness

end Proof
