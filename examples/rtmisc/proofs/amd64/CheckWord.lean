import Janus
import Janus.Contracts.InstrumentCallsSatAmd64
import Extracted

/-!
# `Word(p unsafe.Pointer) uint64` built with `-d=checkptr` (amd64)

```go
func Word(p unsafe.Pointer) uint64 { return *(*uint64)(p) }
```

With `-gcflags=…=-d=checkptr` the conversion `(*uint64)(p)` is preceded by a call of
`runtime.checkptrAlignment(p, type:uint64, 1)`, which throws unless the conversion is valid. The
runtime function is left out (`--contract runtime.checkptrAlignment`, pinned to the runtime's
code) and its behaviour is the hypothesis `CheckptrAlignment64` (`Janus/Contracts/InstrumentCallsAmd64.lean`)
over **every** model `C` of the runtime's `checkptrBase` satisfying its laws.

**Guarantee.** For every non-nil `p` whose 8 bytes are readable and do not straddle two Go objects
(`NoStraddle C`: `checkptrBase(p) = checkptrBase(p+7)`, the runtime's own condition for an 8-byte
pointer-free target) and every Go call state with the runtime usable and `C.depth` bytes of stack
below `Word`'s frame (`CallerOK`), the call returns, obeys the ABI, returns the word at
`p`, changes memory only in the runtime's memory and the stack window, and keeps the runtime
usable. `uint64` has no pointers, so the alignment part of the check does not apply (the type
descriptor's `PtrBytes`, read from the extracted data, is 0).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Instrument

namespace Proof

/-- The element type: the RIP-relative `LEAQ` at `Word+0x13` (`type:uint64`). -/
def elemType : Nat := ripTarget Extracted.program (Extracted.entry + 0x13)

theorem correctness (impl : List Janus.Amd64.Segment) (C : CheckptrModel) (hl : C.Laws)
    (hc : CheckptrAlignment64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.checkptrAlignment") C)
    (p : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p]
      (fun s => CallerOK64 C.toRtEnv s 40 16 ∧ Extracted.program.DataLoaded s.mem ∧
        Buffer s p 8 false ∧ p.toNat ≠ 0 ∧ NoStraddle C s.mem (s.regs 14) p.toNat 8 ∧
        Outside p.toNat 8 C.priv ∧
        Spec.Disjoint p.toNat 8 ((s.regs 4).toNat - (C.depth + 40)) (C.depth + 56) ∧
        Spec.Disjoint (s.regs 14).toNat 16 ((s.regs 4).toNat - (C.depth + 40)) (C.depth + 56))
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE p.toNat 8 ∧
        MemFrame s.mem s'.mem (C.priv ++ [((s.regs 4).toNat - (C.depth + 40), (s.regs 4).toNat + 16)]) ∧
        C.Env s'.mem (s.regs 14)) := by
  intro ret hret s hs ⟨hcal, hd, ⟨hp', hp⟩, hp0, hns, hpo, hpd, hgd16⟩
  have hc' := hcal
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hdp, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : elemType
  simp only [regG, regSP, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd hpd hgd16 hal hdp hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.checkptrAlignment"]
  refine Reaches.call (Summary.withExit hc hret) rfl
    ⟨RTPre64.of_caller hl.env hcal (by janus_frame) (by simp [setRegF, hsp40]) (by simp [setRegF])
      (by simpa using hs.zero) (by simpa using hs.df)
      (by simp [setRegF, hsp40, Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide), ?_⟩ ?_
  · right
    have hseg : SegLoaded s.mem (Extracted.program.data[0]'(by decide)) := hd _ (List.getElem_mem _)
    have hacc0 := hseg.accessible
    have hdj1 := hseg.disjoint_of_writable (a := (s.regs 4).toNat - (C.depth + 40)) (n := C.depth + 56)
      (Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
    have hpb := hseg.readLE 8 8 (by decide +kernel)
    have hsz := hseg.readLE 0 8 (by decide +kernel)
    have hlen : (Extracted.program.data[0]'(by decide)).bytes.length = 256 := by decide +kernel
    have hbase : (Extracted.program.data[0]'(by decide)).base = 4732224 := rfl
    have hpb0 : Janus.Tactic.leOfBytes (((Extracted.program.data[0]'(by decide)).bytes.drop 8).take 8) = 0 := by decide +kernel
    have hsz8 : Janus.Tactic.leOfBytes (((Extracted.program.data[0]'(by decide)).bytes.drop 0).take 8) = 8 := by decide +kernel
    rw [hlen, hbase] at hacc0 hdj1
    rw [hbase, hpb0] at hpb
    rw [hbase, hsz8] at hsz
    have hag : Agrees s.mem (((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8 (BitVec.toNat (s.regs 5))).writeLE
        (BitVec.toNat (s.regs 4) + 8) 8 p.toNat).writeLE (BitVec.toNat (s.regs 4) - 40) 8 4701989)
        (C.priv ++ [((s.regs 14).toNat, (s.regs 14).toNat + 16)]) := by
      apply Agrees.of_window (lo := (s.regs 4).toNat - (C.depth + 40)) (hi := (s.regs 4).toNat + 16)
      · janus_frame
      · rw [outside_append]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by simp only [outside_cons, outside_nil, and_true]; omega⟩
    simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, typPtrBytes, typSize,
      Nat.reduceMod, Nat.reducePow, Arm64.Memory.accessible_writeLE, h_a0]
    have e1 : (((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8 (BitVec.toNat (s.regs 5))).writeLE
        (BitVec.toNat (s.regs 4) + 8) 8 p.toNat).writeLE (BitVec.toNat (s.regs 4) - 40) 8 4701989).readLE
        (4732224 + 8) 8 = 0 := by
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact hpb
    have e2 : (((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8 (BitVec.toNat (s.regs 5))).writeLE
        (BitVec.toNat (s.regs 4) + 8) 8 p.toNat).writeLE (BitVec.toNat (s.regs 4) - 40) 8 4701989).readLE
        4732224 8 = 8 := by
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; simpa using hsz
    refine ⟨by decide, Arm64.Memory.accessible_mono _ hacc0 (by omega) (by omega), fun h => absurd e1 h, ?_⟩
    rw [e2]
    unfold NoStraddle
    rw [hl.base_frame _ _ _ hag]
    unfold NoStraddle at hns
    simpa using hns
  · intro s' hpc' ⟨r, x', y, fl, m', _, _, hs', hfr, henv', _⟩
    subst hs'
    simp only [rtWrites64, Contracts.MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    janus64_run
    exact ⟨by janus_frame, by simpa [setRegF] using henv'⟩


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: the model `InstrumentCallsSat.C0`, `RET` at `runtime.checkptrAlignment`'s address, an
admissible return address, and a call state of `Word(&v)` with `v = 42` at `IfaceModel.VAL`, in
a memory with the binary's read-only data loaded. -/

namespace Witness

open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.InstrumentCallsSat
  Janus.Contracts.InstrumentCallsSatAmd64

def cAddr : Nat := Extracted.program.contractAddr "runtime.checkptrAlignment"

def implAt : List Janus.Amd64.Segment := [{ name := "model", base := cAddr, bytes := InstrumentCallsSatAmd64.retCode }]

def linked : Janus.Amd64.Program :=
  { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : CheckptrAlignment64 (Extracted.program.link implAt) cAddr C0 := by
  rw [linked_eq]
  intro s hpc ⟨hpre, _⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx, hdf, hra, hout⟩ := hpre
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hal hd1 hd2 hst hra
  janus64_run
  exact RTReturn64.intro C0.toRtEnv 3 s _ _ rfl rfl rfl rfl rfl rfl (by simp [hdf]) rfl
    (MemFrame.refl _ _) ⟨he1, he2, hd⟩ trivial

def dbyte (a : Nat) : Option Nat :=
  Extracted.program.data.findSome? fun d =>
    if d.base ≤ a ∧ a < d.base + d.bytes.length then d.bytes[a - d.base]? else none

def ret : Nat := wret

/-- The witness memory: `wmem` with the return address `ret` at `[RSP]` and the read-only data. -/
def mem2 : Janus.Arm64.Memory :=
  ⟨fun a => BitVec.ofNat 8 ((dbyte a).getD ((((wsp + 2, 0x20) :: wtable).lookup a).getD 0)),
    wmem.regions ++ Extracted.program.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

theorem mem2_env (g : W64) : Env0 mem2 g := by
  refine ⟨by decide, by decide, ?_⟩
  unfold Desc; decide

theorem mem2_data : Extracted.program.DataLoaded mem2 := by
  unfold Janus.Amd64.Program.DataLoaded; decide +kernel

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide +kernel)

def pv : BitVec 64 := BitVec.ofNat 64 VAL

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then pv else if i = 4 then BitVec.ofNat 64 wsp
      else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem2 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [pv] s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem pre : CallerOK64 C0.toRtEnv s0 40 16 ∧ Extracted.program.DataLoaded s0.mem ∧
    Buffer s0 pv 8 false ∧ pv.toNat ≠ 0 ∧ NoStraddle C0 s0.mem (s0.regs 14) pv.toNat 8 ∧
    Outside pv.toNat 8 C0.priv ∧
    Spec.Disjoint pv.toNat 8 ((s0.regs 4).toNat - (C0.depth + 40)) (C0.depth + 56) ∧
    Spec.Disjoint (s0.regs 14).toNat 16 ((s0.regs 4).toNat - (C0.depth + 40)) (C0.depth + 56) := by
  refine ⟨⟨mem2_env (s0.regs 14), ⟨by decide, by decide, by decide +kernel⟩, by decide, by decide,
    by decide, by decide +kernel, ?_, ?_, ?_⟩, mem2_data, ⟨by decide, by decide +kernel⟩, by decide,
    ?_, ?_, ?_, ?_⟩
  · simp only [C0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [C0_priv, outside_cons, outside_nil, and_true]; decide
  · right; exact ⟨by decide, rfl⟩
  · simp only [C0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · unfold Spec.Disjoint; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (C : CheckptrModel) (ret : Nat)
    (s : Janus.Amd64.State), C.Laws ∧
    CheckptrAlignment64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.checkptrAlignment") C ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [pv] s ∧
    (CallerOK64 C.toRtEnv s 40 16 ∧ Extracted.program.DataLoaded s.mem ∧
      Buffer s pv 8 false ∧ pv.toNat ≠ 0 ∧ NoStraddle C s.mem (s.regs 14) pv.toNat 8 ∧
      Outside pv.toNat 8 C.priv ∧
      Spec.Disjoint pv.toNat 8 ((s.regs 4).toNat - (C.depth + 40)) (C.depth + 56) ∧
      Spec.Disjoint (s.regs 14).toNat 16 ((s.regs 4).toNat - (C.depth + 40)) (C.depth + 56)) :=
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
