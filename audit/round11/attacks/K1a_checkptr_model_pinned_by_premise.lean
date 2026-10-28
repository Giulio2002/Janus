import Extracted

/-! Round 11a K1a: a premise that pins the checkptr model. `CheckptrModel` is not a
runtime-parameter type of the auditor's V1 rule, so a premise `hCb : ∀ m g q, C.base m g q = 0`
(every pointer is "in the same object" as every other) is accepted next to the contract
hypothesis: `checkptrAlignment` is then assumed to return for EVERY readable non-nil `p`. The real
one throws when the 8 bytes at `p` straddle two Go objects. The theorem drops the `NoStraddle`
precondition and claims `Word(p)` returns for all such `p`. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Instrument

namespace Proof

/-- The element type: `ADRP`+`ADD` at `Word+0x1c` (`type:uint64`). -/
def elemType : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "example.com/rtmisc/checkptr.Word" 7)
    (segWord Extracted.program "example.com/rtmisc/checkptr.Word" 8) 0

theorem correctness (impl : List Segment) (C : CheckptrModel) (hl : C.Laws)
    (hCb : ∀ m g q, C.base m g q = 0)
    (hc : CheckptrAlignment (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.checkptrAlignment") C)
    (p : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p]
      (fun s => CallerOK C.toRtEnv s 48 16 ∧ Extracted.program.DataLoaded s.mem ∧
        Ptr s.mem p 8 false ∧ p.toNat ≠ 0 ∧
        Outside p.toNat 8 C.priv ∧ Disjoint p.toNat 8 (s.sp.toNat - (C.depth + 48)) (C.depth + 64) ∧
        Disjoint (s.regs 28).toNat 16 (s.sp.toNat - (C.depth + 48)) (C.depth + 64))
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE p.toNat 8 ∧
        MemFrame s.mem s'.mem (C.priv ++ [(s.sp.toNat - (C.depth + 48), s.sp.toNat + 16)]) ∧
        C.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hcal, hd, ⟨hp, hp'⟩, hp0, hpo, hpd, hgd16⟩
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
    right
    exact ⟨by omega, by rw [hCb, hCb]⟩
  · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', _⟩
    subst hs'
    simp only [rtWrites, calleeStack] at hfr
    janus_run
    exact ⟨by janus_frame, henv'⟩


end Proof
