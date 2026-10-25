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
  · intro s' hpc' ⟨r, x', y, fl, m', hs', hfr, henv', _⟩
    subst hs'
    simp only [rtWrites64, Contracts.MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    janus64_run
    exact ⟨by janus_frame, by simpa [setRegF] using henv'⟩

end Proof
