import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapStr

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x28) (segWord Extracted.program "example.com/basic.LookupStr" 10)
    (segWord Extracted.program "example.com/basic.LookupStr" 11) 0

/-- The stack window of `LookupStr` and the runtime call. -/
def window (M : MapModel (Nat × Nat) (BitVec 64)) (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - (M.depth + 48), s.sp.toNat + 24)]

theorem correctness (impl : List Segment) (M : MapModel (Nat × Nat) (BitVec 64)) (hl : M.Laws)
    (hacc : Access2Str (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2_faststr") M)
    (m kp kl : BitVec 64) (f : AMap (Nat × Nat) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp, kl]
      (fun s => CallerOK M s 48 24 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f ∧
        kp.toNat + kl.toNat ≤ 2 ^ 48 ∧ s.mem.accessible kp.toNat kl.toNat false = true ∧
        Outside kp.toNat kl.toNat (window M s))
      (fun s s' => s'.regs 0 = (f (strKey s.mem kp.toNat kl.toNat)).getD 0 ∧
        (s'.regs 1).toNat % 256 = (f (strKey s.mem kp.toNat kl.toNat)).isSome.toNat) := by
  intro ret hret s hs ⟨hc, hty, hmap, hkb, hka, hko⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  simp only [window, outside_cons, outside_nil, and_true] at hko
  janus_run until [Extracted.program.contractAddr "runtime.mapaccess2_faststr"]
  have hsp : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; try simp
  have hfw : MemFrame s.mem (((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE
      (BitVec.toNat s.sp - 56) 8 (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 16) 8 kp.toNat)
      [(s.sp.toNat - (M.depth + 48), s.sp.toNat + 24)] := by janus_frame
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp; omega) rfl (by simp [setReg]) (by simp [setReg]) (by decide)
      (by decide), by simpa [setReg] using hty, ?_, ?_, ?_, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))
  · simpa [setReg] using hkb
  · simpa [setReg, hfw.accessible] using hka
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, calleeStack, hsp, outside_cons,
      outside_nil, and_true]
    omega
  · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩, hok⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    janus_run
    have hk := hfw.readLE kp.toNat kl.toNat (by simp only [outside_cons, outside_nil, and_true]; exact hko)
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, strKey, hk] at hs3 hok
    exact ⟨by rw [hs3]; simp [strKey], by simpa [strKey] using hok⟩

end Proof
