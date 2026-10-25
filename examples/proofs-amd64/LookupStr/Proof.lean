import Janus
import Extracted

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64
  Janus.Contracts.MapStr

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x1c)

/-- The stack window of `LookupStr` and the runtime call (amd64). -/
def window (M : MapModel (Nat × Nat) (BitVec 64)) (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - (M.depth + 48), (s.regs 4).toNat + 24)]

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (Nat × Nat) (BitVec 64))
    (hl : M.Laws)
    (hacc : Access2Str64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2_faststr") M)
    (m kp kl : BitVec 64) (f : AMap (Nat × Nat) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp, kl]
      (fun s => CallerOK M s 48 24 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f ∧
        kp.toNat + kl.toNat ≤ 2 ^ 48 ∧ s.mem.accessible kp.toNat kl.toNat false = true ∧
        Outside kp.toNat kl.toNat (window M s))
      (fun s s' => s'.regs 0 = (f (strKey s.mem kp.toNat kl.toNat)).getD 0 ∧
        (s'.regs 3).toNat % 256 = (f (strKey s.mem kp.toNat kl.toNat)).isSome.toNat) := by
  intro ret hret s hs ⟨hc, hty, hmap, hkb, hka, hko⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  simp only [window, outside_cons, outside_nil, and_true] at hko
  have hsp48 : (s.regs 4 - 48#64).toNat = (s.regs 4).toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapaccess2_faststr"]
  have hfw : MemFrame s.mem (((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) + 16) 8 kp.toNat).writeLE
      (BitVec.toNat (s.regs 4) - 48) 8 4741512)
      [((s.regs 4).toNat - (M.depth + 48), (s.regs 4).toNat + 24)] := by janus_frame
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp [setRegF, hsp48]) (by simp [setRegF]) (by simpa using hs.zero)
      (by simpa using hs.df) (by simp [setRegF, hsp48, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), by simpa [setRegF] using hty, ?_, ?_, ?_, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))
  · simpa [setRegF] using hkb
  · simpa [setRegF, hfw.accessible] using hka
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, calleeStack, hsp48, outside_cons,
      outside_nil, and_true]
    omega
  · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩, hok⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp48] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    have hk := hfw.readLE kp.toNat kl.toNat (by simp only [outside_cons, outside_nil, and_true]; exact hko)
    janus64_run
    all_goals try simp only [setRegF, reduceIte, Nat.reduceEqDiff, strKey, hk] at hs3 hok
    all_goals first | exact hok | (simpa [strKey] using hok) | (simp [strKey, hk]; done) | (simp [strKey, hk]; exact hok) | exact ⟨by rw [hs3]; simp [strKey], by simpa [strKey] using hok⟩

end Proof
