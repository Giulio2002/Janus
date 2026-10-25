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

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model of the map runtime (`MapStr.MS0`, in which every map is nil), code that meets the
`Access2Str` contract for it (`MapStr.access2StrCode` at `IfaceSat.A0`, reached from the contract's
address by a branch), an admissible return address and a call state looking up the 8-byte string
`VAL` in a nil map: `correctness` applies, and `LookupStr` returns `(0, false)`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel

/-- `runtime.mapaccess2_faststr`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.mapaccess2_faststr"

/-- The branch at the contract's address and the model code. -/
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := access2StrCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model : Access2Str (Extracted.program.link implAt) cAddr MS0 := by
  have hA : Access2Str (Extracted.program.link implAt) A0 MS0 := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (access2Str_impl f)
  intro f s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA f _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

/-- The witness return address. -/
def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- The key: the 8 bytes at `VAL`. -/
def kp : BitVec 64 := BitVec.ofNat 64 VAL
def kl : BitVec 64 := 8#64

/-- The witness call state: `LookupStr(nil, "…")`. -/
def s0 : State :=
  { regs := fun i => if i = 1 then kp else if i = 2 then kl
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [0#64, kp, kl] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

theorem pre0 : CallerOK MS0 s0 48 24 ∧ MS0.Typ mapType ∧ IsMap MS0 s0.mem (0#64).toNat AMap.empty ∧
    kp.toNat + kl.toNat ≤ 2 ^ 48 ∧ s0.mem.accessible kp.toNat kl.toNat false = true ∧
    Outside kp.toNat kl.toNat (window MS0 s0) := by
  refine ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩, trivial, by simp [IsMap], by decide, by decide, ?_⟩
  · simp only [MS0, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [MS0, outside_cons, outside_nil, and_true]; decide
  · simp only [window, MS0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (Nat × Nat) (BitVec 64)) (ret : Nat)
    (s : State) (m kp kl : BitVec 64) (f : AMap (Nat × Nat) (BitVec 64)),
    M.Laws ∧ Access2Str (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2_faststr") M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m, kp, kl] s ∧
    (CallerOK M s 48 24 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f ∧
      kp.toNat + kl.toNat ≤ 2 ^ 48 ∧ s.mem.accessible kp.toNat kl.toNat false = true ∧
      Outside kp.toNat kl.toNat (window M s)) :=
  ⟨implAt, MS0, ret, s0, 0#64, kp, kl, AMap.empty, MS0_laws, model, hret, setup, pre0⟩

/-- So the guarantee is reached: a lookup in a nil map gives `(0, false)`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 0 ∧ (s'.regs 1).toNat % 256 = 0 := by
  refine (correctness implAt MS0 MS0_laws model 0#64 kp kl AMap.empty ret hret s0 setup pre0).mono ?_
  intro s' h
  exact ⟨h.1, by simpa [AMap.empty] using h.2.1, by simpa [AMap.empty] using h.2.2⟩

end Witness

end Proof
