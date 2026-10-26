import Extracted

/-!
# `InsertS(m map[string]uint64, k string, v uint64)` sets `m[k] = v` (arm64)

**Guarantee.** For every model `M` of the map runtime, every readiness predicate `H` and every
`mapassign_faststr` satisfying `MapStr.AssignStr` (8-byte values), every non-nil map `m`
holding `f`, and every call state with the key's bytes readable, outside the stack window and in
the runtime's memory (`StrOwned`: Go strings are immutable, and the map keeps referring to them),
in which the runtime is ready for the call (`H`): the call returns and memory represents `f` with
the key's **content** mapped to `v`, the runtime environment intact. A nil map is not covered
(`mapassign_faststr` panics).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapStr

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x2c) (segWord Extracted.program "example.com/basic.InsertS" 11)
    (segWord Extracted.program "example.com/basic.InsertS" 12) 0

/-- The stack window of `InsertS` and the runtime call. -/
def window (M : MapModel (Nat × Nat) (BitVec 64)) (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - (M.depth + 48), s.sp.toNat + 40)]

/-- The precondition. -/
def pre (M : MapModel (Nat × Nat) (BitVec 64)) (H : RtReady) (m kp kl : BitVec 64)
    (f : AMap (Nat × Nat) (BitVec 64)) (s : State) : Prop :=
  CallerOK M s 48 40 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f ∧
    kp.toNat + kl.toNat ≤ 2 ^ 48 ∧ s.mem.accessible kp.toNat kl.toNat false = true ∧
    Outside kp.toNat kl.toNat (window M s) ∧ StrOwned M kp.toNat kl.toNat ∧
    H [mapType, m.toNat, kp.toNat, kl.toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView M.priv s.mem)

theorem correctness (impl : List Segment) (M : MapModel (Nat × Nat) (BitVec 64)) (hl : M.Laws)
    (H : RtReady) (hasn : AssignStr (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_faststr") 8 M H)
    (m kp kl v : BitVec 64) (f : AMap (Nat × Nat) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp, kl, v] (pre M H m kp kl f)
      (fun s s' => M.Rep s'.mem m.toNat (f.set (strKey s.mem kp.toNat kl.toNat) v) ∧
        M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap, hkb, hka, hko, hown, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  simp only [window, outside_cons, outside_nil, and_true] at hko
  janus_run until [Extracted.program.contractAddr "runtime.mapassign_faststr"]
  have hsp : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; try simp
  have hfw : MemFrame s.mem ((((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE
      (BitVec.toNat s.sp - 56) 8 (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 16) 8 kp.toNat).writeLE
      (BitVec.toNat s.sp + 32) 8 v.toNat)
      [(s.sp.toNat - (M.depth + 48), s.sp.toNat + 40)] := by janus_frame
  refine Reaches.call (Summary.withExit (hasn f) hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp; omega) rfl (by simp [setReg]) (by simp [setReg]) (by decide)
      (by decide), by simpa [setReg] using hty, by simpa [setReg] using hm0, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact hl.rep_frame _ _ _ _ hmap (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))
  · simpa [setReg] using hkb
  · simpa [setReg, hfw.accessible] using hka
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, calleeStack, hsp, outside_cons,
      outside_nil, and_true]
    omega
  · simpa [setReg] using hown
  · simp only [Ready, setReg_apply, reduceIte, Nat.reduceEqDiff]
    repeat rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    rw [hsp]
    simpa using hH
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := InRanges.disjoint hin (Outside.of_sub hout (a := s.sp.toNat - (M.depth + 48))
      (n := M.depth + 48 + 40) (by omega) (by omega))
    have hk := hfw.readLE kp.toNat kl.toNat (by simp only [outside_cons, outside_nil, and_true]; exact hko)
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, strKey, hk] at hset
    simp only [strKey]
    exact ⟨(hset v).1, (hset v).2.1⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The model `MapModel0.MC ckStr` (one map of at most one entry, keyed by a string's content), the
readiness `MapStrSat.HAssignS` (the map is empty, the key does not overlap its header), code
meeting `AssignStr` for them (`MapStrSat.assignStrCode`, reached from the contract's address by
a branch), and a call state inserting the 8-byte string at `SK` (in the runtime's memory) into
the empty non-nil map `MP`: `correctness` applies. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSat Janus.Contracts.MapStrSat

/-- `runtime.mapassign_faststr`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.mapassign_faststr"

/-- The branch at the contract's address and the model code. -/
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := assignStrCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model : AssignStr (Extracted.program.link implAt) cAddr 8 (MC ckStr) HAssignS := by
  have hA : AssignStr (Extracted.program.link implAt) A0 8 (MC ckStr) HAssignS := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (assignStr_impl f)
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

/-- The map `MP`, the key (the 8 bytes at `SK`) and the value. -/
def mv : BitVec 64 := BitVec.ofNat 64 MP
def kp : BitVec 64 := BitVec.ofNat 64 SK
def kl : BitVec 64 := 8#64
def v : BitVec 64 := 42#64

/-- The witness call state: `InsertS(MP, "ABCD\0\0\0\0", 42)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 1 then kp else if i = 2 then kl else if i = 3 then v
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kp, kl, v] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem pre0 : pre (MC ckStr) HAssignS mv kp kl AMap.empty s0 := by
  refine ⟨⟨mmem_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩, trivial, by decide, mmem_repC _, by decide, by decide, ?_,
    Or.inr (inPriv0 (by decide) (by decide)), ?_⟩
  · simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [MC_priv, priv0, outside_cons, outside_nil, and_true]; decide
  · simp only [window, MC_depth, outside_cons, outside_nil, and_true]; decide
  · refine ⟨?_, Or.inr (Or.inr (by decide))⟩
    show (rtView priv0 mmem).readLE MP 8 = 0
    rw [readLE_rtView0 (by decide) (by decide)]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (Nat × Nat) (BitVec 64)) (H : RtReady)
    (ret : Nat) (s : State) (m kp kl v : BitVec 64) (f : AMap (Nat × Nat) (BitVec 64)),
    M.Laws ∧ AssignStr (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_faststr") 8 M H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m, kp, kl, v] s ∧
    pre M H m kp kl f s :=
  ⟨implAt, MC _, HAssignS, ret, s0, mv, kp, kl, v, AMap.empty, MC_laws _, model, hret, setup, pre0⟩

/-- So the guarantee is reached: the map now holds the key's content with `42`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (MC ckStr).Rep s'.mem MP (AMap.empty.set (strKey mmem SK 8) 42#64) :=
  correctness implAt (MC _) (MC_laws _) HAssignS model mv kp kl v AMap.empty ret hret s0 setup pre0
    |>.mono fun _ h => ⟨h.1, h.2.1⟩

end Witness

end Proof
