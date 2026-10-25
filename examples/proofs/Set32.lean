import Extracted

/-!
# `Set32(m map[uint32]bool, k uint32)` sets `m[k] = true` (arm64)

**Guarantee.** For every model `M` of the map runtime with 1-byte values (a `bool` is the byte
`0` or `1`), every readiness predicate `H` and every `mapassign_fast32` satisfying
`MapVar.AssignF32` with `vs = 1`, every non-nil map `m` holding `f`, and every call state
satisfying `CallerOK` in which the runtime is ready for the call (`H`): the call returns and
memory represents `f` with the 32-bit key `k` (the low half of the argument register) mapped to
`true` (`1#8`), the runtime environment intact. A nil map is not covered (`mapassign_fast32`
panics).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.Set32" 8)
    (segWord Extracted.program "example.com/basic.Set32" 9) 0

/-- The precondition. -/
def pre (M : MapModel (BitVec 32) (BitVec (8 * 1))) (H : RtReady) (m k : BitVec 64)
    (f : AMap (BitVec 32) (BitVec (8 * 1))) (s : State) : Prop :=
  CallerOK M s 48 0 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f ∧
    H [mapType, m.toNat, (k.setWidth 32).toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView M.priv s.mem)

theorem correctness (impl : List Segment) (M : MapModel (BitVec 32) (BitVec (8 * 1))) (hl : M.Laws)
    (H : RtReady) (hasn : AssignF32 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast32") 1 M H)
    (m k : BitVec 64) (f : AMap (BitVec 32) (BitVec (8 * 1))) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k] (pre M H m k f)
      (fun s s' => M.Rep s'.mem m.toNat (f.set (k.setWidth 32) 1#8) ∧ M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.mapassign_fast32"]
  refine Reaches.call (Summary.withExit (hasn f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg])
      (by decide) (by decide), by simpa [setReg] using hty, by simpa [setReg] using hm0, ?_, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact hl.rep_frame _ _ _ _ hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 48))
      (hi := s.sp.toNat + 0) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · simp only [Ready, setReg_apply, reduceIte, Nat.reduceEqDiff, key32]
    repeat rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    rw [show (s.sp - 48#64).toNat = s.sp.toNat - 48 by
        rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl]
    simpa using hH
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 1 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := InRanges.disjoint hin (Outside.of_sub hout (a := s.sp.toNat - (M.depth + 48))
      (n := M.depth + 48 + 0) (by omega) (by omega))
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, key32] at hset
    exact ⟨(hset 1#8).1, (hset 1#8).2.1⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model with 1-byte values (`MCW`: `MapModel0.MC`, one map of at most one entry at `MP`, with a
1-byte value slot), the readiness `MapModel0.HAssign` (the map is empty), code meeting
`AssignF32` for them (`MapVarSat.assignF32Code`: `used = 1`, store the key, return the slot
`MP + 32`), and a call state setting the key `7` in the empty non-nil map `MP`: `correctness`
applies (`returns`: the map then holds `7 ↦ true`). -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSat Janus.Contracts.MapVarSat

/-- The model's private memory. -/
def privW : List (Nat × Nat) := priv0 ++ []

/-- The value of the cell (`1` bytes at `MP + 32`) under its key `ck.get m`. -/
def cellW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Memory) : AMap K (BitVec (8 * 1)) :=
  fun k => if k = ck.get m then some (BitVec.ofNat (8 * 1) (m.readLE (MP + 32) 1)) else none

/-- `MapModel0.MC` with `1`-byte values and the private memory `privW`. -/
def MCW {K : Type} [DecidableEq K] (ck : CellKey K) : MapModel K (BitVec (8 * 1)) where
  Rep m mp f := mp = MP ∧ m.accessible MP 56 true = true ∧ m.readLE (MP + 48) 8 = 1 ∧
    ((m.readLE MP 8 = 0 ∧ f = AMap.empty) ∨ (m.readLE MP 8 = 1 ∧ f = cellW ck m))
  Iter _ _ _ _ _ := False
  Typ _ := True
  Env m _ := ZEnv m
  priv := privW
  depth := 64

theorem agreesW {m m' : Memory} (ha : Agrees m m' privW) : Agrees m m' priv0 :=
  ⟨ha.1, fun a h => ha.2 a (h.append_left _)⟩

theorem inPrivW {a n : Nat} (h1 : 0x10000 ≤ a) (h2 : a + n ≤ 0x11000) : InRanges a n privW :=
  (inPriv0 h1 h2).append_left _

theorem keys_cellW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Memory) :
    Keys (cellW ck m) [ck.get m] :=
  ⟨List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun k => by
    simp only [List.mem_singleton, cellW]; split <;> simp_all⟩

theorem MCW_laws {K : Type} [DecidableEq K] (ck : CellKey K) : (MCW ck).Laws where
  rep_frame m m' mp f h ha := by
    have ha0 := agreesW ha
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hu : m'.readLE MP 8 = m.readLE MP 8 := readLE_of_agrees ha0 (by decide) (by decide)
    have hc : cellW ck m' = cellW ck m := by
      funext k
      simp only [cellW, ck.frame m m' ha0, readLE_of_agrees ha0 (a := MP + 32) (n := 1) (by decide) (by decide)]
    refine ⟨h1, by rw [ha.accessible]; exact h2,
      (readLE_of_agrees ha0 (by decide) (by decide)).trans h3, ?_⟩
    rw [hu, hc]; exact h4
  iter_frame _ _ _ _ _ _ h _ := h.elim
  env_frame m m' _ h ha := ZEnv.frame h (agreesW ha)
  len m mp f h := by
    obtain ⟨rfl, h2, -, h4⟩ := h
    refine ⟨Memory.accessible_mono _ (IfaceModel.acc_read_of_write h2) (Nat.le_refl _) (by decide),
      by decide, fun ks hk => ?_⟩
    rcases h4 with ⟨hu, rfl⟩ | ⟨hu, rfl⟩
    · rw [hu, hk.eq_nil_of_empty]; rfl
    · rw [hu, hk.length_eq (keys_cellW ck m)]; rfl
  finite m mp f h := by
    obtain ⟨-, -, -, h4⟩ := h
    rcases h4 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨[], keys_empty⟩
    · exact ⟨_, keys_cellW ck m⟩

/-- An assignment's readiness in `MCW` (`MapModel0.HAssign` on `privW`): the map is empty. -/
theorem mcw_empty {K : Type} [DecidableEq K] {ck : CellKey K} {s : State} {f : AMap K (BitVec (8 * 1))}
    (hrep : (MCW ck).Rep s.mem (s.regs 1).toNat f) (args : List Nat)
    (hH : Ready HAssign (MCW ck).priv args s) :
    (s.regs 1).toNat = MP ∧ s.mem.accessible MP 56 true = true ∧ s.mem.readLE (MP + 48) 8 = 1 ∧
      f = AMap.empty := by
  obtain ⟨hmp, hacc, hal, hu⟩ := hrep
  have h0 : s.mem.readLE MP 8 = 0 := by
    have := hH; simp only [Ready, HAssign, MCW] at this
    rwa [readLE_rtView (inPrivW (a := MP) (n := 8) (by decide) (by decide))] at this
  refine ⟨hmp, hacc, hal, ?_⟩
  rcases hu with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · omega

/-- What an `MCW` assignment returns (as `MapModel0.cell_assign`). -/
theorem cell_assignW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Memory) (k : K) (g : W64)
    (hacc : m.accessible MP 56 true = true) (hal : m.readLE (MP + 48) 8 = 1) (hu : m.readLE MP 8 = 1)
    (hk : ∀ v, ck.get (m.writeLE (MP + 32) 1 v) = k) (hze : ZEnv m) :
    Map.AssignSlot 1 (MCW ck) MP AMap.empty k g (MP + 32) m := by
  refine ⟨Memory.accessible_mono _ hacc (by decide) (by decide), inPrivW (by decide) (by decide),
    fun v => ⟨?_, hze.writeLE _ (by decide), fun mp' _ hne h => absurd h.1 hne⟩⟩
  have hv : v.toNat % 256 ^ 1 = v.toNat :=
    Nat.mod_eq_of_lt (by have := v.isLt; rwa [Nat.pow_mul] at this)
  have e : (AMap.empty : AMap K (BitVec (8 * 1))).set k v = cellW ck (m.writeLE (MP + 32) 1 v.toNat) := by
    funext k'
    simp only [AMap.set, cellW, hk, Memory.readLE_writeLE_self, hv,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
    split <;> rfl
  rw [e]
  exact ⟨rfl, by rw [Memory.accessible_writeLE]; exact hacc,
    by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal,
    Or.inr ⟨by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hu, rfl⟩⟩


theorem assignF32_implW : AssignF32 (toy.link (at0 assignF32Code)) A0 1 (MCW ck32) HAssign := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hm0, hrep, hH⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  obtain ⟨hmp, hacc, hal, rfl⟩ := mcw_empty hrep _ hH
  simp only [MP] at hacc
  janus_run
  have hfr : MemFrame s.mem ((s.mem.writeLE 67584 8 1).writeLE 67592 4 (BitVec.toNat (s.regs 2)))
      (rtWrites (MCW ck32) s 3 ++ []) := by
    simp only [rtWrites, calleeStack, MCW, privW, priv0, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  have hm1 : (s.mem.writeLE MP 8 1).accessible MP 56 true = true := by
    rw [Memory.accessible_writeLE]; exact hacc
  refine MapSat.mapReturn_of (MCW ck32) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl hfr ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  exact cell_assignW ck32 _ _ (s.regs 28) (by rw [Memory.accessible_writeLE]; exact hm1)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_self])
    (fun v => by
      show BitVec.ofNat 32 (Memory.readLE _ (MP + 8) 4) = _
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_self]
      apply BitVec.eq_of_toNat_eq
      simp [key32, BitVec.toNat_setWidth])
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))

/-- `runtime.mapassign_fast32`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.mapassign_fast32"

/-- The branch at the contract's address and the model code. -/
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := assignF32Code }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model : AssignF32 (Extracted.program.link implAt) cAddr 1 (MCW ck32) HAssign := by
  have hA : AssignF32 (Extracted.program.link implAt) A0 1 (MCW ck32) HAssign := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (assignF32_implW f)
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

/-- The map `MP` and the key `7`. -/
def mv : BitVec 64 := BitVec.ofNat 64 MP
def kv : BitVec 64 := 7#64

/-- The witness call state: `Set32(MP, 7)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 1 then kv
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kv] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem pre0 : pre (MCW ck32) HAssign mv kv AMap.empty s0 := by
  refine ⟨⟨mmem_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩, trivial, by decide,
    ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩, ?_⟩
  · simp only [MCW, privW, priv0, List.append_nil, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [MCW, privW, priv0, List.append_nil, outside_cons, outside_nil, and_true]; decide
  · show (rtView privW mmem).readLE MP 8 = 0
    rw [readLE_rtView (inPrivW (by decide) (by decide))]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec 32) (BitVec (8 * 1))) (H : RtReady)
    (ret : Nat) (s : State) (m k : BitVec 64) (f : AMap (BitVec 32) (BitVec (8 * 1))),
    M.Laws ∧ AssignF32 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast32") 1 M H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m, k] s ∧
    m.toNat ≠ 0 ∧ pre M H m k f s :=
  ⟨implAt, MCW _, HAssign, ret, s0, mv, kv, AMap.empty, MCW_laws _, model, hret, setup, by decide, pre0⟩

/-- So the guarantee is reached: the map now holds `7 ↦ true`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (MCW ck32).Rep s'.mem MP (AMap.empty.set 7#32 1#8) :=
  correctness implAt (MCW _) (MCW_laws _) HAssign model mv kv AMap.empty ret hret s0 setup pre0
    |>.mono fun _ h => ⟨h.1, h.2.1⟩

end Witness

end Proof
