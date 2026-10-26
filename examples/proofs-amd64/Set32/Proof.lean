import Janus
import Extracted

/-!
# `Set32(m map[uint32]bool, k uint32)` sets `m[k] = true` (amd64)

As on arm64, under `MapVarAmd64.AssignF32` with `vs = 1` and a readiness predicate `H` at
entry (`RSP` of the call `40` bytes below the entry's); the key is the low 32 bits of the
argument register (`MOVL BX, CX`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64
  Janus.Contracts.MapVarAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x13)

/-- The return address the call at `Extracted.entry + 0x1a` pushes. -/
def ret1f : Nat := Extracted.entry + 0x1f

/-- The precondition. -/
def pre (M : MapModel (BitVec 32) (BitVec (8 * 1))) (H : Contracts.RtReady) (m k : BitVec 64)
    (f : AMap (BitVec 32) (BitVec (8 * 1))) (s : State) : Prop :=
  CallerOK M s 40 8 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f ∧
    H [mapType, m.toNat, (k.setWidth 32).toNat] (s.regs 14).toNat ((s.regs 4).toNat - 40)
      (Contracts.rtView M.priv s.mem)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 32) (BitVec (8 * 1)))
    (hl : M.Laws) (H : Contracts.RtReady)
    (hasn : AssignF32 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast32") 1 M H)
    (m k : BitVec 64) (f : AMap (BitVec 32) (BitVec (8 * 1))) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k] (pre M H m k f)
      (fun s s' => M.Rep s'.mem m.toNat (f.set (k.setWidth 32) 1#8) ∧ M.Env s'.mem (s.regs 14)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hkk : ((k.setWidth 32).setWidth 64).setWidth 32 = k.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  janus64_run until [Extracted.program.contractAddr "runtime.mapassign_fast32"]
  have hfw : MemFrame s.mem ((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 ret1f)
      [((s.regs 4).toNat - (M.depth + 40), (s.regs 4).toNat + 8)] := by janus_frame
  janus_eval_nat hR : ret1f
  simp only [hR] at hfw
  refine Reaches.call (Summary.withExit (hasn f) hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp [setRegF, hsp40]) (by simp [setRegF]) (by simpa using hs.zero)
      (by simpa using hs.df) (by simp [setRegF, hsp40, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), by simpa [setRegF] using hty, by simpa [setRegF] using hm0, ?_, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact hl.rep_frame _ _ _ _ hmap (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))
  · simp only [Contracts.Ready64, setRegF, reduceIte, Nat.reduceEqDiff, hsp40, key32, hkk]
    repeat rw [Contracts.rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    simpa using hH
  · intro s' hpc' ⟨r, x, y, fl, m', _, _, hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, key32, hkk] at hset
    have hacc0 : s.mem.accessible (r 0).toNat 1 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := Janus.InRanges.disjoint hin (Outside.of_sub hout (a := (s.regs 4).toNat - (M.depth + 40))
      (n := M.depth + 40 + 8) (by omega) (by omega))
    janus64_run
    exact ⟨(hset 1#8).1, (hset 1#8).2.1⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: `MCW` (`MapModel0.MC` with a 1-byte value slot), the readiness `MapModel0.HAssign`,
the code `MapVarSatAmd64.assign32Code` (`used = 1`, the 4-byte key, the slot `MP + 32`) behind a
`JMP` at the contract's address, and a call setting the key `7` in the empty map `MP`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64 Janus.Contracts.MapVarSatAmd64
open Janus.Contracts (RtReady rtView readLE_rtView Ready64)

/-- The model's private memory. -/
def privW : List (Nat × Nat) := priv0 ++ []

/-- The value of the cell (`1` bytes at `MP + 32`) under its key `ck.get m`. -/
def cellW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Janus.Arm64.Memory) : AMap K (BitVec (8 * 1)) :=
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

theorem agreesW {m m' : Janus.Arm64.Memory} (ha : Agrees m m' privW) : Agrees m m' priv0 :=
  ⟨ha.1, fun a h => ha.2 a (h.append_left _)⟩

theorem inPrivW {a n : Nat} (h1 : 0x10000 ≤ a) (h2 : a + n ≤ 0x11000) : InRanges a n privW :=
  (inPriv0 h1 h2).append_left _

theorem keys_cellW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Janus.Arm64.Memory) :
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
    refine ⟨Janus.Arm64.Memory.accessible_mono _ (Janus.Contracts.IfaceModel.acc_read_of_write h2) (Nat.le_refl _) (by decide),
      by decide, fun ks hk => ?_⟩
    rcases h4 with ⟨hu, rfl⟩ | ⟨hu, rfl⟩
    · rw [hu, hk.eq_nil_of_empty]; rfl
    · rw [hu, hk.length_eq (keys_cellW ck m)]; rfl
  finite m mp f h := by
    obtain ⟨-, -, -, h4⟩ := h
    rcases h4 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨[], keys_empty⟩
    · exact ⟨_, keys_cellW ck m⟩

/-- An assignment's readiness in `MCW` (amd64): the map is empty. -/
theorem mcw_empty {K : Type} [DecidableEq K] {ck : CellKey K} {s : State} {f : AMap K (BitVec (8 * 1))}
    (hrep : (MCW ck).Rep s.mem (s.regs 3).toNat f) (args : List Nat)
    (hH : Ready64 HAssign (MCW ck).priv args s) :
    (s.regs 3).toNat = MP ∧ s.mem.accessible MP 56 true = true ∧ s.mem.readLE (MP + 48) 8 = 1 ∧
      f = AMap.empty := by
  obtain ⟨hmp, hacc, hal, hu⟩ := hrep
  have h0 : s.mem.readLE MP 8 = 0 := by
    have := hH; simp only [Ready64, HAssign, MCW] at this
    rwa [readLE_rtView (inPrivW (a := MP) (n := 8) (by decide) (by decide))] at this
  refine ⟨hmp, hacc, hal, ?_⟩
  rcases hu with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · omega

/-- What an `MCW` assignment returns (as `MapModel0.cell_assign`). -/
theorem cell_assignW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Janus.Arm64.Memory) (k : K) (g : W64)
    (hacc : m.accessible MP 56 true = true) (hal : m.readLE (MP + 48) 8 = 1) (hu : m.readLE MP 8 = 1)
    (hk : ∀ v, ck.get (m.writeLE (MP + 32) 1 v) = k) (hze : ZEnv m) :
    Janus.Contracts.MapAmd64.AssignSlot 1 (MCW ck) MP AMap.empty k g (MP + 32) m := by
  refine ⟨Janus.Arm64.Memory.accessible_mono _ hacc (by decide) (by decide), inPrivW (by decide) (by decide),
    fun v => ⟨?_, hze.writeLE _ (by decide), fun mp' _ hne h => absurd h.1 hne⟩⟩
  have hv : v.toNat % 256 ^ 1 = v.toNat :=
    Nat.mod_eq_of_lt (by have := v.isLt; rwa [Nat.pow_mul] at this)
  have e : (AMap.empty : AMap K (BitVec (8 * 1))).set k v = cellW ck (m.writeLE (MP + 32) 1 v.toNat) := by
    funext k'
    simp only [AMap.set, cellW, hk, Janus.Arm64.Memory.readLE_writeLE_self, hv,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
    split <;> rfl
  rw [e]
  exact ⟨rfl, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hacc,
    by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal,
    Or.inr ⟨by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hu, rfl⟩⟩


theorem assignF32_implW : AssignF32 (toy.link (at0 assign32Code)) A0 1 (MCW ck32) HAssign := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hm0, hrep, hH⟩ := hpre
  obtain ⟨hmp, hacc, hal, rfl⟩ := mcw_empty hrep _ hH
  simp only [MP] at hacc
  have hout' := hout
  simp only [MCW, privW, priv0, List.append_nil, outside_cons, outside_nil, and_true] at hout'
  janus64_run
  have hfr : MemFrame s.mem ((Janus.Arm64.Memory.writeLE s.mem 67584 8 1).writeLE 67592 4
      (BitVec.toNat (s.regs 1) % 4294967296)) (rtWrites (MCW ck32) s 3 ++ []) := by
    simp only [rtWrites, Janus.Contracts.MapAmd64.calleeStack, MCW, privW, priv0, List.append_nil,
      List.cons_append, List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  have hm1 : (s.mem.writeLE MP 8 1).accessible MP 56 true = true := by
    rw [Janus.Arm64.Memory.accessible_writeLE]; exact hacc
  refine Janus.Contracts.MapStr.mapReturn64_of (MCW ck32) 3 [] _ s _ _ (by simp [retAddrOf])
    (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl hfr
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  exact cell_assignW ck32 _ _ (s.regs 14) (by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hm1)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Janus.Arm64.Memory.readLE_writeLE_self])
    (fun v => by
      show BitVec.ofNat _ (Janus.Arm64.Memory.readLE _ (MP + 8) 4) = _
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
        Janus.Arm64.Memory.readLE_writeLE_self]
      apply BitVec.eq_of_toNat_eq
      simp only [key32, BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega)
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))

def cAddr : Nat := Extracted.program.contractAddr "runtime.mapassign_fast32"

def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := assign32Code }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model : AssignF32 (Extracted.program.link implAt) cAddr 1 (MCW ck32) HAssign := by
  have hA : AssignF32 (Extracted.program.link implAt) A0 1 (MCW ck32) HAssign := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (assignF32_implW f)
  intro f s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA f _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def mv : BitVec 64 := BitVec.ofNat 64 MP
def kv : BitVec 64 := 7#64

/-- The witness call state: `Set32(MP, 7)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 3 then kv
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mmem64 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kv] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem pre0 : pre (MCW ck32) HAssign mv kv AMap.empty s0 := by
  refine ⟨⟨mmem64_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, ?_, ?_, ?_⟩, trivial, by decide,
    ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩, ?_⟩
  · simp only [MCW, privW, priv0, List.append_nil, outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide
  · simp only [MCW, privW, priv0, List.append_nil, outside_cons, outside_nil, and_true]; decide
  · show (rtView privW mmem64).readLE MP 8 = 0
    rw [readLE_rtView (inPrivW (by decide) (by decide))]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 32) (BitVec (8 * 1)))
    (H : RtReady) (ret : Nat) (s : State) (m k : BitVec 64) (f : AMap (BitVec 32) (BitVec (8 * 1))),
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
