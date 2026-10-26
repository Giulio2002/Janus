import Janus.Contracts.MapSat

/-!
# The map contracts of `Janus.Contracts.MapVar` are satisfiable (arm64)

As `Janus.Contracts.MapSat`, for `makemap`, the generic entry points (8-byte keys of regular
memory: the witness map type `MapModel0.TY` has the key type `KT`, `KeyRegular`), the `_fat`
lookups, the `_fast32` ones and `mapassign_fast64ptr`: the models `MapModel0.ME` (read-only
entry points) and `MapModel0.MC` (assignments: `HAssign`, the map is empty; `makemap`:
`HMake`, no map is alive yet), 8-byte values, A64 code at `IfaceSat.A0`, and a call state with
the non-nil map `MP` that satisfies the contract's whole precondition.
-/

namespace Janus.Contracts.MapVarSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapModel0
  Janus.Contracts.IfaceSat Janus.Contracts.MapSat

/-! ## `makemap` (`MC`, no map alive) -/

theorem makeMap_impl : MakeMap (toy.link (at0 makeCode)) A0 (MC ck64) HMake := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, -, hH⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  obtain ⟨h0, hacc⟩ := hH
  rw [MC_priv, readLE_rtView0 (a := MP + 48) (n := 8) (by decide) (by decide)] at h0
  rw [rtView_accessible] at hacc
  simp only [MP] at hacc
  janus_run
  have hfr : MemFrame s.mem ((s.mem.writeLE 67632 8 1).writeLE 67584 8 0) (rtWrites (MC ck64) s 3 ++ []) := by
    simp only [rtWrites, calleeStack, MC_priv, MC_depth, priv0, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67632 : Nat) = MP + 48 from rfl] at hacc hfr ⊢
  refine mapReturn_of (MC ck64) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl hfr ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ _ h => absurd h (MC_none ck64 h0 _ _)) ⟨?_, ?_, fun mp f h => absurd h (MC_none ck64 h0 _ _)⟩
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]; decide
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact MC_rep_new ck64 (by rw [Memory.accessible_writeLE, Memory.accessible_writeLE]; exact hacc)
      (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_self])
      (by rw [Memory.readLE_writeLE_self])

/-- `MakeMap` is satisfiable: the model `MC ck64`, `H = HMake`, a call `makemap(TY, hint, nil)`
with no map alive. -/
theorem makeMap_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Segment) (H : RtReady),
    M.Laws ∧ MakeMap (toy.link impl) A0 M H ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 2).toNat = 0 ∧
        Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, 0] s) :=
  ⟨MC ck64, _, HMake, MC_laws _, makeMap_impl, mstate mmemDead (args 0 0), rfl,
    mstate_rtpre _ rfl rfl mmemDead rfl _ 3 (by decide)
      (show ZEnv mmemDead from mmem_zenv.writeLE _ (by decide)) mmemDead_guard, trivial, by decide,
    hMake_dead _ _ _⟩

/-! ## Generic and `_fast32` lookups, deletes (`ME`) -/

/-- The zero slot read back as `SlotHoldsN … 8 0`. -/
theorem zs_holds {K : Type} {m : Memory} (hze : ZEnv m) : SlotHoldsN (ME K) m ZS 8 0 :=
  ⟨hze.1, inPriv0 (by decide) (by decide), hze.2⟩

theorem access1G_impl : Access1G (toy.link (at0 zsCode)) A0 8 8 (ME (BitVec (8 * 8))) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, -, hmap, -⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  exact mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, zs_holds hze⟩

/-- The arguments of a generic lookup: `t = TY`, `m = MP`, the key bytes at `VAL`. -/
def gargs : Nat → W64 := args (BitVec.ofNat 64 IfaceModel.VAL) (BitVec.ofNat 64 ZS)

theorem keyIn_g (n : Nat) : KeyIn (mstate mmem gargs) 64 n IfaceModel.VAL 8 := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [calleeStack, outside_cons, outside_nil, and_true]
  show _ ∧ _
  constructor <;> simp [mstate, IfaceModel.wsp, IfaceModel.VAL] <;> omega

/-- `Access1G` is satisfiable: a lookup of the 8 key bytes at `VAL` (key type `KT`, regular
memory) in a non-nil map. -/
theorem access1G_satisfiable : ∃ (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs)))
    (impl : List Segment), M.Laws ∧ Access1G (toy.link impl) A0 n vs M ∧
      ∃ (f : AMap (BitVec (8 * n)) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (s.regs 1).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
        IsMap M s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 3 (s.regs 2).toNat n) :=
  ⟨8, 8, ME _, _, ME_laws _, access1G_impl, AMap.empty, mstate mmem gargs, rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial, keyRegular_mmem,
    (isMap_of_ne (by decide)).2 (mmem_rep _), keyIn_g 3⟩

theorem access2G_impl : Access2G (toy.link (at0 zsCode)) A0 8 8 (ME (BitVec (8 * 8))) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, -, hmap, -⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  exact mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h)
    ⟨hmap, zs_holds hze, by simp [setReg, AMap.empty]⟩

/-- `Access2G` is satisfiable (as `access1G_satisfiable`). -/
theorem access2G_satisfiable : ∃ (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs)))
    (impl : List Segment), M.Laws ∧ Access2G (toy.link impl) A0 n vs M ∧
      ∃ (f : AMap (BitVec (8 * n)) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (s.regs 1).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
        IsMap M s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 3 (s.regs 2).toNat n) :=
  ⟨8, 8, ME _, _, ME_laws _, access2G_impl, AMap.empty, mstate mmem gargs, rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial, keyRegular_mmem,
    (isMap_of_ne (by decide)).2 (mmem_rep _), keyIn_g 3⟩

theorem deleteG_impl : DeleteG (toy.link (at0 retCode)) A0 8 8 (ME (BitVec (8 * 8))) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, -, hmap, -⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  refine mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ?_
  rw [erase_empty]; exact hmap

/-- `DeleteG` is satisfiable (as `access1G_satisfiable`). -/
theorem deleteG_satisfiable : ∃ (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs)))
    (impl : List Segment), M.Laws ∧ DeleteG (toy.link impl) A0 n vs M ∧
      ∃ (f : AMap (BitVec (8 * n)) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (s.regs 1).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
        IsMap M s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 3 (s.regs 2).toNat n) :=
  ⟨8, 8, ME _, _, ME_laws _, deleteG_impl, AMap.empty, mstate mmem gargs, rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial, keyRegular_mmem,
    (isMap_of_ne (by decide)).2 (mmem_rep _), keyIn_g 3⟩

/-! ## `_fat` lookups: the caller's zero value -/

/-- `mov x0, x3; mov x1, xzr; ret`: the caller's zero value and `false`. -/
def fatCode : List Nat := [0xaa0303e0, 0xaa1f03e1, 0xd65f03c0]

theorem access1Fat_impl : Access1Fat (toy.link (at0 fatCode)) A0 8 8 (ME (BitVec (8 * 8))) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, -, hmap, -⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  exact mapReturn_of (ME _) 4 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h)
    ⟨hmap, fun v h => by simp [AMap.empty] at h, fun _ => by simp [setReg]⟩

/-- `Access1Fat` is satisfiable (as `access1G_satisfiable`, the zero value `ZS`). -/
theorem access1Fat_satisfiable : ∃ (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs)))
    (impl : List Segment), M.Laws ∧ Access1Fat (toy.link impl) A0 n vs M ∧
      ∃ (f : AMap (BitVec (8 * n)) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (s.regs 1).toNat ≠ 0 ∧
      (RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
        IsMap M s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 4 (s.regs 2).toNat n) :=
  ⟨8, 8, ME _, _, ME_laws _, access1Fat_impl, AMap.empty, mstate mmem gargs, rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 4 (by decide) mmem_zenv mmem_guard, trivial, keyRegular_mmem,
    (isMap_of_ne (by decide)).2 (mmem_rep _), keyIn_g 4⟩

theorem access2Fat_impl : Access2Fat (toy.link (at0 fatCode)) A0 8 8 (ME (BitVec (8 * 8))) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, -, hmap, -⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  exact mapReturn_of (ME _) 4 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h)
    ⟨hmap, fun v h => by simp [AMap.empty] at h, fun _ => by simp [setReg], by simp [setReg, AMap.empty]⟩

/-- `Access2Fat` is satisfiable (as `access1Fat_satisfiable`). -/
theorem access2Fat_satisfiable : ∃ (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs)))
    (impl : List Segment), M.Laws ∧ Access2Fat (toy.link impl) A0 n vs M ∧
      ∃ (f : AMap (BitVec (8 * n)) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (s.regs 1).toNat ≠ 0 ∧
      (RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
        IsMap M s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 4 (s.regs 2).toNat n) :=
  ⟨8, 8, ME _, _, ME_laws _, access2Fat_impl, AMap.empty, mstate mmem gargs, rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 4 (by decide) mmem_zenv mmem_guard, trivial, keyRegular_mmem,
    (isMap_of_ne (by decide)).2 (mmem_rep _), keyIn_g 4⟩

/-! ## `_fast32` lookups and delete -/

theorem access1F32_impl : Access1F32 (toy.link (at0 zsCode)) A0 8 (ME (BitVec 32)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  exact mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, zs_holds hze⟩

/-- `Access1F32` is satisfiable: a lookup of the key `7` in a non-nil map. -/
theorem access1F32_satisfiable : ∃ (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs)))
    (impl : List Segment), M.Laws ∧ Access1F32 (toy.link impl) A0 vs M ∧
      ∃ (f : AMap (BitVec 32) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (s.regs 1).toNat ≠ 0 ∧ (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f) :=
  ⟨8, ME _, _, ME_laws _, access1F32_impl, AMap.empty, mstate mmem (args 7#64 0), rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _)⟩

theorem access2F32_impl : Access2F32 (toy.link (at0 zsCode)) A0 8 (ME (BitVec 32)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  exact mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h)
    ⟨hmap, zs_holds hze, by simp [setReg, AMap.empty]⟩

/-- `Access2F32` is satisfiable (as `access1F32_satisfiable`). -/
theorem access2F32_satisfiable : ∃ (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs)))
    (impl : List Segment), M.Laws ∧ Access2F32 (toy.link impl) A0 vs M ∧
      ∃ (f : AMap (BitVec 32) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (s.regs 1).toNat ≠ 0 ∧ (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f) :=
  ⟨8, ME _, _, ME_laws _, access2F32_impl, AMap.empty, mstate mmem (args 7#64 0), rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _)⟩

theorem deleteF32_impl : DeleteF32 (toy.link (at0 retCode)) A0 8 (ME (BitVec 32)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  refine mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ?_
  rw [erase_empty]; exact hmap

/-- `DeleteF32` is satisfiable (as `access1F32_satisfiable`). -/
theorem deleteF32_satisfiable : ∃ (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs)))
    (impl : List Segment), M.Laws ∧ DeleteF32 (toy.link impl) A0 vs M ∧
      ∃ (f : AMap (BitVec 32) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (s.regs 1).toNat ≠ 0 ∧ (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f) :=
  ⟨8, ME _, _, ME_laws _, deleteF32_impl, AMap.empty, mstate mmem (args 7#64 0), rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _)⟩

/-! ## Assignments (`MC`, the map empty) -/

/-- The precondition facts every `MC` assignment uses: the map at `MP` is empty, alive and
writable. -/
theorem mc_empty {K : Type} [DecidableEq K] {ck : CellKey K} {s : State} {f : AMap K (BitVec 64)}
    (hrep : (MC ck).Rep s.mem (s.regs 1).toNat f) (args : List Nat)
    (hH : Ready HAssign (MC ck).priv args s) :
    (s.regs 1).toNat = MP ∧ s.mem.accessible MP 56 true = true ∧ s.mem.readLE (MP + 48) 8 = 1 ∧
      f = AMap.empty := by
  obtain ⟨hmp, hacc, hal, hu⟩ := hrep
  have h0 : s.mem.readLE MP 8 = 0 := by
    have := hH; simp only [Ready, HAssign, MC_priv] at this
    rwa [readLE_rtView0 (a := MP) (n := 8) (by decide) (by decide)] at this
  refine ⟨hmp, hacc, hal, ?_⟩
  rcases hu with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · omega

theorem assign64Ptr_impl : Assign64Ptr (toy.link (at0 assignCode)) A0 8 (MC ck64) HAssign := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hm0, hrep, hH⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  obtain ⟨hmp, hacc, hal, rfl⟩ := mc_empty hrep _ hH
  simp only [MP] at hacc
  janus_run
  have hfr : MemFrame s.mem ((s.mem.writeLE 67584 8 1).writeLE 67592 8 (BitVec.toNat (s.regs 2)))
      (rtWrites (MC ck64) s 3 ++ []) := by
    simp only [rtWrites, calleeStack, MC_priv, MC_depth, priv0, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  have hm1 : (s.mem.writeLE MP 8 1).accessible MP 56 true = true := by
    rw [Memory.accessible_writeLE]; exact hacc
  refine mapReturn_of (MC ck64) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl hfr ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  exact cell_assign ck64 _ (s.regs 2) (s.regs 28) (by rw [Memory.accessible_writeLE]; exact hm1)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_self])
    (fun v => by
      show BitVec.ofNat 64 (Memory.readLE _ (MP + 8) 8) = _
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (s.regs 2).isLt]
      simp)
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))

/-- `Assign64Ptr` is satisfiable: `MC ck64`, `H = HAssign`, an assignment to the empty non-nil
map. -/
theorem assign64Ptr_satisfiable : ∃ (vs : Nat) (M : MapModel (BitVec 64) (BitVec (8 * vs)))
    (impl : List Segment) (H : RtReady), M.Laws ∧ Assign64Ptr (toy.link impl) A0 vs M H ∧
      ∃ (f : AMap (BitVec 64) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
        M.Rep s.mem (s.regs 1).toNat f ∧
        Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s) :=
  ⟨8, MC ck64, _, HAssign, MC_laws _, assign64Ptr_impl, AMap.empty,
    mstate mmem (args (BitVec.ofNat 64 IfaceModel.VAL) 0), rfl,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial, by decide,
    mmem_repC _, hAssign_mmem _ _ _⟩

/-- `ldr x3, [x2]; movz x4, #0x800; movk x4, #1, lsl #16; movz x5, #1; str x5, [x4];
str x3, [x4, #8]; add x0, x4, #32; ret`: copy the 8 key bytes into the cell. -/
def assignGCode : List Nat :=
  [0xf9400043, 0xd2810004, 0xf2a00024, 0xd2800025, 0xf9000085, 0xf9000483, 0x91008080, 0xd65f03c0]

theorem assignG_impl : AssignG (toy.link (at0 assignGCode)) A0 8 8 (MC ck64) HAssign := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, -, hm0, hrep, ⟨hk1, hk2, hk3⟩, hH⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  obtain ⟨hmp, hacc, hal, rfl⟩ := mc_empty hrep _ hH
  simp only [MP] at hacc
  janus_run
  have hfr : MemFrame s.mem ((s.mem.writeLE 67584 8 1).writeLE 67592 8
      (s.mem.readLE (BitVec.toNat (s.regs 2)) 8)) (rtWrites (MC ck64) s 3 ++ []) := by
    simp only [rtWrites, calleeStack, MC_priv, MC_depth, priv0, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  have hm1 : (s.mem.writeLE MP 8 1).accessible MP 56 true = true := by
    rw [Memory.accessible_writeLE]; exact hacc
  refine mapReturn_of (MC ck64) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl hfr ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  exact cell_assign ck64 _ _ (s.regs 28) (by rw [Memory.accessible_writeLE]; exact hm1)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_self])
    (fun v => by
      show BitVec.ofNat 64 (Memory.readLE _ (MP + 8) 8) = _
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)]
      rfl)
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))

/-- `AssignG` is satisfiable: `MC ck64`, `H = HAssign`, an assignment of the 8 key bytes at `VAL`
(key type `KT`) to the empty non-nil map. -/
theorem assignG_satisfiable : ∃ (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs)))
    (impl : List Segment) (H : RtReady), M.Laws ∧ AssignG (toy.link impl) A0 n vs M H ∧
      ∃ (f : AMap (BitVec (8 * n)) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
        (s.regs 1).toNat ≠ 0 ∧ M.Rep s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 3 (s.regs 2).toNat n ∧
        Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat,
          s.mem.readLE (s.regs 2).toNat n] s) :=
  ⟨8, 8, MC ck64, _, HAssign, MC_laws _, assignG_impl, AMap.empty, mstate mmem gargs, rfl,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial, keyRegular_mmem,
    by decide, mmem_repC _, keyIn_g 3, hAssign_mmem _ _ _⟩

/-- `movz x4, #0x800; movk x4, #1, lsl #16; movz x5, #1; str x5, [x4]; str w2, [x4, #8];
add x0, x4, #32; ret`: the 4-byte key into the cell. -/
def assignF32Code : List Nat :=
  [0xd2810004, 0xf2a00024, 0xd2800025, 0xf9000085, 0xb9000882, 0x91008080, 0xd65f03c0]

theorem assignF32_impl : AssignF32 (toy.link (at0 assignF32Code)) A0 8 (MC ck32) HAssign := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hm0, hrep, hH⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  obtain ⟨hmp, hacc, hal, rfl⟩ := mc_empty hrep _ hH
  simp only [MP] at hacc
  janus_run
  have hfr : MemFrame s.mem ((s.mem.writeLE 67584 8 1).writeLE 67592 4 (BitVec.toNat (s.regs 2)))
      (rtWrites (MC ck32) s 3 ++ []) := by
    simp only [rtWrites, calleeStack, MC_priv, MC_depth, priv0, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  have hm1 : (s.mem.writeLE MP 8 1).accessible MP 56 true = true := by
    rw [Memory.accessible_writeLE]; exact hacc
  refine mapReturn_of (MC ck32) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl hfr ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  exact cell_assign ck32 _ _ (s.regs 28) (by rw [Memory.accessible_writeLE]; exact hm1)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_self])
    (fun v => by
      show BitVec.ofNat 32 (Memory.readLE _ (MP + 8) 4) = _
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_self]
      apply BitVec.eq_of_toNat_eq
      simp [key32, BitVec.toNat_setWidth])
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))

/-- `AssignF32` is satisfiable: `MC ck32`, `H = HAssign`, an assignment of the key `7` to the
empty non-nil map. -/
theorem assignF32_satisfiable : ∃ (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs)))
    (impl : List Segment) (H : RtReady), M.Laws ∧ AssignF32 (toy.link impl) A0 vs M H ∧
      ∃ (f : AMap (BitVec 32) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
        M.Rep s.mem (s.regs 1).toNat f ∧
        Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, (key32 s).toNat] s) :=
  ⟨8, MC ck32, _, HAssign, MC_laws _, assignF32_impl, AMap.empty, mstate mmem (args 7#64 0), rfl,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial, by decide,
    mmem_repC _, hAssign_mmem _ _ _⟩

end Janus.Contracts.MapVarSat
