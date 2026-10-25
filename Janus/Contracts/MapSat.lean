import Janus.Contracts.MapModel0
import Janus.Contracts.IfaceSat

/-!
# The map contracts of `Janus.Contracts.Map` are satisfiable (arm64)

For every contract of `Janus.Contracts.Map`: a model (`MapModel0.ME`, one empty non-nil map, for
the read-only entry points; `MapModel0.MC`, one map of at most one entry, for `mapassign` and
`makemap_small`), A64 machine code at `IfaceSat.A0` (bytes from GNU `as`) proved by symbolic
execution to meet the contract for the model, the readiness predicate `H` where the contract
takes one (`MapModel0.HAssign`: the map is empty; `MapModel0.HMake`: no map is alive yet), and
a call state satisfying the contract's whole precondition, with a **non-nil** map where the
contract is about one (`<contract>_satisfiable`; `audit/round9/sat_check.py`, row SAT).
-/

namespace Janus.Contracts.MapSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapModel0
  Janus.Contracts.IfaceSat
open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write)

/-! ## The witness call state -/

/-- The return of a model implementation as `Map.RTReturn` (arm64). -/
theorem mapReturn_of {K V : Type} (M : MapModel K V) (nargs : Nat) (extra : List (Nat × Nat))
    (except : Nat) (s s' : State) (P : (Nat → W64) → Memory → Prop) (hsp : s'.sp = s.sp)
    (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28)
    (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid) (htp : s'.tpidr = s.tpidr)
    (hfc : s'.fpcr = s.fpcr) (hfs : s'.fpsr = s.fpsr)
    (hfr : MemFrame s.mem s'.mem (Map.rtWrites M s nargs ++ extra)) (henv : M.Env s'.mem (s.regs 28))
    (hok : Map.OthersKept M s.mem s'.mem except) (hp : P s'.regs s'.mem)
    (hex : s'.excl = s.excl := by first | rfl | simp_all) (hep : s'.exclPass = s.exclPass := by first | rfl | simp_all) :
    Map.RTReturn M nargs extra except s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.mem, ?_, hfr, henv, hok, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs, ex, ep⟩ := s'
  simp only at hsp hpc hdz htp hfc hfs h18 h28 h29 hex hep ⊢
  subst hsp hpc hdz htp hfc hfs hex hep
  congr
  funext i
  simp only [Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

/-- The witness call state: the arguments `r`, goroutine `wg`, return address `wret`, stack
pointer `wsp`, memory `m`. -/
def mstate (m : Memory) (r : Nat → W64) : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else r i,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := m }

/-- `RTPre` at the witness state, for any model with the private memory `priv0`, 64 bytes of
stack and an environment that holds there. -/
theorem mstate_rtpre {K V : Type} (M : MapModel K V) (hp : M.priv = priv0) (hd : M.depth = 64)
    (m : Memory) (hreg : m.regions = IfaceModel.wmem.regions) (r : Nat → W64) (n : Nat) (hn : n ≤ 4)
    (he : M.Env m (BitVec.ofNat 64 wg)) (hg : m.readLE (wg + 16) 8 = 0) : RTPre M n (mstate m r) := by
  have hacc : ∀ a k w, m.accessible a k w = IfaceModel.wmem.accessible a k w := by
    intro a k w; unfold Memory.accessible; rw [hreg]
  have hw : IfaceModel.wmem.accessible (wsp - 64) (64 + 8 + 8 * 4) true = true := by decide
  have h28 : (mstate m r).regs 28 = BitVec.ofNat 64 wg := rfl
  have h30 : (mstate m r).regs 30 = BitVec.ofNat 64 wret := rfl
  have hsp : (mstate m r).sp = BitVec.ofNat 64 wsp := rfl
  have hm : (mstate m r).mem = m := rfl
  refine ⟨by rw [h28, hm]; exact he, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, by rw [hd]; decide, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, h28]; decide
  · simp only [regG, stackguard0Offset, h28, hm, hacc]; decide
  · simp only [stackguard0, regG, stackguard0Offset, h28, hm, hsp, hd]
    rw [show (BitVec.ofNat 64 wg).toNat = wg from rfl, hg]; decide
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [hsp]; decide
  · simp only [hsp, hd]; decide
  · simp only [hsp]; simp [wsp]; omega
  · simp only [hsp, hm, hd, BitVec.toNat_ofNat, hacc]
    exact Memory.accessible_mono _ hw (by simp [wsp]) (by simp [wsp]; omega)
  · simp only [hsp, hd, hp, priv0, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [wsp]

/-- The witness memories' stack guard word is `0`, their regions `IfaceModel.wmem`'s. -/
theorem mmem_guard : mmem.readLE (wg + 16) 8 = 0 := by decide
theorem mmemDead_guard : mmemDead.readLE (wg + 16) 8 = 0 := by
  unfold mmemDead; rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; decide
theorem mmemDead_regions : mmemDead.regions = IfaceModel.wmem.regions := rfl

/-- The arguments `t = TY`, `m = MP`, then `a2`, `a3`. -/
def args (a2 a3 : W64) : Nat → W64 :=
  fun i => if i = 0 then BitVec.ofNat 64 TY else if i = 1 then BitVec.ofNat 64 MP
    else if i = 2 then a2 else if i = 3 then a3 else 0

/-! ## Lookups: return the zero slot and `false` (`ME`) -/

/-- `movz x0, #0x900; movk x0, #1, lsl #16; mov x1, xzr; ret`: `ZS` and `false`. -/
def zsCode : List Nat := [0xd2812000, 0xf2a00020, 0xaa1f03e1, 0xd65f03c0]

theorem access1_impl : Access1 (toy.link (at0 zsCode)) A0 (ME (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  refine mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, ?_⟩
  simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
  exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩

/-- `Access1` is satisfiable, for a lookup in a non-nil map. -/
theorem access1_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Segment),
    M.Laws ∧ Access1 (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State),
      s.pc = BitVec.ofNat 64 A0 ∧ (s.regs 1).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f) :=
  ⟨ME _, _, ME_laws _, access1_impl, AMap.empty, mstate mmem (args 7#64 0), rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _)⟩

/-! ## Assignment (`MC`, the map empty) -/

/-- `movz x4, #0x800; movk x4, #1, lsl #16; movz x5, #1; str x5, [x4]; str x2, [x4, #8];
add x0, x4, #32; ret`: `used = 1`, the key, and the value slot `MP + 32`. -/
def assignCode : List Nat :=
  [0xd2810004, 0xf2a00024, 0xd2800025, 0xf9000085, 0xf9000482, 0x91008080, 0xd65f03c0]

theorem assign_impl : Assign (toy.link (at0 assignCode)) A0 (MC ck64) HAssign := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hm0, hrep, hH⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  obtain ⟨hmp, hacc, hal, hu⟩ := hrep
  have h0 : s.mem.readLE MP 8 = 0 := by
    have := hH; simp only [Ready, HAssign, MC_priv] at this
    rwa [readLE_rtView0 (a := MP) (n := 8) (by decide) (by decide)] at this
  have hf : f = AMap.empty := by
    rcases hu with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · omega
  subst hf
  simp only [MP] at hacc
  janus_run
  have hfr : MemFrame s.mem ((s.mem.writeLE 67584 8 1).writeLE 67592 8 (BitVec.toNat (s.regs 2)))
      (rtWrites (MC ck64) s 3 ++ []) := by
    simp only [rtWrites, calleeStack, MC_priv, MC_depth, priv0, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67616 : Nat) = MP + 32 from rfl] at hacc ⊢
  have hm1 : (s.mem.writeLE MP 8 1).accessible MP 56 true = true := by
    rw [Memory.accessible_writeLE]; exact hacc
  refine mapReturn_of (MC ck64) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl hfr ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
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

/-- `Assign` is satisfiable: the model `MC ck64`, `H = HAssign`, and an assignment to the empty
non-nil map. -/
theorem assign_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Segment) (H : RtReady),
    M.Laws ∧ Assign (toy.link impl) A0 M H ∧ ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State),
      s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧ M.Rep s.mem (s.regs 1).toNat f ∧
        Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s) :=
  ⟨MC ck64, _, HAssign, MC_laws _, assign_impl, AMap.empty, mstate mmem (args 7#64 0), rfl,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial, by decide,
    mmem_repC _, hAssign_mmem _ _ _⟩

/-! ## `makemap_small` (`MC`, no map alive) -/

/-- `movz x0, #0x800; movk x0, #1, lsl #16; movz x5, #1; str x5, [x0, #48]; str xzr, [x0];
ret`: the map at `MP`, alive and empty. -/
def makeCode : List Nat := [0xd2810000, 0xf2a00020, 0xd2800025, 0xf9001805, 0xf900001f, 0xd65f03c0]

theorem makeSmall_impl : MakeSmall (toy.link (at0 makeCode)) A0 (MC ck64) HMake := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, hH⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  obtain ⟨h0, hacc⟩ := hH
  rw [MC_priv, readLE_rtView0 (a := MP + 48) (n := 8) (by decide) (by decide)] at h0
  rw [rtView_accessible] at hacc
  simp only [MP] at hacc
  janus_run
  have hfr : MemFrame s.mem ((s.mem.writeLE 67632 8 1).writeLE 67584 8 0) (rtWrites (MC ck64) s 0 ++ []) := by
    simp only [rtWrites, calleeStack, MC_priv, MC_depth, priv0, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67632 : Nat) = MP + 48 from rfl] at hacc hfr ⊢
  refine mapReturn_of (MC ck64) 0 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl hfr ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ _ h => absurd h (MC_none ck64 h0 _ _)) ⟨?_, ?_, fun mp f h => absurd h (MC_none ck64 h0 _ _)⟩
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]; decide
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact MC_rep_new ck64 (by rw [Memory.accessible_writeLE, Memory.accessible_writeLE]; exact hacc)
      (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_self])
      (by rw [Memory.readLE_writeLE_self])

/-- `MakeSmall` is satisfiable: the model `MC ck64`, `H = HMake`, and a call with no map alive. -/
theorem makeSmall_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Segment) (H : RtReady),
    M.Laws ∧ MakeSmall (toy.link impl) A0 M H ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre M 0 s ∧ Ready H M.priv [] s) :=
  ⟨MC ck64, _, HMake, MC_laws _, makeSmall_impl, mstate mmemDead (args 0 0), rfl,
    mstate_rtpre _ rfl rfl mmemDead rfl _ 0 (by decide)
      (show ZEnv mmemDead from mmem_zenv.writeLE _ (by decide)) mmemDead_guard, hMake_dead _ _ _⟩

theorem access2_impl : Access2 (toy.link (at0 zsCode)) A0 (ME (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  refine mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, ?_, ?_⟩
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩
  · simp [setReg, AMap.empty]

/-- `Access2` is satisfiable, for a lookup in a non-nil map. -/
theorem access2_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Segment),
    M.Laws ∧ Access2 (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State),
      s.pc = BitVec.ofNat 64 A0 ∧ (s.regs 1).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f) :=
  ⟨ME _, _, ME_laws _, access2_impl, AMap.empty, mstate mmem (args 7#64 0), rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _)⟩

/-- `movz x0, #0x900; movk x0, #1, lsl #16; mov x1, xzr; ret` for `[16]byte` keys. -/
theorem access2Ptr_impl : Access2Ptr (toy.link (at0 zsCode)) A0 (ME (BitVec 128)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap, -⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  refine mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, ?_, ?_⟩
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩
  · simp [setReg, AMap.empty]

/-- `Access2Ptr` is satisfiable: a lookup of the 16 bytes at `VAL` in a non-nil map. -/
theorem access2Ptr_satisfiable : ∃ (M : MapModel (BitVec 128) (BitVec 64)) (impl : List Segment),
    M.Laws ∧ Access2Ptr (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 128) (BitVec 64)) (s : State),
      s.pc = BitVec.ofNat 64 A0 ∧ (s.regs 1).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f ∧
        s.mem.accessible (s.regs 2).toNat 16 false = true ∧
        Outside (s.regs 2).toNat 16 (calleeStack s M.depth 3)) :=
  ⟨ME _, _, ME_laws _, access2Ptr_impl, AMap.empty,
    mstate mmem (args (BitVec.ofNat 64 IfaceModel.VAL) 0), rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _), by decide,
    by simp only [calleeStack, ME_depth, outside_cons, outside_nil, and_true]; decide⟩

/-! ## `delete` and `clear` of the empty map: `ret` -/

/-- `ret`. -/
def retCode : List Nat := [0xd65f03c0]

theorem delete_impl : Delete (toy.link (at0 retCode)) A0 (ME (BitVec 64)) := by
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

/-- `Delete` is satisfiable, for a delete in a non-nil map. -/
theorem delete_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Segment),
    M.Laws ∧ Delete (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State),
      s.pc = BitVec.ofNat 64 A0 ∧ (s.regs 1).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f) :=
  ⟨ME _, _, ME_laws _, delete_impl, AMap.empty, mstate mmem (args 7#64 0), rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _)⟩

theorem clear_impl : Clear (toy.link (at0 retCode)) A0 (ME (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  exact mapReturn_of (ME _) 2 [] _ s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) hmap

/-- `Clear` is satisfiable, for a non-nil map. -/
theorem clear_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Segment),
    M.Laws ∧ Clear (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State),
      s.pc = BitVec.ofNat 64 A0 ∧ (s.regs 1).toNat ≠ 0 ∧
      (RTPre M 2 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f) :=
  ⟨ME _, _, ME_laws _, clear_impl, AMap.empty, mstate mmem (args 0 0), rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 2 (by decide) mmem_zenv mmem_guard, trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _)⟩

/-! ## Iteration over the empty map: store the end of the iteration -/

/-- `str xzr, [x2]; ret`: the key pointer of the iterator is `0`. -/
def iterStartCode : List Nat := [0xf900005f, 0xd65f03c0]

theorem iterStart_impl : IterStart (toy.link (at0 iterStartCode)) A0 (ME (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap, hit, hip, hic⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  have hip8 : Outside (s.regs 2).toNat 8 (ME (BitVec 64)).priv := Outside.of_sub hip (by omega) (by simp [iterSize])
  have hw : s.mem.accessible (s.regs 2).toNat 8 true = true :=
    Memory.accessible_mono _ hit (Nat.le_refl _) (by simp [iterSize])
  janus_run
  have ha := agrees_writeLE s.mem 0 hip8
  refine mapReturn_of (ME _) 3 _ _ s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_
    (ZEnv.frame hze ha) (fun _ _ _ h => (ME_laws _).rep_frame _ _ _ _ h ha) ⟨ME_isMap_frame hmap ha,
      [], keys_empty, Nat.zero_le _, ?_⟩
  · simp only [rtWrites, List.append_assoc]
    exact (MemFrame.refl _ _).writeLE_inRanges _
      ⟨((s.regs 2).toNat, (s.regs 2).toNat + iterSize), by simp, Nat.le_refl _, by simp [iterSize]⟩
  · show (s.mem.writeLE (s.regs 2).toNat 8 _).readLE (s.regs 2).toNat 8 = 0
    rw [Memory.readLE_writeLE_self]

/-- `IterStart` is satisfiable: an iteration over a non-nil (empty) map with the iterator `IT`. -/
theorem iterStart_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Segment),
    M.Laws ∧ IterStart (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State),
      s.pc = BitVec.ofNat 64 A0 ∧ (s.regs 1).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f ∧
        s.mem.accessible (s.regs 2).toNat iterSize true = true ∧
        Outside (s.regs 2).toNat iterSize M.priv ∧
        Outside (s.regs 2).toNat iterSize (calleeStack s M.depth 3)) :=
  ⟨ME _, _, ME_laws _, iterStart_impl, AMap.empty, mstate mmem (args (BitVec.ofNat 64 IT) 0), rfl,
    by decide, mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard, trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _), by decide,
    by simp only [ME_priv, priv0, outside_cons, outside_nil, and_true]; decide,
    by simp only [calleeStack, ME_depth, outside_cons, outside_nil, and_true]; decide⟩

/-- `ME` with iterators that have at most one key left and a writable iterator struct (`IterNext`
stores into it, and its precondition says nothing else about the struct). -/
def MEI (K : Type) : MapModel K (BitVec 64) :=
  { ME K with Iter := fun m it _ _ ks => ks.length ≤ 1 ∧ m.accessible it iterSize true = true }

@[simp] theorem MEI_priv (K : Type) : (MEI K).priv = priv0 := rfl
@[simp] theorem MEI_depth (K : Type) : (MEI K).depth = 64 := rfl

theorem MEI_laws (K : Type) : (MEI K).Laws where
  rep_frame := (ME_laws K).rep_frame
  iter_frame _ _ _ _ _ _ h ha := ⟨h.1, by rw [ha.accessible]; exact h.2⟩
  env_frame := (ME_laws K).env_frame
  len := (ME_laws K).len
  finite := (ME_laws K).finite

/-- `str xzr, [x0]; ret`: the iteration is over. -/
def iterNextCode : List Nat := [0xf900001f, 0xd65f03c0]

theorem iterNext_impl : IterNext (toy.link (at0 iterNextCode)) A0 (MEI (BitVec 64)) := by
  rw [link_at0]
  intro mp f k ks s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, hmap, ⟨hlen, hit⟩, hip, hic⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hks : ks = [] := by cases ks <;> simp_all
  subst hks
  have hip8 : Outside (s.regs 0).toNat 8 (MEI (BitVec 64)).priv := Outside.of_sub hip (by omega) (by simp [iterSize])
  have hw : s.mem.accessible (s.regs 0).toNat 8 true = true :=
    Memory.accessible_mono _ hit (Nat.le_refl _) (by simp [iterSize])
  janus_run
  have ha := agrees_writeLE s.mem 0 hip8
  refine mapReturn_of (MEI _) 1 _ _ s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_
    (ZEnv.frame hze ha) (fun _ _ _ h => (MEI_laws _).rep_frame _ _ _ _ h ha)
    ⟨IsMap.frame (MEI_laws _) hmap ha, ⟨Nat.zero_le _, by rw [Memory.accessible_writeLE]; exact hit⟩, ?_⟩
  · simp only [rtWrites, List.append_assoc]
    exact (MemFrame.refl _ _).writeLE_inRanges _
      ⟨((s.regs 0).toNat, (s.regs 0).toNat + iterSize), by simp, Nat.le_refl _, by simp [iterSize]⟩
  · show (s.mem.writeLE (s.regs 0).toNat 8 _).readLE (s.regs 0).toNat 8 = 0
    rw [Memory.readLE_writeLE_self]

/-- `IterNext` is satisfiable: the last step of an iteration (one key left) over the non-nil map,
with the iterator `IT`. -/
theorem iterNext_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Segment),
    M.Laws ∧ IterNext (toy.link impl) A0 M ∧ ∃ (mp : Nat) (f : AMap (BitVec 64) (BitVec 64))
      (k : BitVec 64) (ks : List (BitVec 64)) (s : State), s.pc = BitVec.ofNat 64 A0 ∧ mp ≠ 0 ∧
      (RTPre M 1 s ∧ IsMap M s.mem mp f ∧ M.Iter s.mem (s.regs 0).toNat mp f (k :: ks) ∧
        Outside (s.regs 0).toNat iterSize M.priv ∧
        Outside (s.regs 0).toNat iterSize (calleeStack s M.depth 1)) :=
  ⟨MEI _, _, MEI_laws _, iterNext_impl, MP, AMap.empty, 7#64, [],
    mstate mmem (fun i => if i = 0 then BitVec.ofNat 64 IT else 0), rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 1 (by decide) mmem_zenv mmem_guard,
    (isMap_of_ne (by decide)).2 (mmem_rep _), ⟨by decide, by decide⟩,
    by simp only [MEI_priv, priv0, outside_cons, outside_nil, and_true]; decide,
    by simp only [calleeStack, MEI_depth, outside_cons, outside_nil, and_true]; decide⟩

end Janus.Contracts.MapSat
