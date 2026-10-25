import Janus.Contracts.MapModel0
import Janus.Contracts.MapStrSat

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
  refine MapStr.mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
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
  refine MapStr.mapReturn_of (MC ck64) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
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
  refine MapStr.mapReturn_of (MC ck64) 0 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
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

end Janus.Contracts.MapSat
