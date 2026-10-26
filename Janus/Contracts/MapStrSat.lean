import Janus.Contracts.MapStr
import Janus.Contracts.EqHashModel
import Janus.Contracts.IfaceSat
import Janus.Contracts.MapSat

/-!
# The string-keyed map contracts are satisfiable (arm64)

For every contract of `Janus.Contracts.MapStr`: a model of the map runtime, machine code at
`IfaceSat.A0` proved (by symbolic execution) to meet the contract for that model, and a call
state that satisfies the contract's whole precondition (`audit/round9/sat_check.py`, row SAT).
`Access2Str` uses the model `MS0` (every map is nil); the other contracts use the models of
`Janus.Contracts.MapModel0` (`ME`, one empty non-nil map; `MC ckStr`, one map of at most one
entry, whose key is the string whose header the code stores) with the witness state of
`Janus.Contracts.MapSat`.
-/



namespace Janus.Contracts.MapStr

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Map

/-- The zero slot of the model: 8 bytes of the model runtime's heap. -/
def ZS : Nat := 0x10f00

/-- The model: no non-nil map exists; the environment is a readable zero slot `ZS`. -/
def MS0 : MapModel (Nat × Nat) (BitVec 64) where
  Rep _ _ _ := False
  Iter _ _ _ _ _ := False
  Typ _ := True
  Env m _ := m.accessible ZS 8 false = true ∧ m.readLE ZS 8 = 0
  priv := [(0x10000, 0x11000)]
  depth := 64

theorem MS0_laws : MS0.Laws where
  rep_frame _ _ _ _ h _ := h.elim
  iter_frame _ _ _ _ _ _ h _ := h.elim
  env_frame m m' g h ha := by
    obtain ⟨h1, h2⟩ := h
    have hin : InRanges ZS 8 MS0.priv := ⟨(0x10000, 0x11000), by simp [MS0], by decide, by decide⟩
    exact ⟨by rw [ha.accessible]; exact h1, (ha.readLE hin).trans h2⟩
  len _ _ _ h := h.elim
  finite _ _ _ h := h.elim

/-- A map value of `MS0` is nil and empty. -/
theorem isMap_MS0 {m : Memory} {mp : Nat} {f : AMap (Nat × Nat) (BitVec 64)} (h : IsMap MS0 m mp f) :
    mp = 0 ∧ f = AMap.empty := by
  unfold IsMap at h
  split at h
  · exact ⟨by assumption, h⟩
  · exact h.elim

theorem env_wmem : MS0.Env EqHashModel.wmem 0 := ⟨by decide, by decide⟩

theorem env_wmem64 : MS0.Env EqHashModel.wmem64 0 := ⟨by decide, by decide⟩

end Janus.Contracts.MapStr

namespace Janus.Contracts.MapStr

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel

/-- The return of a model implementation as `Map.RTReturn` (arm64). -/
theorem mapReturn_of {K V : Type} (M : MapModel K V) (nargs : Nat) (extra : List (Nat × Nat))
    (except : Nat) (s s' : State) (P : (Nat → W64) → Memory → Prop) (hsp : s'.sp = s.sp)
    (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28)
    (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid) (htp : s'.tpidr = s.tpidr)
    (hfc : s'.fpcr = s.fpcr) (hfs : s'.fpsr = s.fpsr)
    (hfr : MemFrame s.mem s'.mem (Map.rtWrites M s nargs ++ extra)) (henv : M.Env s'.mem (s.regs 28))
    (hok : Map.OthersKept M s.mem s'.mem except) (hp : P s'.regs s'.mem)
    (hex : s'.excl = s.excl := by first | rfl | simp_all)
    (hep : s'.exclPass = s.exclPass := by first | rfl | simp_all) :
    Map.RTReturn M nargs extra except s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.mem, ?_, hfr, henv, hok, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs, ex, ep⟩ := s'
  simp only at hsp hpc hdz htp hfc hfs hex hep h18 h28 h29 ⊢
  subst hsp hpc hdz htp hfc hfs hex hep
  congr
  funext i
  simp only [Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

/-- `movz x0, #0xf00; movk x0, #1, lsl #16; mov x1, xzr; ret`: the zero slot and `false`. -/
def access2StrCode : List Nat := [0xd281e000, 0xf2a00020, 0xaa1f03e1, 0xd65f03c0]

theorem access2Str_impl : Access2Str (toy.link (at0 access2StrCode)) A0 MS0 := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨⟨he1, he2⟩, hg, hc, hout⟩, -, hmap, -⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  obtain ⟨hmp, rfl⟩ := isMap_MS0 hmap
  janus_run
  refine mapReturn_of MS0 4 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2⟩ (fun _ _ _ h => h) ⟨?_, ?_, ?_⟩
  · simp [IsMap, hmp]
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact ⟨he1, ⟨(0x10000, 0x11000), by simp [MS0], by decide, by decide⟩, by simpa [AMap.empty, ZS] using he2⟩
  · simp [setReg, AMap.empty]

/-- `Access2Str` is satisfiable. -/
theorem access2Str_satisfiable : ∃ (M : MapModel (Nat × Nat) (BitVec 64)) (impl : List Segment),
    M.Laws ∧ Access2Str (toy.link impl) A0 M ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (Map.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat AMap.empty ∧
        (s.regs 2).toNat + (s.regs 3).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 2).toNat (s.regs 3).toNat false = true ∧
        Outside (s.regs 2).toNat (s.regs 3).toNat (calleeStack s M.depth 4)) := by
  refine ⟨MS0, _, MS0_laws, access2Str_impl,
    { regs := fun i => if i = 2 then BitVec.ofNat 64 VAL else if i = 3 then 8#64
        else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else 0,
      sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
      mem := EqHashModel.wmem }, rfl, ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩, trivial,
      by simp [IsMap], by decide, by decide, ?_⟩⟩
  · simp only [MS0, outside_cons, outside_nil, and_true]; decide
  · simp only [calleeStack, MS0, outside_cons, outside_nil, and_true]; decide

end Janus.Contracts.MapStr


namespace Janus.Contracts.MapStrSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapStr
  Janus.Contracts.MapModel0 Janus.Contracts.IfaceSat Janus.Contracts.MapSat

/-- The arguments of a string lookup: `t = TY`, `m = MP`, the 8 bytes at `VAL`. -/
def sargs : Nat → W64 := args (BitVec.ofNat 64 IfaceModel.VAL) 8#64

theorem strIn_s : StrIn (mstate mmem sargs) 64 4 := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [calleeStack, outside_cons, outside_nil, and_true]
  constructor <;> simp [mstate, sargs, args, IfaceModel.wsp, IfaceModel.VAL]

theorem zs_holdsS {m : Memory} (hze : ZEnv m) : SlotHoldsN (ME (Nat × Nat)) m MapModel0.ZS 8 0 :=
  ⟨hze.1, inPriv0 (by decide) (by decide), hze.2⟩

/-- `movz x0, #0x900; movk x0, #1, lsl #16; mov x1, xzr; ret` (`MapSat.zsCode`): `ZS`. -/
theorem access1Str_impl : Access1Str (toy.link (at0 zsCode)) A0 8 (ME (Nat × Nat)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap, -⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  exact MapSat.mapReturn_of (ME _) 4 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, zs_holdsS hze⟩

/-- `Access1Str` is satisfiable: a lookup of the 8-byte string at `VAL` in a non-nil map. -/
theorem access1Str_satisfiable : ∃ (vs : Nat) (M : MapModel (Nat × Nat) (BitVec (8 * vs)))
    (impl : List Segment), M.Laws ∧ Access1Str (toy.link impl) A0 vs M ∧
      ∃ (f : AMap (Nat × Nat) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (s.regs 1).toNat ≠ 0 ∧
      (Map.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f ∧
        StrIn s M.depth 4) :=
  ⟨8, ME _, _, ME_laws _, access1Str_impl, AMap.empty, mstate mmem sargs, rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 4 (by decide) mmem_zenv mmem_guard, trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _), strIn_s⟩

/-- `ret` (`MapSat.retCode`). -/
theorem deleteStr_impl : DeleteStr (toy.link (at0 retCode)) A0 8 (ME (Nat × Nat)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap, -⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty hmap
  subst hf
  janus_run
  refine MapSat.mapReturn_of (ME _) 4 [] _ s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _)
    hze (fun _ _ _ h => h) ?_
  rw [erase_empty]; exact hmap

/-- `DeleteStr` is satisfiable (as `access1Str_satisfiable`). -/
theorem deleteStr_satisfiable : ∃ (vs : Nat) (M : MapModel (Nat × Nat) (BitVec (8 * vs)))
    (impl : List Segment), M.Laws ∧ DeleteStr (toy.link impl) A0 vs M ∧
      ∃ (f : AMap (Nat × Nat) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (s.regs 1).toNat ≠ 0 ∧
      (Map.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f ∧
        StrIn s M.depth 4) :=
  ⟨8, ME _, _, ME_laws _, deleteStr_impl, AMap.empty, mstate mmem sargs, rfl, by decide,
    mstate_rtpre _ rfl rfl mmem rfl _ 4 (by decide) mmem_zenv mmem_guard, trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _), strIn_s⟩

/-! ## `mapassign_faststr` (`MC ckStr`) -/

/-- The readiness of a string assignment in `MC ckStr`: the map is empty, and the key's bytes
(arguments 2 and 3: pointer and length) do not overlap the map's header, which the code writes. -/
def HAssignS : RtReady := fun args _ _ v =>
  v.readLE MP 8 = 0 ∧
    (args.getD 3 0 = 0 ∨ args.getD 2 0 + args.getD 3 0 ≤ MP ∨ MP + 56 ≤ args.getD 2 0)

/-- `movz x4, #0x800; movk x4, #1, lsl #16; movz x5, #1; str x5, [x4]; str x2, [x4, #8];
str x3, [x4, #16]; add x0, x4, #32; ret`: the key's header into the cell. -/
def assignStrCode : List Nat :=
  [0xd2810004, 0xf2a00024, 0xd2800025, 0xf9000085, 0xf9000482, 0xf9000883, 0x91008080, 0xd65f03c0]

theorem assignStr_impl : AssignStr (toy.link (at0 assignStrCode)) A0 8 (MC ckStr) HAssignS := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hm0, hrep, hstr, hown, hH⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  obtain ⟨h0, hdis⟩ := hH
  simp only [MC_priv, List.getD_cons_succ, List.getD_cons_zero] at h0 hdis
  rw [readLE_rtView0 (a := MP) (n := 8) (by decide) (by decide)] at h0
  obtain ⟨hmp, hacc, hal, hu⟩ := hrep
  have hf : f = AMap.empty := by
    rcases hu with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · omega
  subst hf
  simp only [MP] at hacc
  janus_run
  have hfr : MemFrame s.mem (((s.mem.writeLE 67584 8 1).writeLE 67592 8 (BitVec.toNat (s.regs 2))).writeLE
      67600 8 (BitVec.toNat (s.regs 3))) (rtWrites (MC ckStr) s 4 ++ []) := by
    simp only [rtWrites, calleeStack, MC_priv, MC_depth, priv0, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67600 : Nat) = MP + 16 from rfl, show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  refine MapSat.mapReturn_of (MC ckStr) 4 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl hfr (((hze.writeLE _ (by decide)).writeLE _ (by decide)).writeLE _
      (by decide)) (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  -- the key's bytes, as the runtime's memory holds them after the stores
  have hkey : ∀ v, (rtView priv0 ((((s.mem.writeLE MP 8 1).writeLE (MP + 8) 8 (s.regs 2).toNat).writeLE
      (MP + 16) 8 (s.regs 3).toNat).writeLE (MP + 32) 8 v)).readLE (s.regs 2).toNat (s.regs 3).toNat =
      s.mem.readLE (s.regs 2).toNat (s.regs 3).toNat := by
    intro v
    rcases hdis with h0' | hd
    · rw [h0']; rfl
    rcases hown with h | h
    · rw [h]; rfl
    · rw [MC_priv] at h
      rw [readLE_rtView h]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [MP] at hd ⊢; omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by simp only [MP] at hd ⊢; omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by simp only [MP] at hd ⊢; omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by simp only [MP] at hd ⊢; omega)]
  exact cell_assign ckStr _ _ (s.regs 28)
    (by rw [Memory.accessible_writeLE, Memory.accessible_writeLE, Memory.accessible_writeLE]; exact hacc)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Memory.readLE_writeLE_self])
    (fun v => by
      show (Memory.readLE _ (MP + 16) 8, (rtView priv0 _).readLE (Memory.readLE _ (MP + 8) 8)
        (Memory.readLE _ (MP + 16) 8)) = _
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (s.regs 3).isLt,
        Memory.readLE_writeLE_of_disjoint _ _ (by decide), Memory.readLE_writeLE_of_disjoint _ _ (by decide),
        Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (s.regs 2).isLt, hkey]
      rfl)
    (((hze.writeLE _ (by decide)).writeLE _ (by decide)).writeLE _ (by decide))

/-- The arguments of the witness assignment: the 4-byte string at `SK` (in the runtime's
memory, away from the header). -/
def aargs : Nat → W64 := args (BitVec.ofNat 64 SK) 4#64

/-- `AssignStr` is satisfiable: `MC ckStr`, `H = HAssignS`, an assignment of the string `"ABCD"`
at `SK` to the empty non-nil map. -/
theorem assignStr_satisfiable : ∃ (vs : Nat) (M : MapModel (Nat × Nat) (BitVec (8 * vs)))
    (impl : List Segment) (H : RtReady), M.Laws ∧ AssignStr (toy.link impl) A0 vs M H ∧
      ∃ (f : AMap (Nat × Nat) (BitVec (8 * vs))) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (Map.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
        M.Rep s.mem (s.regs 1).toNat f ∧ StrIn s M.depth 4 ∧
        StrOwned M (s.regs 2).toNat (s.regs 3).toNat ∧
        Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat, (s.regs 3).toNat] s) := by
  refine ⟨8, MC ckStr, _, HAssignS, MC_laws _, assignStr_impl, AMap.empty, mstate mmem aargs, rfl,
    mstate_rtpre _ rfl rfl mmem rfl _ 4 (by decide) mmem_zenv mmem_guard, trivial, by decide,
    mmem_repC _, ⟨by decide, by decide, ?_⟩, Or.inr (inPriv0 (by decide) (by decide)), ?_, ?_⟩
  · simp only [calleeStack, outside_cons, outside_nil, and_true]
    constructor <;> simp [mstate, aargs, args, IfaceModel.wsp, SK]
  · show (rtView priv0 mmem).readLE MP 8 = 0
    rw [readLE_rtView0 (by decide) (by decide)]; decide
  · exact Or.inr (Or.inr (by decide))

end Janus.Contracts.MapStrSat
