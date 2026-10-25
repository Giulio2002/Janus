import Janus.Contracts.MapStrAmd64
import Janus.Contracts.MapStrSat
import Janus.Contracts.IfaceSatAmd64
import Janus.Contracts.MapModel0

/-!
# The string-keyed map contracts are satisfiable (amd64)

As `Janus.Contracts.MapStrSat`, for `Janus.Contracts.MapStrAmd64`.
-/

namespace Janus.Contracts.MapStr

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map
  Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
open Janus (MemFrame Outside outside_cons outside_nil InRanges)

/-- The return of a model implementation as `MapAmd64.RTReturn`. -/
theorem mapReturn64_of {K V : Type} (M : MapModel K V) (nargs : Nat) (extra : List (Nat × Nat))
    (except : Nat) (s s' : State) (P : (Nat → W64) → Janus.Arm64.Memory → Prop)
    (hrip : s'.rip = retAddrOf s) (h4 : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (hmx : s'.mxcsr = s.mxcsr)
    (hfr : MemFrame s.mem s'.mem (Contracts.MapAmd64.rtWrites M s nargs ++ extra))
    (henv : M.Env s'.mem (s.regs 14)) (hok : Contracts.MapAmd64.OthersKept M s.mem s'.mem except)
    (hp : P s'.regs s'.mem) : Contracts.MapAmd64.RTReturn M nargs extra except s s' P := by
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mem, ?_, hfr, henv, hok, hp⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx⟩ := s'
  simp only at hrip h4 h5 h14 hx hfs hdf hmx ⊢
  subst hrip hfs hdf hmx
  congr
  · funext i
    simp only [Contracts.MapAmd64.keepABI]
    split
    · rename_i hi; subst hi; exact h4
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [Contracts.MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-- `mov $0x10f00, %eax; xor %ebx, %ebx; ret`: the zero slot and `false`. -/
def access2StrCode64 : List Nat := [0xb8, 0x00, 0x0f, 0x01, 0x00, 0x31, 0xdb, 0xc3]

theorem access2Str64_impl : Access2Str64 (toy.link (at0 access2StrCode64)) A0 MS0 := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨⟨he1, he2⟩, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap, -⟩ := hpre
  obtain ⟨hmp, rfl⟩ := isMap_MS0 hmap
  janus64_run
  refine mapReturn64_of MS0 4 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) ⟨he1, he2⟩ (fun _ _ _ h => h)
    ⟨?_, ?_, ?_⟩
  · simp [IsMap, hmp]
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact ⟨he1, ⟨(0x10000, 0x11000), by simp [MS0], by decide, by decide⟩, by simpa [AMap.empty, ZS] using he2⟩
  · simp [setRegF, AMap.empty]

/-- `Access2Str64` is satisfiable. -/
theorem access2Str64_satisfiable : ∃ (M : MapModel (Nat × Nat) (BitVec 64))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ Access2Str64 (toy.link impl) A0 M ∧
      ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (Contracts.MapAmd64.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat AMap.empty ∧
        (s.regs 1).toNat + (s.regs 7).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 1).toNat (s.regs 7).toNat false = true ∧
        Outside (s.regs 1).toNat (s.regs 7).toNat (Contracts.MapAmd64.calleeStack s M.depth 4)) := by
  refine ⟨MS0, _, MS0_laws, access2Str64_impl,
    { regs := fun i => if i = 1 then BitVec.ofNat 64 VAL else if i = 7 then 8#64
        else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
      rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
      mem := Janus.Contracts.EqHashModel.wmem64 }, rfl,
    ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
      by decide, rfl, rfl, by decide, ?_⟩, trivial, by simp [IsMap], by decide, by decide, ?_⟩⟩
  · simp only [MS0, outside_cons, outside_nil, and_true]; decide
  · simp only [Contracts.MapAmd64.calleeStack, MS0, outside_cons, outside_nil, and_true]; decide

end Janus.Contracts.MapStr

/-! ## The map witnesses' call state (amd64; shared with `MapSatAmd64`, `MapVarSatAmd64`) -/

namespace Janus.Contracts.MapSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts.MapAmd64 Janus.Contracts.MapModel0 Janus.Contracts.IfaceSatAmd64
open Janus (MemFrame Outside outside_cons outside_nil InRanges)
open Janus.Contracts.IfaceModel (wsp wg wret)

/-! ## The witness call state -/

/-- The witness call state (amd64): the arguments `r`, `RSP = wsp`, `R14 = wg`, memory `m`. -/
def mstate64 (m : Janus.Arm64.Memory) (r : Nat → W64) : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else r i,
    rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := m }

/-- `RTPre` at the witness state, for any model with the private memory `priv0`, 64 bytes of
stack and an environment that holds there. -/
theorem mstate64_rtpre {K V : Type} (M : MapModel K V) (hp : M.priv = priv0) (hd : M.depth = 64)
    (m : Janus.Arm64.Memory) (hreg : m.regions = IfaceModel.wmem.regions) (r : Nat → W64) (n : Nat)
    (hn : n ≤ 4) (he : M.Env m (BitVec.ofNat 64 wg)) (hg : m.readLE (wg + 16) 8 = 0)
    (hret : m.readLE wsp 8 = wret) : RTPre M n (mstate64 m r) := by
  have hacc : ∀ a k w, m.accessible a k w = IfaceModel.wmem.accessible a k w := by
    intro a k w; unfold Janus.Arm64.Memory.accessible; rw [hreg]
  have hw : IfaceModel.wmem.accessible (wsp - 64) (64 + 8 + 8 * 4) true = true := by decide
  have h4 : (mstate64 m r).regs 4 = BitVec.ofNat 64 wsp := rfl
  have h14 : (mstate64 m r).regs 14 = BitVec.ofNat 64 wg := rfl
  have hm : (mstate64 m r).mem = m := rfl
  refine ⟨by rw [h14, hm]; exact he, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [regG, stackguard0Offset, h14]; decide
  · simp only [regG, stackguard0Offset, h14, hm, hacc]; decide
  · simp only [stackguard0, regG, regSP, stackguard0Offset, h14, h4, hm, hd]
    rw [show (BitVec.ofNat 64 wg).toNat = wg from rfl, hg]; decide
  · simp only [h4]; decide
  · simp only [h4, hd]; decide
  · simp only [h4]; simp [wsp]; omega
  · simp only [h4, hm, hd, BitVec.toNat_ofNat, hacc]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by simp [wsp]) (by simp [wsp]; omega)
  · simp only [h4, hm]; rw [show (BitVec.ofNat 64 wsp).toNat = wsp from rfl, hret]; decide
  · simp only [h4, hd, hp, priv0, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [wsp]

theorem mmem64_guard : mmem64.readLE (wg + 16) 8 = 0 := by decide
theorem mmem64Dead_guard : mmem64Dead.readLE (wg + 16) 8 = 0 := by
  unfold mmem64Dead; rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; decide
theorem mmem64Dead_ret : mmem64Dead.readLE wsp 8 = wret := by
  unfold mmem64Dead; rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact mmem64_ret

/-- The arguments `t = TY` (`RAX`), `m = MP` (`RBX`), then `RCX = a2`, `RDI = a3`. -/
def args (a2 a3 : W64) : Nat → W64 :=
  fun i => if i = 0 then BitVec.ofNat 64 TY else if i = 3 then BitVec.ofNat 64 MP
    else if i = 1 then a2 else if i = 7 then a3 else 0

/-- `mov $0x10900, %eax; xor %ebx, %ebx; ret`: `ZS` and `false`. -/
def zsCode : List Nat := [0xb8, 0x00, 0x09, 0x01, 0x00, 0x31, 0xdb, 0xc3]

/-- `ret`. -/
def retCode : List Nat := [0xc3]

end Janus.Contracts.MapSatAmd64

/-! ## The string-keyed witnesses of `MapStrAmd64` (`MapModel0.ME`, `MapModel0.MC ckStr`) -/

namespace Janus.Contracts.MapSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts.MapAmd64 Janus.Contracts.MapModel0 Janus.Contracts.IfaceSatAmd64
  Janus.Contracts.MapStr
open Janus (MemFrame Outside outside_cons outside_nil InRanges)
open Janus.Contracts (RtReady rtView Ready64 readLE_rtView rtView_accessible)
open Janus.Contracts.MapVar (SlotHoldsN)
open Janus.Contracts.IfaceModel (wsp wg wret VAL)

/-- A string key `(p, 8)` (`RCX`, `RDI`) at an address of the witness memory's user data or model
heap is readable and outside the callee's stack window. -/
theorem strIn_w (p : Nat) (h1 : 0x10300 ≤ p) (h2 : p + 8 ≤ 0x31000) (h3 : p + 8 ≤ 0x11000 ∨ 0x30000 ≤ p)
    (n : Nat) (_hn : n ≤ 4) : StrIn64 (mstate64 mmem64 (args (BitVec.ofNat 64 p) 8#64)) 64 n := by
  have hp : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨by simp [mstate64, args, hp]; omega, ?_, ?_⟩
  · simp only [mstate64, args, reduceIte, Nat.reduceEqDiff, hp]
    rcases h3 with h3 | h3
    · exact Janus.Arm64.Memory.accessible_mono _ (show mmem64.accessible 0x10300 0xd00 false = true by decide)
        (by omega) (by simp; omega)
    · exact Janus.Arm64.Memory.accessible_mono _ (show mmem64.accessible 0x30000 0x1000 false = true by decide)
        (by omega) (by simp; omega)
  · simp only [Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    simp [mstate64, args, hp, wsp]; omega

/-- The string key's lookups and deletes return `ZS` and `false` / do nothing (`ME`). -/
theorem access1Str64_impl : Access1Str64 (toy.link (at0 zsCode)) A0 8 (ME (Nat × Nat)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap, -⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  refine MapStr.mapReturn64_of (ME _) 4 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ⟨hmap, ?_⟩
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
  exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, MapModel0.ZS] using hze.2⟩

theorem access1Str64_satisfiable : ∃ (M : MapModel (Nat × Nat) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ Access1Str64 (toy.link impl) A0 8 M ∧
      ∃ (f : AMap (Nat × Nat) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (s.regs 3).toNat ≠ 0 ∧
      (Contracts.MapAmd64.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f ∧
        StrIn64 s M.depth 4) :=
  ⟨ME _, _, ME_laws _, access1Str64_impl, AMap.empty, mstate64 mmem64 (args (BitVec.ofNat 64 VAL) 8#64),
    rfl, by decide, mstate64_rtpre _ rfl rfl mmem64 rfl _ 4 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    trivial, (isMap_of_ne (by decide)).2 (mmem64_rep _),
    strIn_w VAL (by decide) (by decide) (Or.inr (by decide)) 4 (by decide)⟩

theorem deleteStr64_impl : DeleteStr64 (toy.link (at0 retCode)) A0 8 (ME (Nat × Nat)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap, -⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  refine MapStr.mapReturn64_of (ME _) 4 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ?_
  rw [erase_empty]; exact hmap

theorem deleteStr64_satisfiable : ∃ (M : MapModel (Nat × Nat) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ DeleteStr64 (toy.link impl) A0 8 M ∧
      ∃ (f : AMap (Nat × Nat) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (s.regs 3).toNat ≠ 0 ∧
      (Contracts.MapAmd64.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f ∧
        StrIn64 s M.depth 4) :=
  ⟨ME _, _, ME_laws _, deleteStr64_impl, AMap.empty, mstate64 mmem64 (args (BitVec.ofNat 64 VAL) 8#64),
    rfl, by decide, mstate64_rtpre _ rfl rfl mmem64 rfl _ 4 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    trivial, (isMap_of_ne (by decide)).2 (mmem64_rep _),
    strIn_w VAL (by decide) (by decide) (Or.inr (by decide)) 4 (by decide)⟩

/-- The readiness of a string assignment in `MC ckStr`: the map is empty and the key's bytes
are not in the header the call writes (`AssignStr64` allows the key's bytes anywhere in the
runtime's memory, also in the map's own storage, which the call changes). -/
def HAssignStr : RtReady := fun args _ _ v =>
  v.readLE MP 8 = 0 ∧ (args.getD 3 0 = 0 ∨ MP + 56 ≤ args.getD 2 0 ∨ args.getD 2 0 + args.getD 3 0 ≤ MP)

/-- `mov $0x10800, %edx; movq $1, (%rdx); mov %rcx, 8(%rdx); mov %rdi, 16(%rdx);
lea 32(%rdx), %rax; ret`: `used = 1`, the key's header, the value slot `MP + 32`. -/
def assignStrCode64 : List Nat :=
  [0xba, 0x00, 0x08, 0x01, 0x00, 0x48, 0xc7, 0x02, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4a, 0x08,
   0x48, 0x89, 0x7a, 0x10, 0x48, 0x8d, 0x42, 0x20, 0xc3]

theorem assignStr64_impl : AssignStr64 (toy.link (at0 assignStrCode64)) A0 8 (MC ckStr) HAssignStr := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hm0, hrep, -, hown, hH⟩ := hpre
  obtain ⟨hmp, hacc, hal, hu⟩ := hrep
  obtain ⟨h0, hdis⟩ := hH
  simp only [MC_priv, List.getD_cons_succ, List.getD_cons_zero] at h0 hdis
  rw [readLE_rtView0 (a := MP) (n := 8) (by decide) (by decide)] at h0
  have hf : f = AMap.empty := by
    rcases hu with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · omega
  subst hf
  simp only [MP] at hacc
  have hout' := hout
  simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true] at hout'
  janus64_run
  have hfr : MemFrame s.mem (((Janus.Arm64.Memory.writeLE s.mem 67584 8 1).writeLE 67592 8
      (BitVec.toNat (s.regs 1))).writeLE 67600 8 (BitVec.toNat (s.regs 7)))
      (Contracts.MapAmd64.rtWrites (MC ckStr) s 4 ++ []) := by
    simp only [Contracts.MapAmd64.rtWrites, MapAmd64.calleeStack, MC_priv, MC_depth, priv0,
      List.append_nil, List.cons_append, List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67600 : Nat) = MP + 16 from rfl, show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  have hm1 : (s.mem.writeLE MP 8 1).accessible MP 56 true = true := by
    rw [Janus.Arm64.Memory.accessible_writeLE]; exact hacc
  refine MapStr.mapReturn64_of (MC ckStr) 4 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl hfr
    (((hze.writeLE _ (by decide)).writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  -- the key's bytes, as the runtime's memory holds them, are those of the call state
  have hkey : ∀ v, (rtView priv0 ((((s.mem.writeLE MP 8 1).writeLE (MP + 8) 8 (BitVec.toNat (s.regs 1))).writeLE
      (MP + 16) 8 (BitVec.toNat (s.regs 7))).writeLE (MP + 32) 8 v)).readLE (s.regs 1).toNat (s.regs 7).toNat =
      s.mem.readLE (s.regs 1).toNat (s.regs 7).toNat := by
    intro v
    by_cases hz : (s.regs 7).toNat = 0
    · rw [hz]; rfl
    rcases hown with h | h
    · exact absurd h hz
    · rw [readLE_rtView (rt := priv0) h]
      have hd : ∀ a, MP ≤ a → a + 8 ≤ MP + 56 →
          ((s.regs 1).toNat + (s.regs 7).toNat ≤ a ∨ a + 8 ≤ (s.regs 1).toNat) := by
        intro a h1 h2; rcases hdis with hz' | hz' | hz'
        · exact absurd hz' hz
        · omega
        · omega
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (hd _ (by simp [MP]) (by simp [MP])),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (hd _ (by simp [MP]) (by simp [MP])),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (hd _ (by simp [MP]) (by simp [MP])),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (hd _ (by simp [MP]) (by simp [MP]))]
  exact cell_assign ckStr _ _ (s.regs 14)
    (by rw [Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.accessible_writeLE]; exact hm1)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide), Janus.Arm64.Memory.readLE_writeLE_self])
    (fun v => by
      show (Janus.Arm64.Memory.readLE _ (MP + 16) 8, (rtView priv0 _).readLE (Janus.Arm64.Memory.readLE _ (MP + 8) 8)
        (Janus.Arm64.Memory.readLE _ (MP + 16) 8)) = _
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
        Janus.Arm64.Memory.readLE_writeLE_self,
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
        Janus.Arm64.Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (s.regs 1).isLt, Nat.mod_eq_of_lt (s.regs 7).isLt, hkey]
      rfl)
    (((hze.writeLE _ (by decide)).writeLE _ (by decide)).writeLE _ (by decide))

theorem assignStr64_satisfiable : ∃ (M : MapModel (Nat × Nat) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment) (H : RtReady), M.Laws ∧ AssignStr64 (toy.link impl) A0 8 M H ∧
      ∃ (f : AMap (Nat × Nat) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (Contracts.MapAmd64.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧
        M.Rep s.mem (s.regs 3).toNat f ∧ StrIn64 s M.depth 4 ∧
        StrOwned M (s.regs 1).toNat (s.regs 7).toNat ∧
        Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat, (s.regs 7).toNat] s) :=
  ⟨MC ckStr, _, HAssignStr, MC_laws _, assignStr64_impl, AMap.empty,
    mstate64 mmem64 (args (BitVec.ofNat 64 SK) 8#64), rfl,
    mstate64_rtpre _ rfl rfl mmem64 rfl _ 4 (by decide) mmem64_zenv mmem64_guard mmem64_ret, trivial,
    by decide, mmem64_repC _, strIn_w SK (by decide) (by decide) (Or.inl (by decide)) 4 (by decide),
    Or.inr (inPriv0 (by decide) (by decide)),
    ⟨by show (rtView priv0 mmem64).readLE MP 8 = 0
        rw [readLE_rtView0 (by decide) (by decide)]; decide,
      Or.inr (Or.inl (by decide))⟩⟩

end Janus.Contracts.MapSatAmd64
