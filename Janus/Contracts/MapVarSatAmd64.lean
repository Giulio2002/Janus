import Janus.Contracts.MapVarAmd64
import Janus.Contracts.MapSatAmd64

/-!
# The map contracts of `Janus.Contracts.MapVarAmd64` are satisfiable (amd64)

As `Janus.Contracts.MapSatAmd64`, for `makemap`, the generic entry points (8-byte keys of
regular memory, `MapModel0.TY`/`KT`), the `_fat` lookups, the `_fast32` entry points and
`mapassign_fast64ptr` (values of `vs = 8` bytes): the models `MapModel0.ME` (lookups,
deletes) and `MapModel0.MC` (assignments, `makemap`), x86-64 code from GNU `as`, and a call
state satisfying each contract's whole precondition, with the non-nil map `MP`
(`<contract>_satisfiable`; `audit/round9/sat_check.py`, row SAT).
-/

namespace Janus.Contracts.MapVarSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts.MapAmd64 Janus.Contracts.MapVarAmd64 Janus.Contracts.MapModel0
  Janus.Contracts.IfaceSatAmd64 Janus.Contracts.MapSatAmd64
open Janus (MemFrame Outside outside_cons outside_nil InRanges)
open Janus.Contracts (RtReady rtView Ready64 readLE_rtView rtView_accessible)
open Janus.Contracts.MapVar (SlotHoldsN KeyRegular keyAt)
open Janus.Contracts.IfaceModel (wsp wg wret VAL)

/-- The key pointer of the witnesses: the 8 bytes at `IfaceModel.VAL` (user data). -/
theorem keyIn_w (n : Nat) :
    KeyIn (mstate64 mmem64 (args (BitVec.ofNat 64 VAL) 0)) 64 n VAL 8 := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
  simp [mstate64, VAL, wsp]

/-! ## Generic lookups (`ME`) -/

theorem access1G_impl : Access1G (toy.link (at0 zsCode)) A0 8 8 (ME (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, -, hmap, -⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  refine MapStr.mapReturn64_of (ME _) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ⟨hmap, ?_⟩
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
  exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩

theorem access1G_satisfiable : ∃ (M : MapModel (BitVec (8 * 8)) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ Access1G (toy.link impl) A0 8 8 M ∧
      ∃ (f : AMap (BitVec (8 * 8)) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat 8 ∧
        IsMap M s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 3 (s.regs 1).toNat 8) :=
  ⟨ME _, _, ME_laws _, access1G_impl, AMap.empty, mstate64 mmem64 (args (BitVec.ofNat 64 VAL) 0), rfl,
    by decide, mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    trivial, keyRegular_mmem64, (isMap_of_ne (by decide)).2 (mmem64_rep _), keyIn_w 3⟩

/-- `mov %rdi, %rax; xor %ebx, %ebx; ret`: the caller's zero value and `false`. -/
def fatCode : List Nat := [0x48, 0x89, 0xf8, 0x31, 0xdb, 0xc3]

theorem access2G_impl : Access2G (toy.link (at0 zsCode)) A0 8 8 (ME (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, -, hmap, -⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  refine MapStr.mapReturn64_of (ME _) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ⟨hmap, ?_, ?_⟩
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩
  · simp [setRegF, AMap.empty]

theorem access2G_satisfiable : ∃ (M : MapModel (BitVec (8 * 8)) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ Access2G (toy.link impl) A0 8 8 M ∧
      ∃ (f : AMap (BitVec (8 * 8)) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat 8 ∧
        IsMap M s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 3 (s.regs 1).toNat 8) :=
  ⟨ME _, _, ME_laws _, access2G_impl, AMap.empty, mstate64 mmem64 (args (BitVec.ofNat 64 VAL) 0), rfl,
    by decide, mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    trivial, keyRegular_mmem64, (isMap_of_ne (by decide)).2 (mmem64_rep _), keyIn_w 3⟩

theorem deleteG_impl : DeleteG (toy.link (at0 retCode)) A0 8 8 (ME (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, -, hmap, -⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  refine MapStr.mapReturn64_of (ME _) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ?_
  rw [erase_empty]; exact hmap

theorem deleteG_satisfiable : ∃ (M : MapModel (BitVec (8 * 8)) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ DeleteG (toy.link impl) A0 8 8 M ∧
      ∃ (f : AMap (BitVec (8 * 8)) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat 8 ∧
        IsMap M s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 3 (s.regs 1).toNat 8) :=
  ⟨ME _, _, ME_laws _, deleteG_impl, AMap.empty, mstate64 mmem64 (args (BitVec.ofNat 64 VAL) 0), rfl,
    by decide, mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    trivial, keyRegular_mmem64, (isMap_of_ne (by decide)).2 (mmem64_rep _), keyIn_w 3⟩

theorem access1Fat_impl : Access1Fat (toy.link (at0 fatCode)) A0 8 8 (ME (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, -, hmap, -⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  refine MapStr.mapReturn64_of (ME _) 4 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ⟨hmap, fun v h => by simp [AMap.empty] at h, fun _ => by simp [setRegF]⟩

theorem access1Fat_satisfiable : ∃ (M : MapModel (BitVec (8 * 8)) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ Access1Fat (toy.link impl) A0 8 8 M ∧
      ∃ (f : AMap (BitVec (8 * 8)) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat 8 ∧
        IsMap M s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 4 (s.regs 1).toNat 8) :=
  ⟨ME _, _, ME_laws _, access1Fat_impl, AMap.empty, mstate64 mmem64 (args (BitVec.ofNat 64 VAL) 0), rfl,
    by decide, mstate64_rtpre _ rfl rfl mmem64 rfl _ 4 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    trivial, keyRegular_mmem64, (isMap_of_ne (by decide)).2 (mmem64_rep _), keyIn_w 4⟩

theorem access2Fat_impl : Access2Fat (toy.link (at0 fatCode)) A0 8 8 (ME (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, -, hmap, -⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  refine MapStr.mapReturn64_of (ME _) 4 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ⟨hmap, fun v h => by simp [AMap.empty] at h, fun _ => by simp [setRegF], by simp [setRegF, AMap.empty]⟩

theorem access2Fat_satisfiable : ∃ (M : MapModel (BitVec (8 * 8)) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ Access2Fat (toy.link impl) A0 8 8 M ∧
      ∃ (f : AMap (BitVec (8 * 8)) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat 8 ∧
        IsMap M s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 4 (s.regs 1).toNat 8) :=
  ⟨ME _, _, ME_laws _, access2Fat_impl, AMap.empty, mstate64 mmem64 (args (BitVec.ofNat 64 VAL) 0), rfl,
    by decide, mstate64_rtpre _ rfl rfl mmem64 rfl _ 4 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    trivial, keyRegular_mmem64, (isMap_of_ne (by decide)).2 (mmem64_rep _), keyIn_w 4⟩

theorem access1F32_impl : Access1F32 (toy.link (at0 zsCode)) A0 8 (ME (BitVec 32)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  refine MapStr.mapReturn64_of (ME _) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ⟨hmap, ?_⟩
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
  exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩

theorem access1F32_satisfiable : ∃ (M : MapModel (BitVec 32) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ Access1F32 (toy.link impl) A0 8 M ∧
      ∃ (f : AMap (BitVec 32) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f) :=
  ⟨ME _, _, ME_laws _, access1F32_impl, AMap.empty, mstate64 mmem64 (args 7#64 0), rfl,
    by decide, mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    trivial, (isMap_of_ne (by decide)).2 (mmem64_rep _)⟩

theorem access2F32_impl : Access2F32 (toy.link (at0 zsCode)) A0 8 (ME (BitVec 32)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  refine MapStr.mapReturn64_of (ME _) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ⟨hmap, ?_, ?_⟩
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩
  · simp [setRegF, AMap.empty]

theorem access2F32_satisfiable : ∃ (M : MapModel (BitVec 32) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ Access2F32 (toy.link impl) A0 8 M ∧
      ∃ (f : AMap (BitVec 32) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f) :=
  ⟨ME _, _, ME_laws _, access2F32_impl, AMap.empty, mstate64 mmem64 (args 7#64 0), rfl,
    by decide, mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    trivial, (isMap_of_ne (by decide)).2 (mmem64_rep _)⟩

theorem deleteF32_impl : DeleteF32 (toy.link (at0 retCode)) A0 8 (ME (BitVec 32)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  refine MapStr.mapReturn64_of (ME _) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ?_
  rw [erase_empty]; exact hmap

theorem deleteF32_satisfiable : ∃ (M : MapModel (BitVec 32) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ DeleteF32 (toy.link impl) A0 8 M ∧
      ∃ (f : AMap (BitVec 32) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f) :=
  ⟨ME _, _, ME_laws _, deleteF32_impl, AMap.empty, mstate64 mmem64 (args 7#64 0), rfl,
    by decide, mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    trivial, (isMap_of_ne (by decide)).2 (mmem64_rep _)⟩

/-! ## Assignments (`MC`, the map empty) -/

/-- `mov (%rcx), %rsi; mov $0x10800, %edx; movq $1, (%rdx); mov %rsi, 8(%rdx);
lea 32(%rdx), %rax; ret`: a copy of the 8 key bytes (read first: the key may lie anywhere,
even in the header), `used = 1`, the value slot `MP + 32`. -/
def assignGCode : List Nat :=
  [0x48, 0x8b, 0x31, 0xba, 0x00, 0x08, 0x01, 0x00, 0x48, 0xc7, 0x02, 0x01, 0x00, 0x00, 0x00,
   0x48, 0x89, 0x72, 0x08, 0x48, 0x8d, 0x42, 0x20, 0xc3]

theorem assignG_impl : AssignG (toy.link (at0 assignGCode)) A0 8 8 (MC ck64) HAssign := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, -, hm0, hrep, ⟨hk1, hk2, hk3⟩, hH⟩ := hpre
  obtain ⟨hmp, hacc, hal, hu⟩ := hrep
  have h0 : s.mem.readLE MP 8 = 0 := by
    have := hH; simp only [Ready64, HAssign, MC_priv] at this
    rwa [readLE_rtView0 (a := MP) (n := 8) (by decide) (by decide)] at this
  have hf : f = AMap.empty := by
    rcases hu with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · omega
  subst hf
  simp only [MP] at hacc
  have hout' := hout
  simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true] at hout'
  janus64_run
  have hfr : MemFrame s.mem ((Janus.Arm64.Memory.writeLE s.mem 67584 8 1).writeLE 67592 8 (Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8))
      (rtWrites (MC ck64) s 3 ++ []) := by
    simp only [rtWrites, MapAmd64.calleeStack, MC_priv, MC_depth, priv0, List.append_nil,
      List.cons_append, List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  have hm1 : (s.mem.writeLE MP 8 1).accessible MP 56 true = true := by
    rw [Janus.Arm64.Memory.accessible_writeLE]; exact hacc
  refine MapStr.mapReturn64_of (MC ck64) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl hfr
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  exact cell_assign ck64 _ _ (s.regs 14) (by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hm1)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide), Janus.Arm64.Memory.readLE_writeLE_self])
    (fun v => by
      show BitVec.ofNat _ (Janus.Arm64.Memory.readLE _ (MP + 8) 8) = _
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide), Janus.Arm64.Memory.readLE_writeLE_self]
      rw [Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ _)]; rfl)
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))

theorem assignG_satisfiable : ∃ (M : MapModel (BitVec (8 * 8)) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment) (H : RtReady), M.Laws ∧ AssignG (toy.link impl) A0 8 8 M H ∧
      ∃ (f : AMap (BitVec (8 * 8)) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat 8 ∧
        (s.regs 3).toNat ≠ 0 ∧ M.Rep s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 3 (s.regs 1).toNat 8 ∧
        Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat,
          s.mem.readLE (s.regs 1).toNat 8] s) :=
  ⟨MC ck64, _, HAssign, MC_laws _, assignG_impl, AMap.empty,
    mstate64 mmem64 (args (BitVec.ofNat 64 VAL) 0), rfl,
    mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret, trivial,
    keyRegular_mmem64, by decide, mmem64_repC _, keyIn_w 3, hAssign_mmem64 _ _ _⟩

/-- `mov $0x10800, %edx; movq $1, (%rdx); mov %ecx, 8(%rdx); lea 32(%rdx), %rax; ret`:
`used = 1`, the 4-byte key, the value slot `MP + 32`. -/
def assign32Code : List Nat :=
  [0xba, 0x00, 0x08, 0x01, 0x00, 0x48, 0xc7, 0x02, 0x01, 0x00, 0x00, 0x00, 0x89, 0x4a, 0x08,
   0x48, 0x8d, 0x42, 0x20, 0xc3]

theorem assignF32_impl : AssignF32 (toy.link (at0 assign32Code)) A0 8 (MC ck32) HAssign := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hm0, hrep, hH⟩ := hpre
  obtain ⟨hmp, hacc, hal, hu⟩ := hrep
  have h0 : s.mem.readLE MP 8 = 0 := by
    have := hH; simp only [Ready64, HAssign, MC_priv] at this
    rwa [readLE_rtView0 (a := MP) (n := 8) (by decide) (by decide)] at this
  have hf : f = AMap.empty := by
    rcases hu with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · omega
  subst hf
  simp only [MP] at hacc
  have hout' := hout
  simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true] at hout'
  janus64_run
  have hfr : MemFrame s.mem ((Janus.Arm64.Memory.writeLE s.mem 67584 8 1).writeLE 67592 4 (BitVec.toNat (s.regs 1) % 4294967296))
      (rtWrites (MC ck32) s 3 ++ []) := by
    simp only [rtWrites, MapAmd64.calleeStack, MC_priv, MC_depth, priv0, List.append_nil,
      List.cons_append, List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  have hm1 : (s.mem.writeLE MP 8 1).accessible MP 56 true = true := by
    rw [Janus.Arm64.Memory.accessible_writeLE]; exact hacc
  refine MapStr.mapReturn64_of (MC ck32) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl hfr
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  exact cell_assign ck32 _ _ (s.regs 14) (by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hm1)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide), Janus.Arm64.Memory.readLE_writeLE_self])
    (fun v => by
      show BitVec.ofNat _ (Janus.Arm64.Memory.readLE _ (MP + 8) 4) = _
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide), Janus.Arm64.Memory.readLE_writeLE_self]
      apply BitVec.eq_of_toNat_eq
      simp only [key32, BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega)
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))

theorem assignF32_satisfiable : ∃ (M : MapModel (BitVec 32) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment) (H : RtReady), M.Laws ∧ AssignF32 (toy.link impl) A0 8 M H ∧
      ∃ (f : AMap (BitVec 32) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧
        M.Rep s.mem (s.regs 3).toNat f ∧
        Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, (key32 s).toNat] s) :=
  ⟨MC ck32, _, HAssign, MC_laws _, assignF32_impl, AMap.empty, mstate64 mmem64 (args 7#64 0), rfl,
    mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret, trivial,
    by decide, mmem64_repC _, hAssign_mmem64 _ _ _⟩

theorem assign64Ptr_impl : Assign64Ptr (toy.link (at0 assignCode)) A0 8 (MC ck64) HAssign := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hm0, hrep, hH⟩ := hpre
  obtain ⟨hmp, hacc, hal, hu⟩ := hrep
  have h0 : s.mem.readLE MP 8 = 0 := by
    have := hH; simp only [Ready64, HAssign, MC_priv] at this
    rwa [readLE_rtView0 (a := MP) (n := 8) (by decide) (by decide)] at this
  have hf : f = AMap.empty := by
    rcases hu with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · omega
  subst hf
  simp only [MP] at hacc
  have hout' := hout
  simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true] at hout'
  janus64_run
  have hfr : MemFrame s.mem ((Janus.Arm64.Memory.writeLE s.mem 67584 8 1).writeLE 67592 8 (BitVec.toNat (s.regs 1)))
      (rtWrites (MC ck64) s 3 ++ []) := by
    simp only [rtWrites, MapAmd64.calleeStack, MC_priv, MC_depth, priv0, List.append_nil,
      List.cons_append, List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  have hm1 : (s.mem.writeLE MP 8 1).accessible MP 56 true = true := by
    rw [Janus.Arm64.Memory.accessible_writeLE]; exact hacc
  refine MapStr.mapReturn64_of (MC ck64) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl hfr
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  exact cell_assign ck64 _ _ (s.regs 14) (by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hm1)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide), Janus.Arm64.Memory.readLE_writeLE_self])
    (fun v => by
      show BitVec.ofNat _ (Janus.Arm64.Memory.readLE _ (MP + 8) 8) = _
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide), Janus.Arm64.Memory.readLE_writeLE_self]
      rw [Nat.mod_eq_of_lt (s.regs 1).isLt]; simp)
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))

theorem assign64Ptr_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec (8 * 8)))
    (impl : List Janus.Amd64.Segment) (H : RtReady), M.Laws ∧ Assign64Ptr (toy.link impl) A0 8 M H ∧
      ∃ (f : AMap (BitVec 64) (BitVec (8 * 8))) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧
        M.Rep s.mem (s.regs 3).toNat f ∧
        Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s) :=
  ⟨MC ck64, _, HAssign, MC_laws _, assign64Ptr_impl, AMap.empty,
    mstate64 mmem64 (args (BitVec.ofNat 64 VAL) 0), rfl,
    mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret, trivial,
    by decide, mmem64_repC _, hAssign_mmem64 _ _ _⟩

/-! ## `makemap` (`MC`, no map alive; the code of `makemap_small`) -/

theorem makeMap_impl : MakeMap (toy.link (at0 makeCode)) A0 (MC ck64) HMake := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, -, hH⟩ := hpre
  obtain ⟨h0, hacc⟩ := hH
  rw [MC_priv, readLE_rtView0 (a := MP + 48) (n := 8) (by decide) (by decide)] at h0
  rw [rtView_accessible] at hacc
  simp only [MP] at hacc
  have hout' := hout
  simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true] at hout'
  janus64_run
  have hfr : MemFrame s.mem ((Janus.Arm64.Memory.writeLE s.mem 67632 8 1).writeLE 67584 8 0)
      (rtWrites (MC ck64) s 3 ++ []) := by
    simp only [rtWrites, MapAmd64.calleeStack, MC_priv, MC_depth, priv0, List.append_nil,
      List.cons_append, List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67632 : Nat) = MP + 48 from rfl] at hacc hfr ⊢
  refine MapStr.mapReturn64_of (MC ck64) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl hfr
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ _ h => absurd h (MC_none ck64 h0 _ _)) ⟨?_, ?_, fun mp f h => absurd h (MC_none ck64 h0 _ _)⟩
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]; decide
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact MC_rep_new ck64 (by rw [Janus.Arm64.Memory.accessible_writeLE,
        Janus.Arm64.Memory.accessible_writeLE]; exact hacc)
      (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
        Janus.Arm64.Memory.readLE_writeLE_self])
      (by rw [Janus.Arm64.Memory.readLE_writeLE_self])

theorem makeMap_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Janus.Amd64.Segment)
    (H : RtReady), M.Laws ∧ MakeMap (toy.link impl) A0 M H ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat = 0 ∧
        Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, 0] s) :=
  ⟨MC ck64, _, HMake, MC_laws _, makeMap_impl, mstate64 mmem64Dead (args 0 0), rfl,
    mstate64_rtpre _ rfl rfl mmem64Dead rfl _ 3 (by decide)
      (show ZEnv mmem64Dead from mmem64_zenv.writeLE _ (by decide)) mmem64Dead_guard mmem64Dead_ret,
    trivial, by decide, hMake_dead64 _ _ _⟩

end Janus.Contracts.MapVarSatAmd64
