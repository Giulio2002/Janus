import Janus.Contracts.MapModel0
import Janus.Contracts.MapAmd64
import Janus.Contracts.MapStrSatAmd64

/-!
# The map contracts of `Janus.Contracts.MapAmd64` are satisfiable (amd64)

As `Janus.Contracts.MapSat` for the amd64 contracts: the models `MapModel0.ME` (one empty
non-nil map; lookups, `delete`, `clear`, iteration) and `MapModel0.MC` (one map of at most one
entry; `mapassign_fast64`, `makemap_small`), x86-64 machine code at `IfaceSatAmd64.A0` (bytes
from GNU `as`) proved by symbolic execution to meet each contract, the readiness predicates
`MapModel0.HAssign` / `MapModel0.HMake`, and a call state (`mstate64`, memory
`MapModel0.mmem64`, the return address `wret` at `[RSP]`) satisfying the whole precondition,
with the non-nil map `MP` wherever the contract is about a map (`<contract>_satisfiable`;
`audit/round9/sat_check.py`, row SAT). The call state, `zsCode` and `retCode` are in
`Janus.Contracts.MapStrSatAmd64`, which the string witnesses share.
-/

namespace Janus.Contracts.MapSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts.MapAmd64 Janus.Contracts.MapModel0 Janus.Contracts.IfaceSatAmd64
open Janus (MemFrame Outside outside_cons outside_nil InRanges)
open Janus.Contracts (RtReady rtView Ready64 readLE_rtView rtView_accessible)
open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write)

/-! ## Lookups: return the zero slot and `false` (`ME`) -/

theorem access1_impl : Access1 (toy.link (at0 zsCode)) A0 (ME (BitVec 64)) := by
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

theorem access1_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Janus.Amd64.Segment),
    M.Laws ∧ Access1 (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State),
      s.rip = BitVec.ofNat 64 A0 ∧ (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f) :=
  ⟨ME _, _, ME_laws _, access1_impl, AMap.empty, mstate64 mmem64 (args 7#64 0), rfl, by decide,
    mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret, trivial,
    (isMap_of_ne (by decide)).2 (mmem64_rep _)⟩

theorem access2_impl : Access2 (toy.link (at0 zsCode)) A0 (ME (BitVec 64)) := by
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

theorem access2_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Janus.Amd64.Segment),
    M.Laws ∧ Access2 (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State),
      s.rip = BitVec.ofNat 64 A0 ∧ (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f) :=
  ⟨ME _, _, ME_laws _, access2_impl, AMap.empty, mstate64 mmem64 (args 7#64 0), rfl, by decide,
    mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret, trivial,
    (isMap_of_ne (by decide)).2 (mmem64_rep _)⟩

/-- `ME` with 16-byte keys (`[16]byte`, the generic `mapaccess2`). -/
theorem access2Ptr_impl : Access2Ptr (toy.link (at0 zsCode)) A0 (ME (BitVec 128)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap, -⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  refine MapStr.mapReturn64_of (ME _) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ⟨hmap, ?_, ?_⟩
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩
  · simp [setRegF, AMap.empty]

theorem access2Ptr_satisfiable : ∃ (M : MapModel (BitVec 128) (BitVec 64)) (impl : List Janus.Amd64.Segment),
    M.Laws ∧ Access2Ptr (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 128) (BitVec 64)) (s : State),
      s.rip = BitVec.ofNat 64 A0 ∧ (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f ∧
        s.mem.accessible (s.regs 1).toNat 16 false = true ∧
        Outside (s.regs 1).toNat 16 (Janus.Contracts.MapAmd64.calleeStack s M.depth 3)) :=
  ⟨ME _, _, ME_laws _, access2Ptr_impl, AMap.empty,
    mstate64 mmem64 (args (BitVec.ofNat 64 IfaceModel.VAL) 0), rfl, by decide,
    mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret, trivial,
    (isMap_of_ne (by decide)).2 (mmem64_rep _), by decide,
    by simp only [Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]; decide⟩

/-! ## `delete` and `clear` of the empty map: `ret` -/

theorem delete_impl : Delete (toy.link (at0 retCode)) A0 (ME (BitVec 64)) := by
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

theorem delete_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Janus.Amd64.Segment),
    M.Laws ∧ Delete (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State),
      s.rip = BitVec.ofNat 64 A0 ∧ (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f) :=
  ⟨ME _, _, ME_laws _, delete_impl, AMap.empty, mstate64 mmem64 (args 7#64 0), rfl, by decide,
    mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret, trivial,
    (isMap_of_ne (by decide)).2 (mmem64_rep _)⟩

theorem clear_impl : Clear (toy.link (at0 retCode)) A0 (ME (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap⟩ := hpre
  have hf := ME_empty hmap
  subst hf
  janus64_run
  exact MapStr.mapReturn64_of (ME _) 2 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) hmap

theorem clear_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Janus.Amd64.Segment),
    M.Laws ∧ Clear (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State),
      s.rip = BitVec.ofNat 64 A0 ∧ (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 2 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f) :=
  ⟨ME _, _, ME_laws _, clear_impl, AMap.empty, mstate64 mmem64 (args 7#64 0), rfl, by decide,
    mstate64_rtpre _ rfl rfl mmem64 rfl _ 2 (by decide) mmem64_zenv mmem64_guard mmem64_ret, trivial,
    (isMap_of_ne (by decide)).2 (mmem64_rep _)⟩

/-! ## Assignment (`MC`, the map empty) -/

/-- `mov $0x10800, %edx; movq $1, (%rdx); mov %rcx, 8(%rdx); lea 32(%rdx), %rax; ret`:
`used = 1`, the key, and the value slot `MP + 32`. -/
def assignCode : List Nat :=
  [0xba, 0x00, 0x08, 0x01, 0x00, 0x48, 0xc7, 0x02, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4a, 0x08,
   0x48, 0x8d, 0x42, 0x20, 0xc3]

theorem assign_impl : Assign (toy.link (at0 assignCode)) A0 (MC ck64) HAssign := by
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
    simp only [rtWrites, MapAmd64.calleeStack, MC_priv, MC_depth, priv0, List.append_nil, List.cons_append,
      List.nil_append]
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
  exact cell_assign ck64 _ (s.regs 1) (s.regs 14) (by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hm1)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide), Janus.Arm64.Memory.readLE_writeLE_self])
    (fun v => by
      show BitVec.ofNat 64 (Janus.Arm64.Memory.readLE _ (MP + 8) 8) = _
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide), Janus.Arm64.Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (s.regs 1).isLt]
      simp)
    ((hze.writeLE _ (by decide)).writeLE _ (by decide))

theorem assign_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Janus.Amd64.Segment)
    (H : RtReady), M.Laws ∧ Assign (toy.link impl) A0 M H ∧
      ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧ M.Rep s.mem (s.regs 3).toNat f ∧
        Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s) :=
  ⟨MC ck64, _, HAssign, MC_laws _, assign_impl, AMap.empty, mstate64 mmem64 (args 7#64 0), rfl,
    mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret, trivial,
    by decide, mmem64_repC _, hAssign_mmem64 _ _ _⟩

/-! ## `makemap_small` (`MC`, no map alive) -/

/-- `mov $0x10800, %eax; movq $1, 48(%rax); movq $0, (%rax); ret`: the map at `MP`, alive and
empty. -/
def makeCode : List Nat :=
  [0xb8, 0x00, 0x08, 0x01, 0x00, 0x48, 0xc7, 0x40, 0x30, 0x01, 0x00, 0x00, 0x00,
   0x48, 0xc7, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc3]

theorem makeSmall_impl : MakeSmall (toy.link (at0 makeCode)) A0 (MC ck64) HMake := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, hH⟩ := hpre
  obtain ⟨h0, hacc⟩ := hH
  rw [MC_priv, readLE_rtView0 (a := MP + 48) (n := 8) (by decide) (by decide)] at h0
  rw [rtView_accessible] at hacc
  simp only [MP] at hacc
  have hout' := hout
  simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true] at hout'
  janus64_run
  have hfr : MemFrame s.mem ((Janus.Arm64.Memory.writeLE s.mem 67632 8 1).writeLE 67584 8 0)
      (rtWrites (MC ck64) s 0 ++ []) := by
    simp only [rtWrites, MapAmd64.calleeStack, MC_priv, MC_depth, priv0, List.append_nil,
      List.cons_append, List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67632 : Nat) = MP + 48 from rfl] at hacc hfr ⊢
  refine MapStr.mapReturn64_of (MC ck64) 0 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
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

theorem makeSmall_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Janus.Amd64.Segment)
    (H : RtReady), M.Laws ∧ MakeSmall (toy.link impl) A0 M H ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre M 0 s ∧ Ready64 H M.priv [] s) :=
  ⟨MC ck64, _, HMake, MC_laws _, makeSmall_impl, mstate64 mmem64Dead (args 0 0), rfl,
    mstate64_rtpre _ rfl rfl mmem64Dead rfl _ 0 (by decide)
      (show ZEnv mmem64Dead from mmem64_zenv.writeLE _ (by decide)) mmem64Dead_guard mmem64Dead_ret,
    hMake_dead64 _ _ _⟩

/-! ## Iteration (`MEi`: `ME` whose iterators are writable) -/

/-- `ME` with an iterator relation that also records that the iterator struct is writable
(`IterNext`'s precondition says nothing else about it). -/
def MEi (K : Type) : MapModel K (BitVec 64) :=
  { ME K with Iter := fun m it _ _ ks => ks.length ≤ 1 ∧ m.accessible it iterSize true = true }

theorem MEi_laws (K : Type) : (MEi K).Laws where
  rep_frame := (ME_laws K).rep_frame
  iter_frame _ _ _ _ _ _ h ha := ⟨h.1, by rw [ha.accessible]; exact h.2⟩
  env_frame := (ME_laws K).env_frame
  len := (ME_laws K).len
  finite := (ME_laws K).finite

theorem MEi_empty {K : Type} {m : Janus.Arm64.Memory} {mp : Nat} {f : AMap K (BitVec 64)}
    (h : IsMap (MEi K) m mp f) : f = AMap.empty := ME_empty (K := K) h

/-- `mov (%rsp), %rdx; movq $0, (%rcx); lea 8(%rsp), %rsp; jmp *%rdx`: the iteration is over
(key pointer `0`). The return address is loaded before the store, since the contract lets the
iterator struct overlap the return-address slot. -/
def iterStartCode : List Nat :=
  [0x48, 0x8b, 0x14, 0x24, 0x48, 0xc7, 0x01, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x64, 0x24, 0x08,
   0xff, 0xe2]

theorem iterStart_impl : IterStart (toy.link (at0 iterStartCode)) A0 (MEi (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap, hit, hpo, hco⟩ := hpre
  have hf := MEi_empty hmap
  subst hf
  have hit' := hit
  simp only [iterSize] at hit'
  have hp8 : Outside (s.regs 1).toNat 8 priv0 := Outside.of_sub hpo (by omega) (by simp [iterSize])
  have hag := Janus.Spec.Map.agrees_writeLE s.mem 0 hp8
  janus64_run
  have hfr : MemFrame s.mem (Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 1)) 8 0)
      (rtWrites (MEi (BitVec 64)) s 3 ++ [((s.regs 1).toNat, (s.regs 1).toNat + iterSize)]) := by
    simp only [rtWrites, MapAmd64.calleeStack, iterSize]
    simp only [MEi, ME_priv, ME_depth, priv0, List.cons_append, List.nil_append]
    janus_frame
  refine MapStr.mapReturn64_of (MEi _) 3 _ _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl hfr
    ((MEi_laws _).env_frame _ _ _ hze hag)
    (fun _ _ _ h => (MEi_laws _).rep_frame _ _ _ _ h hag)
    ⟨IsMap.frame (MEi_laws _) hmap hag, [], keys_empty,
      ⟨by decide, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hit⟩, ?_⟩
  show Janus.Arm64.Memory.readLE _ _ 8 = 0
  rw [Janus.Arm64.Memory.readLE_writeLE_self]

theorem iterStart_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Janus.Amd64.Segment),
    M.Laws ∧ IterStart (toy.link impl) A0 M ∧ ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State),
      s.rip = BitVec.ofNat 64 A0 ∧ (s.regs 3).toNat ≠ 0 ∧
      (RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f ∧
        s.mem.accessible (s.regs 1).toNat iterSize true = true ∧
        Outside (s.regs 1).toNat iterSize M.priv ∧
        Outside (s.regs 1).toNat iterSize (Janus.Contracts.MapAmd64.calleeStack s M.depth 3) ∧
        Outside (s.regs 1).toNat iterSize (Janus.Contracts.MapAmd64.retSlot s)) :=
  ⟨MEi _, _, MEi_laws _, iterStart_impl, AMap.empty, mstate64 mmem64 (args (BitVec.ofNat 64 IT) 0), rfl,
    by decide, mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    trivial, (isMap_of_ne (by decide)).2 (mmem64_rep _), by decide,
    by simp only [MEi, ME_priv, priv0, outside_cons, outside_nil, and_true]; decide,
    by simp only [Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]; decide,
    by simp only [Janus.Contracts.MapAmd64.retSlot, outside_cons, outside_nil, and_true]; decide⟩

/-- `mov (%rsp), %rdx; movq $0, (%rax); lea 8(%rsp), %rsp; jmp *%rdx`: the iteration is over. -/
def iterNextCode : List Nat :=
  [0x48, 0x8b, 0x14, 0x24, 0x48, 0xc7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x64, 0x24, 0x08,
   0xff, 0xe2]

theorem iterNext_impl : IterNext (toy.link (at0 iterNextCode)) A0 (MEi (BitVec 64)) := by
  rw [link_at0]
  intro mp f k ks s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, hmap, ⟨hlen, hit⟩, hpo, hco⟩ := hpre
  have hks : ks = [] := by
    cases ks with
    | nil => rfl
    | cons _ _ => simp at hlen
  subst hks
  have hit' := hit
  simp only [iterSize] at hit'
  have hp8 : Outside (s.regs 0).toNat 8 priv0 := Outside.of_sub hpo (by omega) (by simp [iterSize])
  have hag := Janus.Spec.Map.agrees_writeLE s.mem 0 hp8
  janus64_run
  have hfr : MemFrame s.mem (Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 0)) 8 0)
      (rtWrites (MEi (BitVec 64)) s 1 ++ [((s.regs 0).toNat, (s.regs 0).toNat + iterSize)]) := by
    simp only [rtWrites, MapAmd64.calleeStack, iterSize]
    simp only [MEi, ME_priv, ME_depth, priv0, List.cons_append, List.nil_append]
    janus_frame
  refine MapStr.mapReturn64_of (MEi _) 1 _ _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl hfr
    ((MEi_laws _).env_frame _ _ _ hze hag)
    (fun _ _ _ h => (MEi_laws _).rep_frame _ _ _ _ h hag)
    ⟨IsMap.frame (MEi_laws _) hmap hag,
      ⟨by decide, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hit⟩, ?_⟩
  show Janus.Arm64.Memory.readLE _ _ 8 = 0
  rw [Janus.Arm64.Memory.readLE_writeLE_self]

theorem iterNext_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Janus.Amd64.Segment),
    M.Laws ∧ IterNext (toy.link impl) A0 M ∧ ∃ (mp : Nat) (f : AMap (BitVec 64) (BitVec 64))
      (k : BitVec 64) (ks : List (BitVec 64)) (s : State), s.rip = BitVec.ofNat 64 A0 ∧ mp ≠ 0 ∧
      (RTPre M 1 s ∧ IsMap M s.mem mp f ∧ M.Iter s.mem (s.regs 0).toNat mp f (k :: ks) ∧
        Outside (s.regs 0).toNat iterSize M.priv ∧
        Outside (s.regs 0).toNat iterSize (Janus.Contracts.MapAmd64.calleeStack s M.depth 1) ∧
        Outside (s.regs 0).toNat iterSize (Janus.Contracts.MapAmd64.retSlot s)) :=
  ⟨MEi _, _, MEi_laws _, iterNext_impl, MP, AMap.empty, 0, [],
    mstate64 mmem64 (fun i => if i = 0 then BitVec.ofNat 64 IT else 0), rfl, by decide,
    mstate64_rtpre _ rfl rfl mmem64 rfl _ 1 (by decide) mmem64_zenv mmem64_guard mmem64_ret,
    (isMap_of_ne (by decide)).2 (mmem64_rep _), ⟨by decide, by decide⟩,
    by simp only [MEi, ME_priv, priv0, outside_cons, outside_nil, and_true]; decide,
    by simp only [Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]; decide,
    by simp only [Janus.Contracts.MapAmd64.retSlot, outside_cons, outside_nil, and_true]; decide⟩

end Janus.Contracts.MapSatAmd64
