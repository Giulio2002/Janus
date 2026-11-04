import Janus.Contracts.LiveStub
import Janus.Contracts.LiveStubMap
import Janus.Contracts.MapSatAmd64

/-!
# Map runtime stubs at a program's own contract addresses (amd64)

The stubs of `MapSatAmd64` (one empty non-nil map for lookups, `delete` and `clear`: `ME`; at most one
entry for `mapassign_fast64` and `makemap_small`: `MC`), placed where an extracted program says the
runtime function is, and the tactics that prove the contract for them: each is the proof of
`MapSatAmd64.<contract>_impl` with `rw [link_at0]` replaced by `change ReachesRet _ _ s _`, run by
the executor at the real address (the stub code is position independent). Used for the
non-vacuity witnesses of theorems that assume these contracts (see `docs/RUNTIME-CONTRACTS.md`). The linked
program must be a closed constant (`def linked := Extracted.program.link segs`), the address a numeral
constant (`def cA := janus_eval% (Extracted.program.contractAddr "runtime.…")`). Nothing is trusted:
every contract is an ordinary kernel-checked theorem; no axiom is added.
-/

namespace Janus.Contracts.LiveStubMapAmd64

def mk (nm : String) (addr : Nat) (bs : List Nat) : Janus.Amd64.Segment := ⟨nm, addr, bs⟩

/-- `runtime.mapaccess1*/mapaccess2*`: return the zero slot (and `false`). -/
def accessSeg (addr : Nat) : Janus.Amd64.Segment := mk "live-stub.mapaccess" addr Janus.Contracts.MapSatAmd64.zsCode
/-- `runtime.mapassign_fast64`: store the key and return the slot. -/
def assignSeg (addr : Nat) : Janus.Amd64.Segment := mk "live-stub.mapassign" addr MapSatAmd64.assignCode
/-- `runtime.makemap_small`. -/
def makeSmallSeg (addr : Nat) : Janus.Amd64.Segment := mk "live-stub.makemap" addr MapSatAmd64.makeCode
/-- `runtime.mapdelete_fast64`, `runtime.mapclear`: `ret`. -/
def retSeg (addr : Nat) : Janus.Amd64.Segment := mk "live-stub.mapret" addr Janus.Contracts.MapSatAmd64.retCode

/-- `runtime.mapaccess1_fast64` in the one-entry model `MC` (amd64), as `LiveStubMap.access1McCode`. -/
def access1McCode : List Nat :=
  [0xba, 0x00, 0x08, 0x01, 0x00, 0x48, 0x39, 0xd3, 0x75, 0x16, 0x48, 0x8b, 0x32, 0x48, 0x85, 0xf6, 0x74, 0x0e,
   0x48, 0x8b, 0x72, 0x08, 0x48, 0x39, 0xce, 0x75, 0x05, 0x48, 0x8d, 0x42, 0x20, 0xc3, 0xb8, 0x00, 0x09, 0x01,
   0x00, 0x31, 0xdb, 0xc3]
def access1McSeg (addr : Nat) : Janus.Amd64.Segment := ⟨"live-stub.mapaccess1mc", addr, access1McCode⟩

end Janus.Contracts.LiveStubMapAmd64

/-- The proof of `MapSatAmd64.access1_impl` against the stub at the real address. -/
syntax "janus64_map_access1" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_map_access1) => `(tactic| (
      open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts.MapAmd64 Janus.Contracts.MapModel0 Janus.Contracts.IfaceSatAmd64
        Janus.Contracts.MapSatAmd64 Janus.Contracts in
      open Janus (MemFrame Outside outside_cons outside_nil InRanges) in
      open Janus.Contracts (RtReady rtView Ready64 readLE_rtView rtView_accessible) in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap⟩ := hpre
      have hf := ME_empty hmap
      subst hf
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      refine MapStr.mapReturn64_of (ME _) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
        (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
        (fun _ _ _ h => h) ⟨hmap, ?_⟩
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
      exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩
      )))

/-- The proof of `MapSatAmd64.access2_impl` against the stub at the real address. -/
syntax "janus64_map_access2" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_map_access2) => `(tactic| (
      open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts.MapAmd64 Janus.Contracts.MapModel0 Janus.Contracts.IfaceSatAmd64
        Janus.Contracts.MapSatAmd64 Janus.Contracts in
      open Janus (MemFrame Outside outside_cons outside_nil InRanges) in
      open Janus.Contracts (RtReady rtView Ready64 readLE_rtView rtView_accessible) in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap⟩ := hpre
      have hf := ME_empty hmap
      subst hf
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      refine MapStr.mapReturn64_of (ME _) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
        (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
        (fun _ _ _ h => h) ⟨hmap, ?_, ?_⟩
      · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
        exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩
      · simp [setRegF, AMap.empty]
      )))

/-- The proof of `MapSatAmd64.access2Ptr_impl` against the stub at the real address. -/
syntax "janus64_map_access2ptr" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_map_access2ptr) => `(tactic| (
      open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts.MapAmd64 Janus.Contracts.MapModel0 Janus.Contracts.IfaceSatAmd64
        Janus.Contracts.MapSatAmd64 Janus.Contracts in
      open Janus (MemFrame Outside outside_cons outside_nil InRanges) in
      open Janus.Contracts (RtReady rtView Ready64 readLE_rtView rtView_accessible) in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap, -⟩ := hpre
      have hf := ME_empty hmap
      subst hf
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      refine MapStr.mapReturn64_of (ME _) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
        (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
        (fun _ _ _ h => h) ⟨hmap, ?_, ?_⟩
      · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
        exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩
      · simp [setRegF, AMap.empty]
      )))

/-- The proof of `MapSatAmd64.assign_impl` against the stub at the real address. -/
syntax "janus64_map_assign" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_map_assign) => `(tactic| (
      open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts.MapAmd64 Janus.Contracts.MapModel0 Janus.Contracts.IfaceSatAmd64
        Janus.Contracts.MapSatAmd64 Janus.Contracts in
      open Janus (MemFrame Outside outside_cons outside_nil InRanges) in
      open Janus.Contracts (RtReady rtView Ready64 readLE_rtView rtView_accessible) in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
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
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
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
      )))

/-- The proof of `MapSatAmd64.makeSmall_impl` against the stub at the real address. -/
syntax "janus64_map_makesmall" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_map_makesmall) => `(tactic| (
      open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts.MapAmd64 Janus.Contracts.MapModel0 Janus.Contracts.IfaceSatAmd64
        Janus.Contracts.MapSatAmd64 Janus.Contracts in
      open Janus (MemFrame Outside outside_cons outside_nil InRanges) in
      open Janus.Contracts (RtReady rtView Ready64 readLE_rtView rtView_accessible) in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro s hpc hpre
      obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, hH⟩ := hpre
      obtain ⟨h0, hacc⟩ := hH
      rw [MC_priv, readLE_rtView0 (a := MP + 48) (n := 8) (by decide) (by decide)] at h0
      rw [rtView_accessible] at hacc
      simp only [MP] at hacc
      have hout' := hout
      simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true] at hout'
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
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
      )))

/-- The proof of `MapSatAmd64.delete_impl` against the stub at the real address. -/
syntax "janus64_map_delete" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_map_delete) => `(tactic| (
      open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts.MapAmd64 Janus.Contracts.MapModel0 Janus.Contracts.IfaceSatAmd64
        Janus.Contracts.MapSatAmd64 Janus.Contracts in
      open Janus (MemFrame Outside outside_cons outside_nil InRanges) in
      open Janus.Contracts (RtReady rtView Ready64 readLE_rtView rtView_accessible) in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap⟩ := hpre
      have hf := ME_empty hmap
      subst hf
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      refine MapStr.mapReturn64_of (ME _) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
        (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
        (fun _ _ _ h => h) ?_
      rw [erase_empty]; exact hmap
      )))

/-- The proof of `MapSatAmd64.clear_impl` against the stub at the real address. -/
syntax "janus64_map_clear" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_map_clear) => `(tactic| (
      open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts.MapAmd64 Janus.Contracts.MapModel0 Janus.Contracts.IfaceSatAmd64
        Janus.Contracts.MapSatAmd64 Janus.Contracts in
      open Janus (MemFrame Outside outside_cons outside_nil InRanges) in
      open Janus.Contracts (RtReady rtView Ready64 readLE_rtView rtView_accessible) in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap⟩ := hpre
      have hf := ME_empty hmap
      subst hf
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      exact MapStr.mapReturn64_of (ME _) 2 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
        (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
        (fun _ _ _ h => h) hmap
      )))

/-- `Access1` (amd64) for `MC ck64` against `LiveStubMapAmd64.access1McSeg`; as `janus_map_access1mc`. -/
syntax "janus64_map_access1mc" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_map_access1mc) => `(tactic| (
      open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts.MapAmd64 Janus.Contracts.MapModel0 Janus.Contracts.IfaceSatAmd64
        Janus.Contracts.MapSatAmd64 Janus.Contracts in
      open Janus (MemFrame Outside outside_cons outside_nil InRanges) in
      open Janus.Contracts (RtReady rtView Ready64 readLE_rtView rtView_accessible) in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap⟩ := hpre
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      by_cases h0 : (s.regs 3).toNat = 0
      · have hf : f = AMap.empty := by simpa [IsMap, h0] using hmap
        have hx : s.regs 3 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h0)
        janus64_run [hx]
        refine MapStr.mapReturn64_of (MC ck64) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
          (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
          (fun _ _ _ h => h) ⟨by simpa [hx] using hmap, ?_⟩
        simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
        exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [hf, AMap.empty, ZS] using hze.2⟩
      · have hrep : (MC ck64).Rep s.mem (s.regs 3).toNat f := by simpa [IsMap, h0] using hmap
        obtain ⟨hmp, hacc, hal', hu⟩ := hrep
        have hx : s.regs 3 = 67584#64 := BitVec.eq_of_toNat_eq (by rw [hmp]; decide)
        have hmap' : IsMap (MC ck64) s.mem 67584 f := by rw [hx] at hmap; simpa using hmap
        have hacc' : s.mem.accessible 67584 56 true = true := hacc
        rcases hu with ⟨hu0, hf⟩ | ⟨hu1, hf⟩
        · have hu0' : s.mem.readLE 67584 8 = 0 := hu0
          janus64_run [hx]
          refine MapStr.mapReturn64_of (MC ck64) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
            (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
            (fun _ _ _ h => h) ⟨hmap', ?_⟩
          simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
          exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [hf, AMap.empty, ZS] using hze.2⟩
        · have hu1' : s.mem.readLE 67584 8 = 1 := hu1
          by_cases hk : s.mem.readLE 67592 8 = (s.regs 1).toNat
          · have hkb : BitVec.ofNat 64 (s.mem.readLE 67592 8) = s.regs 1 := by rw [hk]; simp
            have hsub : (2 ^ 64 - (s.regs 1).toNat + s.mem.readLE 67592 8) % 2 ^ 64 = 0 := by
              have := (s.regs 1).isLt; rw [hk]; omega
            janus64_run [hx]
            refine MapStr.mapReturn64_of (MC ck64) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
              (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
              (fun _ _ _ h => h) ⟨hmap', ?_⟩
            have hkey : s.regs 1 = ck64.get s.mem := Janus.Contracts.LiveStubMap.key_eq s.mem _ hk
            have hv : (cellMap ck64 s.mem (s.regs 1)).getD 0#64 = BitVec.ofNat 64 (s.mem.readLE (MP + 32) 8) := by
              simp [cellMap, ← hkey]
            have hacr : s.mem.accessible 67584 56 false = true := Janus.Contracts.IfaceModel.acc_read_of_write hacc'
            have hslot : s.mem.accessible 67616 8 false = true := Janus.Arm64.Memory.accessible_mono _ hacr (by decide) (by decide)
            simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reduceMod, hf, hv]
            refine ⟨by simpa using hslot, inPriv0 (by decide) (by decide), ?_⟩
            first
              | exact (Nat.mod_eq_of_lt (Janus.Contracts.LiveStubMap.readLE8_lt _ 67616)).symm
              | exact (Nat.mod_eq_of_lt (Janus.Contracts.LiveStubMap.readLE8_lt _ (MP + 32))).symm
          · have hkb : ¬ BitVec.ofNat 64 (s.mem.readLE 67592 8) = s.regs 1 := by
              intro h; apply hk; have := congrArg BitVec.toNat h
              simp only [BitVec.toNat_ofNat] at this
              rwa [Nat.mod_eq_of_lt (Janus.Contracts.LiveStubMap.readLE8_lt _ _)] at this
            have hsub : ¬ (2 ^ 64 - (s.regs 1).toNat + s.mem.readLE 67592 8) % 2 ^ 64 = 0 := by
              have h1 := (s.regs 1).isLt; have h2 := Janus.Contracts.LiveStubMap.readLE8_lt s.mem 67592
              intro h; apply hk; omega
            janus64_run [hx]
            refine MapStr.mapReturn64_of (MC ck64) 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
              (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
              (fun _ _ _ h => h) ⟨hmap', ?_⟩
            have hn : (cellMap ck64 s.mem (s.regs 1)) = none := by
              simp [cellMap, Janus.Contracts.LiveStubMap.key_ne s.mem _ hk]
            simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hf, hn]
            exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [ZS] using hze.2⟩
      )))
