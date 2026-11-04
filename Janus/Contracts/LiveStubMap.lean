import Janus.Contracts.LiveStub
import Janus.Contracts.MapSat

/-!
# Map runtime stubs at a program's own contract addresses (arm64)

The stubs of `MapSat` (one empty non-nil map for lookups, `delete` and `clear`: `ME`; at most one
entry for `mapassign_fast64` and `makemap_small`: `MC`), placed where an extracted program says the
runtime function is, and the tactics that prove the contract for them: each is the proof of
`MapSat.<contract>_impl` with `rw [link_at0]` replaced by `change ReachesRet _ _ s _`, run by
the executor at the real address (the stub code is position independent). Used for the
non-vacuity witnesses of theorems that assume these contracts (see `docs/RUNTIME-CONTRACTS.md`). The linked
program must be a closed constant (`def linked := Extracted.program.link segs`), the address a numeral
constant (`def cA := janus_eval% (Extracted.program.contractAddr "runtime.…")`). Nothing is trusted:
every contract is an ordinary kernel-checked theorem; no axiom is added.
-/

namespace Janus.Contracts.LiveStubMap

def mk (nm : String) (addr : Nat) (ws : List Nat) : Janus.Segment := ⟨nm, addr, ws⟩

/-- `runtime.mapaccess1*/mapaccess2*`: return the zero slot (and `false`). -/
def accessSeg (addr : Nat) : Janus.Segment := mk "live-stub.mapaccess" addr Janus.Contracts.MapSat.zsCode
/-- `runtime.mapassign_fast64`: store the key and return the slot. -/
def assignSeg (addr : Nat) : Janus.Segment := mk "live-stub.mapassign" addr MapSat.assignCode
/-- `runtime.makemap_small`. -/
def makeSmallSeg (addr : Nat) : Janus.Segment := mk "live-stub.makemap" addr MapSat.makeCode
/-- `runtime.mapdelete_fast64`, `runtime.mapclear`: `ret`. -/
def retSeg (addr : Nat) : Janus.Segment := mk "live-stub.mapret" addr Janus.Contracts.MapSat.retCode

/-- The witness memory `m` with a program data segment `d` added (read-only, at its own address, which the
caller keeps clear of `m`'s regions). -/
def withData (m : Janus.Arm64.Memory) (d : Janus.DataSegment) : Janus.Arm64.Memory :=
  ⟨fun a => if d.base ≤ a ∧ a < d.base + d.bytes.length then BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
      else m.bytes a, m.regions ++ [⟨d.base, d.bytes.length, false⟩]⟩

/-- `runtime.mapaccess1_fast64` in the one-entry model `MC`: the value slot `MP + 32` when `m = MP`, the cell is
used and its key is `k`; else the zero slot. -/
def access1McCode : List Nat :=
  [0xd2810004, 0xf2a00024, 0xeb04003f, 0x54000101, 0xf9400085, 0xb40000c5, 0xf9400486, 0xeb0200df,
   0x54000061, 0x91008080, 0xd65f03c0, 0xd2812000, 0xf2a00020, 0xd65f03c0]
def access1McSeg (addr : Nat) : Janus.Segment := ⟨"live-stub.mapaccess1mc", addr, access1McCode⟩

open Janus Janus.Spec.Map Janus.Contracts.MapModel0 in
theorem readLE8_lt (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 8 < 2 ^ 64 := by
  simpa using Janus.Arm64.Memory.readLE_lt m a 8

open Janus Janus.Spec.Map Janus.Contracts.MapModel0 in
theorem key_ne (m : Janus.Arm64.Memory) (x : BitVec 64) (h : ¬ m.readLE (MP + 8) 8 = x.toNat) :
    ¬ x = ck64.get m := by
  intro hx
  apply h
  have := congrArg BitVec.toNat hx
  simp only [ck64, BitVec.toNat_ofNat] at this
  rw [this, Nat.mod_eq_of_lt (readLE8_lt m _)]

open Janus Janus.Spec.Map Janus.Contracts.MapModel0 in
theorem key_eq (m : Janus.Arm64.Memory) (x : BitVec 64) (h : m.readLE (MP + 8) 8 = x.toNat) :
    x = ck64.get m := by
  apply BitVec.eq_of_toNat_eq
  simp only [ck64, BitVec.toNat_ofNat]
  rw [h, Nat.mod_eq_of_lt x.isLt]

end Janus.Contracts.LiveStubMap

/-- The proof of `MapSat.access1_impl` against the stub at the real address. -/
syntax "janus_map_access1" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_map_access1) => `(tactic| (
      open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapModel0
        Janus.Contracts.IfaceSat Janus.Contracts.MapSat in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
      obtain ⟨hl1, hl2, -⟩ := hc
      have hf := ME_empty hmap
      subst hf
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      refine mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
        (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, ?_⟩
      simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
      exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩
      )))

/-- The proof of `MapSat.access2_impl` against the stub at the real address. -/
syntax "janus_map_access2" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_map_access2) => `(tactic| (
      open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapModel0
        Janus.Contracts.IfaceSat Janus.Contracts.MapSat in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
      obtain ⟨hl1, hl2, -⟩ := hc
      have hf := ME_empty hmap
      subst hf
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      refine mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
        (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, ?_, ?_⟩
      · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
        exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩
      · simp [setReg, AMap.empty]
      )))

/-- The proof of `MapSat.access2Ptr_impl` against the stub at the real address. -/
syntax "janus_map_access2ptr" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_map_access2ptr) => `(tactic| (
      open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapModel0
        Janus.Contracts.IfaceSat Janus.Contracts.MapSat in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap, -⟩ := hpre
      obtain ⟨hl1, hl2, -⟩ := hc
      have hf := ME_empty hmap
      subst hf
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      refine mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
        (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, ?_, ?_⟩
      · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
        exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [AMap.empty, ZS] using hze.2⟩
      · simp [setReg, AMap.empty]
      )))

/-- The proof of `MapSat.assign_impl` against the stub at the real address. -/
syntax "janus_map_assign" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_map_assign) => `(tactic| (
      open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapModel0
        Janus.Contracts.IfaceSat Janus.Contracts.MapSat in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
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
      change Janus.Tactic.ReachesRet _ _ s _
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
      )))

/-- The proof of `MapSat.makeSmall_impl` against the stub at the real address. -/
syntax "janus_map_makesmall" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_map_makesmall) => `(tactic| (
      open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapModel0
        Janus.Contracts.IfaceSat Janus.Contracts.MapSat in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro s hpc hpre
      obtain ⟨⟨hze, hg, hc, hout⟩, hH⟩ := hpre
      obtain ⟨hl1, hl2, -⟩ := hc
      obtain ⟨h0, hacc⟩ := hH
      rw [MC_priv, readLE_rtView0 (a := MP + 48) (n := 8) (by decide) (by decide)] at h0
      rw [rtView_accessible] at hacc
      simp only [MP] at hacc
      change Janus.Tactic.ReachesRet _ _ s _
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
      )))

/-- The proof of `MapSat.delete_impl` against the stub at the real address. -/
syntax "janus_map_delete" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_map_delete) => `(tactic| (
      open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapModel0
        Janus.Contracts.IfaceSat Janus.Contracts.MapSat in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
      obtain ⟨hl1, hl2, -⟩ := hc
      have hf := ME_empty hmap
      subst hf
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      refine mapReturn_of (ME _) 3 [] _ s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) hze
        (fun _ _ _ h => h) ?_
      rw [erase_empty]; exact hmap
      )))

/-- The proof of `MapSat.clear_impl` against the stub at the real address. -/
syntax "janus_map_clear" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_map_clear) => `(tactic| (
      open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapModel0
        Janus.Contracts.IfaceSat Janus.Contracts.MapSat in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
      obtain ⟨hl1, hl2, -⟩ := hc
      have hf := ME_empty hmap
      subst hf
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      exact mapReturn_of (ME _) 2 [] _ s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) hze
        (fun _ _ _ h => h) hmap
      )))

/-- `Access1` for the one-entry model `MC ck64` against `LiveStubMap.access1McSeg`: the proof by cases on
`m = 0`, the `used` word and the key (the stub branches on them; each branch is run by the executor). -/
syntax "janus_map_access1mc" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_map_access1mc) => `(tactic| (
      open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
        Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapModel0
        Janus.Contracts.IfaceSat Janus.Contracts.MapSat in
      open Janus.Contracts.IfaceModel (wsp wg wret acc_read_of_write) in
      (
      intro f s hpc hpre
      obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
      obtain ⟨hl1, hl2, -⟩ := hc
      change Janus.Tactic.ReachesRet _ _ s _
      by_cases h0 : (s.regs 1).toNat = 0
      · have hf : f = AMap.empty := by simpa [IsMap, h0] using hmap
        have hx : s.regs 1 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h0)
        janus_run [hx]
        refine mapReturn_of (MC ck64) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
          (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h)
          ⟨by simpa [hx] using hmap, ?_⟩
        simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
        exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [hf, AMap.empty, ZS] using hze.2⟩
      · have hrep : (MC ck64).Rep s.mem (s.regs 1).toNat f := by simpa [IsMap, h0] using hmap
        obtain ⟨hmp, hacc, hal, hu⟩ := hrep
        have hx : s.regs 1 = 67584#64 := BitVec.eq_of_toNat_eq (by rw [hmp]; decide)
        have hmap' : IsMap (MC ck64) s.mem 67584 f := by rw [hx] at hmap; simpa using hmap
        have hacc' : s.mem.accessible 67584 56 true = true := hacc
        rcases hu with ⟨hu0, hf⟩ | ⟨hu1, hf⟩
        · have hu0' : s.mem.readLE 67584 8 = 0 := hu0
          janus_run [hx]
          refine mapReturn_of (MC ck64) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
            (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap', ?_⟩
          simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
          exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [hf, AMap.empty, ZS] using hze.2⟩
        · have hu1' : s.mem.readLE 67584 8 = 1 := hu1
          by_cases hk : s.mem.readLE 67592 8 = (s.regs 2).toNat
          · janus_run [hx]
            refine mapReturn_of (MC ck64) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
              (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap', ?_⟩
            have hkey : s.regs 2 = ck64.get s.mem := Janus.Contracts.LiveStubMap.key_eq s.mem _ hk
            have hv : (cellMap ck64 s.mem (s.regs 2)).getD 0#64 = BitVec.ofNat 64 (s.mem.readLE (MP + 32) 8) := by
              simp [cellMap, ← hkey]
            have hacr : s.mem.accessible 67584 56 false = true := Janus.Contracts.IfaceModel.acc_read_of_write hacc'
            have hslot : s.mem.accessible 67616 8 false = true := Memory.accessible_mono _ hacr (by decide) (by decide)
            simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reduceMod, hf, hv]
            refine ⟨by simpa using hslot, inPriv0 (by decide) (by decide), ?_⟩
            first
              | exact (Nat.mod_eq_of_lt (Janus.Contracts.LiveStubMap.readLE8_lt _ 67616)).symm
              | exact (Nat.mod_eq_of_lt (Janus.Contracts.LiveStubMap.readLE8_lt _ (MP + 32))).symm
          · janus_run [hx]
            refine mapReturn_of (MC ck64) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
              (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap', ?_⟩
            have hn : (cellMap ck64 s.mem (s.regs 2)) = none := by
              simp [cellMap, Janus.Contracts.LiveStubMap.key_ne s.mem _ hk]
            simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hf, hn]
            exact ⟨hze.1, inPriv0 (by decide) (by decide), by simpa [ZS] using hze.2⟩
      )))
