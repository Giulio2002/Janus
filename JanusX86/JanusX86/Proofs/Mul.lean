import JanusX86.Proofs.Jcc32

/-! # MUL (`F6/F7 /4`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem mul_spec_eq {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (x y : BitVec w) :
    mul_spec (w / 8) (x.setWidth 64) (y.setWidth 64) =
      ((BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w)).setWidth 64, (BitVec.ofNat w (x.toNat * y.toNat)).setWidth 64,
        BitVec.ofNat 128 (x.toNat * y.toNat)) := by
  have hx := x.isLt
  have hy := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ (2 * w) := by
    rw [show 2 * w = w + w by omega, Nat.pow_add]; exact Nat.mul_lt_mul'' hx hy
  have hc : ((x.toNat : Int) * (y.toNat : Int)) = ((x.toNat * y.toNat : Nat) : Int) := by push_cast; rfl
  rcases hw with rfl | rfl | rfl | rfl <;>
  simp only [mul_spec, mul_spec_8, mul_spec_16, mul_spec_32, mul_spec_64, Nat.reduceDiv, Prod.mk.injEq] <;>
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
  simp [Sail.BitVec.extractLsb, Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt,
    BitVec.extractLsb_toNat, bits_of_int_natCast_toNat, Nat.shiftRight_eq_div_pow] <;>
  rw [hc, bits_of_int_natCast_toNat, Nat.mod_eq_of_lt (a := x.toNat * y.toNat) (by simp only [Nat.reducePow, Nat.reduceMul] at hxy ⊢; exact hxy)] <;> omega

/-- The flags `MUL`/`IMUL` (one operand) write: `CF = OF = c`, `PF AF ZF SF` from the undefined source. -/
def mfl (r : BitVec 32) (c : BitVec 1) (u : Nat) : BitVec 32 :=
  _update_rflagsbits_of (_update_rflagsbits_sf (_update_rflagsbits_zf (_update_rflagsbits_af
    (_update_rflagsbits_pf (_update_rflagsbits_cf r c) (bits_of_int (u : Int) 1)) (bits_of_int (u : Int) 1))
    (bits_of_int (u : Int) 1)) (bits_of_int (u : Int) 1)) c

/-- Janus' flags after `MUL`/`IMUL`: `CF = OF = ovf`, the rest undefined. -/
def mulFlags (ovf : Bool) : Janus.Amd64.Flags :=
  { cf := some ovf, ovf := some ovf, sf := none, zf := none, af := none, pf := none }

theorem flagsRel_mfl {f0 : Janus.Amd64.Flags} {df : Bool} {r : BitVec 32} (hr : FlagsRel f0 df r) (ovf : Bool) (u : Nat) :
    FlagsRel (mulFlags ovf) df (mfl r (BitVec.ofBool ovf) u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [mfl, mulFlags, rf_get_cf_upd_cf, rf_get_cf_upd_pf, rf_get_cf_upd_af, rf_get_cf_upd_zf, rf_get_cf_upd_sf,
    rf_get_cf_upd_of, rf_get_of_upd_of, rf_get_df_upd_cf, rf_get_df_upd_pf, rf_get_df_upd_af, rf_get_df_upd_zf,
    rf_get_df_upd_sf, rf_get_df_upd_of, rf_get_ac_upd_cf, rf_get_ac_upd_pf, rf_get_ac_upd_af, rf_get_ac_upd_zf,
    rf_get_ac_upd_sf, rf_get_ac_upd_of]
  all_goals first | exact hr.df | exact hr.ac | (intro v hv; cases hv; rfl) | (intro v hv; cases hv)

set_option maxHeartbeats 4000000 in
theorem run_mul {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0xF6 ∨ opc = 0xF7) {w : Nat} (hw : w = if opc = 0xF6 then 8 else osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (V : BitVec w) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_mul .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (((if w = 8 then js.putReg 16 0 (BitVec.ofNat 16 ((js.getReg w 0).toNat * V.toNat))
          else (js.putReg w 0 (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat))).putReg w 2
            (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w))).setFlags
          (mulFlags (decide (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w) ≠ 0)))).setRip
          (BitVec.ofNat 64 (tr + inc))) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hl := hc.log
  have hb : (BitVec.ofNat 8 opc == 0xF6#8) = decide (opc % 2 = 0) := by rcases hopc with rfl | rfl <;> decide
  have hsz : (if decide (opc % 2 = 0) = true then (1 : Int) else if rexW p = true then 8
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    have := size_int p (decide (opc % 2 = 0)); simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [this, hw]; rcases hopc with rfl | rfl <;> simp
  simp only [x86_mul, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hb, hsz, hsg, Int.toNat_natCast,
    ← bits3_zero, hX sg hsg4 hsg5, run_add_inc tr inc hinc htr, hlen, is_some, Bool.false_eq_true, ↓reduceIte,
    run_pure, nbytes_eq _ hW, run_rgfi_size h hW _ rex hrex (n := 0) (by decide) (Or.inl (by decide)), trunc128,
    mul_spec_eq hW, regLocOf_zero]
  simp only [regVal]
  have hXlt : (js.getReg w 0).toNat * V.toNat < 2 ^ (2 * w) := by
    rw [show 2 * w = w + w by omega, Nat.pow_add]; exact Nat.mul_lt_mul'' (js.getReg w 0).isLt V.isLt
  have hcb : ∀ hi : BitVec w, (hi.setWidth 64 == 0#64) = decide (hi = 0) := by
    intro hi
    have h64 : w ≤ 64 := by omega
    have hlt := hi.isLt
    have : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h64
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro e; apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_setWidth, BitVec.toNat_zero, Nat.mod_eq_of_lt (show hi.toNat < 2 ^ 64 by omega)] at this
      simpa using this
    · intro e; subst e; simp
  have hcbit : ∀ hi : BitVec w, (if (hi.setWidth 64 == 0#64) = true then (0#1 : BitVec 1) else 1#1) =
      BitVec.ofBool (decide (hi ≠ 0)) := by
    intro hi; rw [hcb]; by_cases e : hi = 0 <;> simp only [e, decide_true, decide_false, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true] <;> rfl
  have hu' : ∀ (t : SState), t.regs.get? .janus_undef = some u → ∀ v : BitVec 32,
      (t.set .rflags v).regs.get? .janus_undef = some u := fun t ht v => by
    rw [get?_set_ne _ _ (by decide)]; exact ht
  have hflags : ∀ (t : SState) (rt : BitVec 32), t.regs.get? .rflags = some rt → t.regs.get? .janus_undef = some u →
      ∀ c : BitVec 1, (do
        let rflags_var ← readReg Register.rflags
        writeReg Register.rflags (_update_rflagsbits_cf rflags_var c)
        let rflags_var ← readReg Register.rflags
        let sailval ← undef_flg ()
        writeReg Register.rflags (_update_rflagsbits_pf rflags_var sailval)
        let rflags_var ← readReg Register.rflags
        let sailval ← undef_flg ()
        writeReg Register.rflags (_update_rflagsbits_af rflags_var sailval)
        let rflags_var ← readReg Register.rflags
        let sailval ← undef_flg ()
        writeReg Register.rflags (_update_rflagsbits_zf rflags_var sailval)
        let rflags_var ← readReg Register.rflags
        let sailval ← undef_flg ()
        writeReg Register.rflags (_update_rflagsbits_sf rflags_var sailval)
        let rflags_var ← readReg Register.rflags
        writeReg Register.rflags (_update_rflagsbits_of rflags_var c) : SailM Unit).run t =
        .ok () (t.set .rflags (mfl rt c u)) := by
    intro t rt hrt hut c
    rw [← set_self hrt]
    simp only [run_bind, run_readReg (get?_set_same _ _ _), run_writeReg, set_set, run_undef_flg (hu' _ hut _), mfl]
  rcases hW with rfl | hW16
  · simp only [show ((8 / 8 : Nat) : Int) = 1 from rfl]
    have hv16 : Sail.BitVec.truncate (BitVec.ofNat 128 ((js.getReg 8 0).toNat * V.toNat)) 64 =
        (BitVec.ofNat 16 ((js.getReg 8 0).toNat * V.toNat)).setWidth 64 := by
      apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate]; omega
    have hw16 := run_write_rgfi_size h hl (w := 16) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide))
      (BitVec.ofNat 16 ((js.getReg 8 0).toNat * V.toNat))
    simp only [regLocOf_zero, Nat.reduceDiv] at hw16
    rw [hv16, show (2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl, show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl,
      run_bind, hw16]
    simp only []
    generalize hV0 : (regWrite js 16 (Janus.Amd64.Loc.reg 0) (BitVec.ofNat 16 ((js.getReg 8 0).toNat * V.toNat))).regs
      (locReg (Janus.Amd64.Loc.reg 0)) = V0
    have hr1 : (setGpr s V0 (locReg (.reg 0))).regs.get? .rflags = some rf := by
      rw [get?_setGpr_of_not s V0 (by decide) rfl]; exact hr
    have hu1 : (setGpr s V0 (locReg (.reg 0))).regs.get? .janus_undef = some u := by
      rw [get?_setGpr_of_not s V0 (by decide) rfl]; exact hu
    have hl1 : (setGpr s V0 (locReg (.reg 0))).regs.get? .log_register_writes = some false := by
      rw [get?_setGpr_of_not s V0 (by decide) rfl]; exact hl
    have hc1 := hc.setGpr (r := locReg (.reg 0)) (by decide) V0
    have hrel1 := h.writeReg (w := 16) false (n := 0) (by decide) (BitVec.ofNat 16 ((js.getReg 8 0).toNat * V.toNat))
    simp only [regLocOf_zero, hV0] at hrel1
    have hcv := hcbit (BitVec.ofNat 8 ((js.getReg 8 0).toNat * V.toNat / 2 ^ 8))
    have hfr' : FlagsRel (mulFlags (decide (BitVec.ofNat 8 ((js.getReg 8 0).toNat * V.toNat / 2 ^ 8) ≠ 0))) 
        (regWrite js 16 (Janus.Amd64.Loc.reg 0) (BitVec.ofNat 16 ((js.getReg 8 0).toNat * V.toNat))).df
        (mfl rf (BitVec.ofBool (decide (BitVec.ofNat 8 ((js.getReg 8 0).toNat * V.toNat / 2 ^ 8) ≠ 0))) u) := by
      rw [regWrite_df]; exact flagsRel_mfl hfr _ u
    by_cases hz : (BitVec.setWidth 64 (BitVec.ofNat 8 ((js.getReg 8 0).toNat * V.toNat / 2 ^ 8)) == 0#64) = true
    · simp only [hz, ↓reduceIte] at hcv ⊢
      rw [run_bind, hflags _ _ hr1 hu1 (0#1)]
      simp only []
      refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl1) _ htr, ?_, (hc1.set (by decide) _).set (by decide) _⟩
      rw [hcv]; exact hrel1.flagsRip _ _ hfr' _
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hcv ⊢
      rw [run_bind, hflags _ _ hr1 hu1 (1#1)]
      simp only []
      refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl1) _ htr, ?_, (hc1.set (by decide) _).set (by decide) _⟩
      rw [hcv]; exact hrel1.flagsRip _ _ hfr' _
  · have hw8 : w ≠ 8 := by omega
    have hW' : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := Or.inr hW16
    have hm1 : ((w / 8 : Nat) : Int) ≠ 1 := by omega
    split
    · rename_i h1'; exact absurd h1' hm1
    simp only [hw8, ↓reduceIte]
    have hrl : ∀ k, regLocOf p.rex.isSome w k = .reg k := fun k => by unfold regLocOf; rw [if_neg hw8]
    have hwa := run_write_rgfi_size h hl hW' _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat))
    simp only [hrl] at hwa
    rw [run_bind, run_bind, hwa]
    simp only []
    generalize hV0 : (regWrite js w (Janus.Amd64.Loc.reg 0) (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat))).regs (locReg (Janus.Amd64.Loc.reg 0)) = V0
    have hrel1 := h.writeReg (w := w) p.rex.isSome (n := 0) (by decide) (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat))
    simp only [hrl, hV0] at hrel1
    have hl1 : (setGpr s V0 (locReg (.reg 0))).regs.get? .log_register_writes = some false := by
      rw [get?_setGpr_of_not s V0 (by decide) rfl]; exact hl
    have hwd := run_write_rgfi_size hrel1 hl1 hW' _ rex hrex (n := 2) (by decide) (Or.inl (by decide)) (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w))
    simp only [hrl] at hwd
    rw [show (0x2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl, hwd]
    simp only []
    generalize hV2 : (regWrite (regWrite js w (Janus.Amd64.Loc.reg 0) (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat))) w (Janus.Amd64.Loc.reg 2) (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w))).regs
      (locReg (Janus.Amd64.Loc.reg 2)) = V2
    have hrel2 := hrel1.writeReg (w := w) p.rex.isSome (n := 2) (by decide) (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w))
    simp only [hrl, hV2] at hrel2
    generalize hs2 : setGpr (setGpr s V0 (locReg (.reg 0))) V2 (locReg (.reg 2)) = s2 at hrel2 ⊢
    have hr2 : s2.regs.get? .rflags = some rf := by
      rw [← hs2, get?_setGpr_of_not _ V2 (by decide) rfl, get?_setGpr_of_not s V0 (by decide) rfl]; exact hr
    have hu2 : s2.regs.get? .janus_undef = some u := by
      rw [← hs2, get?_setGpr_of_not _ V2 (by decide) rfl, get?_setGpr_of_not s V0 (by decide) rfl]; exact hu
    have hl2' : s2.regs.get? .log_register_writes = some false := by
      rw [← hs2, get?_setGpr_of_not _ V2 (by decide) rfl, get?_setGpr_of_not s V0 (by decide) rfl]; exact hl
    have hc2 : X86Config s2 := by rw [← hs2]; exact (hc.setGpr (by decide) _).setGpr (by decide) _
    have hcv := hcbit (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w))
    have hfr' : FlagsRel (mulFlags (decide ((BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w)) ≠ 0)))
        (regWrite (regWrite js w (Janus.Amd64.Loc.reg 0) (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat))) w (Janus.Amd64.Loc.reg 2) (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w))).df
        (mfl rf (BitVec.ofBool (decide ((BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w)) ≠ 0))) u) := by
      rw [regWrite_df, regWrite_df]; exact flagsRel_mfl hfr _ u
    have hJ : (js.putReg w 0 (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat))).putReg w 2 (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w)) = regWrite (regWrite js w (Janus.Amd64.Loc.reg 0) (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat))) w (Janus.Amd64.Loc.reg 2) (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w)) := rfl
    rw [hJ]
    by_cases hz : (BitVec.setWidth 64 (BitVec.ofNat w ((js.getReg w 0).toNat * V.toNat / 2 ^ w)) == 0#64) = true
    · simp only [hz, ↓reduceIte] at hcv ⊢
      rw [run_bind, hflags _ _ hr2 hu2 (0#1)]
      simp only []
      refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl2') _ htr, ?_, (hc2.set (by decide) _).set (by decide) _⟩
      rw [hcv]; exact hrel2.flagsRip _ _ hfr' _
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hcv ⊢
      rw [run_bind, hflags _ _ hr2 hu2 (1#1)]
      simp only []
      refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl2') _ htr, ?_, (hc2.set (by decide) _).set (by decide) _⟩
      rw [hcv]; exact hrel2.flagsRip _ _ hfr' _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- The group-3 instruction with ModRM extension `e ∈ 4..7`. -/
def grp3 (e w : Nat) (D : Janus.Amd64.Loc) : Janus.Amd64.Instr :=
  if e = 4 then .mul1 false w D else if e = 5 then .mul1 true w D else if e = 6 then .div false w D else .div true w D

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_grp3 {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (ho : o = 0xF6 ∨ o = 0xF7) (hext : 4 ≤ m / 8 % 8)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {w : Nat} (hw : w = if o = 0xF6 then 8 else osz p)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ len = n + 1 + c ∧ len ≤ 15 ∧ i = grp3 (m / 8 % 8) w (rmDst p w mm.rm) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hex := modrm_ext hmd
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have ho8 : (osz p = 8) = False := by rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hex; subst hex
  have he : m / 8 % 8 = 4 ∨ m / 8 % 8 = 5 ∨ m / 8 % 8 = 6 ∨ m / 8 % 8 = 7 := by omega
  generalize hE : m / 8 % 8 = e at he hd ⊢
  rcases ho with rfl | rfl <;> rcases he with rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, true_and, and_true,
      false_and, and_false, or_false, false_or, ho8, finish, hE] at hd hw ⊢
    subst hw
    by_cases hl : 15 < n + 1 + c <;> by_cases hrp : p.rep = 0 <;>
      cases hf : p.fs <;> cases hk : p.lock <;> cases rm <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, rmDst, rmLoc, regLocOf, grp3, ho8] at hd ⊢ <;>
      (try simp [withFS, lockable] at hd ⊢)
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := hd; omega)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, by omega, rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; simp; omega)
      | (simp at hd; done)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_mul (opc : Nat) (hopc : opc = 0xF6 ∨ opc = 0xF7)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hm : _get_modr_m_reg m = BitVec.ofNat 3 4) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_mul .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases hopc with rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, hm, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **MUL r/m** (`F6/F7 /4`): every ModRM form and width; `AX` or `rDX:rAX`, `CF = OF`. -/
theorem mul_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o = 0xF6 ∨ o = 0xF7)
    (hext : m / 8 % 8 = 4)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  cases hmd : modrm (p.rex.getD 0) (m :: rest) with
  | none =>
    exfalso
    obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
    simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
    rcases ho with rfl | rfl <;> simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  generalize hw : (if o = 0xF6 then 8 else osz p) = w
  obtain ⟨hlk, hfs, hrep, rfl, hlen, rfl⟩ := decode_grp3 hpp ho (by omega) hmd hw.symm hd
  rw [step_of_decode hd] at hstep
  simp only [grp3, hext, ↓reduceIte, exec] at hstep
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [← hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  rw [hnext] at hstep
  unfold execMul1 at hstep
  cases hrd : readLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c)) w (rmDst p w mm.rm) with
  | error e => simp [hrd] at hstep
  | ok X =>
  obtain ⟨hok, rfl⟩ := readLoc_loc hrd
  simp only [hrd, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hstep
  subst hstep
  have hreg4 : _get_modr_m_reg (BitVec.ofNat 8 m) = BitVec.ofNat 3 4 := by rw [(modrm_fields m hm256).2.1, hext]
  refine rm_frame hrel hcfg hcode hlim hpp (by unfold prefixGroup; omega) (by omega) (by omega)
    (by rcases ho with rfl | rfl <;> decide) hlk hmd (fun _ _ => hfs) hW (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => x86_mul .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_one_byte_mul o ho sr tr x hl rex _ sib hreg4 s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr _ _ _
  obtain ⟨s', hs', hrel', hc'⟩ := run_mul hrel hcfg hpr hrv o ho hw.symm m hm256 sib tr _ inc eaddr
    (hX true false false hok) hinc8 js.rip.toNat (by omega) (by omega) (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  rw [hinc'] at hrel'
  have hF : ∀ F : Nat, F < 2 ^ 16 → (BitVec.ofNat 8 (F / 2 ^ 8)).toNat * 256 + (BitVec.ofNat 8 F).toNat = F := by
    intro F hF; simp; omega
  by_cases h8 : w = 8
  · subst h8
    simp only [↓reduceIte] at hrel' ⊢
    rw [hF _ (Nat.lt_of_lt_of_eq (Nat.mul_lt_mul'' (js.getReg 8 0).isLt (BitVec.isLt _)) (by decide))]
    exact hrel'
  · simp only [h8, ↓reduceIte] at hrel' ⊢; exact hrel'

end JanusX86.Proofs
