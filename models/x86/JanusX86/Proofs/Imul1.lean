import JanusX86.Proofs.Mul

/-! # IMUL r/m (one operand, `F6/F7 /5`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem prod_bound {w : Nat} (hw : 1 ≤ w) (x y : BitVec w) :
    (x.toInt * y.toInt).natAbs ≤ 2 ^ (w - 1) * 2 ^ (w - 1) := by
  rw [Int.natAbs_mul]
  have hx1 := BitVec.le_toInt x
  have hx2 : x.toInt < 2 ^ (w - 1) := BitVec.toInt_lt
  have hy1 := BitVec.le_toInt y
  have hy2 : y.toInt < 2 ^ (w - 1) := BitVec.toInt_lt
  have e : ((2 : Int) ^ (w - 1)) = ((2 ^ (w - 1) : Nat) : Int) := by push_cast; rfl
  apply Nat.mul_le_mul <;> omega


theorem imul_cf_8 (F : Int) (hb : F.natAbs ≤ 16384) :
    (bool_to_bits !Sail.BitVec.signExtend (Sail.BitVec.extractLsb (BitVec.ofInt 16 F) 7 0) 16 == BitVec.ofInt 16 F) =
    BitVec.ofBool (decide ((BitVec.ofInt 8 F).toInt ≠ F)) := by
  have key : (Sail.BitVec.signExtend (Sail.BitVec.extractLsb (BitVec.ofInt 16 F) 7 0) 16 == BitVec.ofInt 16 F) =
      decide ((BitVec.ofInt 8 F).toInt = F) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← BitVec.toInt_inj]
    simp only [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.toInt_signExtend_of_le (show 8 ≤ 16 by decide)]
    simp [BitVec.toInt_ofInt, BitVec.toInt, BitVec.extractLsb_toNat, Int.bmod]
    omega
  rw [key]; cases h : decide ((BitVec.ofInt 8 F).toInt = F) <;> simp_all <;> rfl

theorem imul_cf_16 (F : Int) (hb : F.natAbs ≤ 1073741824) :
    (bool_to_bits !Sail.BitVec.signExtend (Sail.BitVec.extractLsb (BitVec.ofInt 32 F) 15 0) 32 == BitVec.ofInt 32 F) =
    BitVec.ofBool (decide ((BitVec.ofInt 16 F).toInt ≠ F)) := by
  have key : (Sail.BitVec.signExtend (Sail.BitVec.extractLsb (BitVec.ofInt 32 F) 15 0) 32 == BitVec.ofInt 32 F) =
      decide ((BitVec.ofInt 16 F).toInt = F) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← BitVec.toInt_inj]
    simp only [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.toInt_signExtend_of_le (show 16 ≤ 32 by decide)]
    simp [BitVec.toInt_ofInt, BitVec.toInt, BitVec.extractLsb_toNat, Int.bmod]
    omega
  rw [key]; cases h : decide ((BitVec.ofInt 16 F).toInt = F) <;> simp_all <;> rfl

theorem imul_cf_32 (F : Int) (hb : F.natAbs ≤ 4611686018427387904) :
    (bool_to_bits !Sail.BitVec.signExtend (Sail.BitVec.extractLsb (BitVec.ofInt 64 F) 31 0) 64 == BitVec.ofInt 64 F) =
    BitVec.ofBool (decide ((BitVec.ofInt 32 F).toInt ≠ F)) := by
  have key : (Sail.BitVec.signExtend (Sail.BitVec.extractLsb (BitVec.ofInt 64 F) 31 0) 64 == BitVec.ofInt 64 F) =
      decide ((BitVec.ofInt 32 F).toInt = F) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← BitVec.toInt_inj]
    simp only [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.toInt_signExtend_of_le (show 32 ≤ 64 by decide)]
    simp [BitVec.toInt_ofInt, BitVec.toInt, BitVec.extractLsb_toNat, Int.bmod]
    omega
  rw [key]; cases h : decide ((BitVec.ofInt 32 F).toInt = F) <;> simp_all <;> rfl

theorem imul_cf_64 (F : Int) (hb : F.natAbs ≤ 85070591730234615865843651857942052864) :
    (bool_to_bits !Sail.BitVec.signExtend (Sail.BitVec.extractLsb (BitVec.ofInt 128 F) 63 0) 128 == BitVec.ofInt 128 F) =
    BitVec.ofBool (decide ((BitVec.ofInt 64 F).toInt ≠ F)) := by
  have key : (Sail.BitVec.signExtend (Sail.BitVec.extractLsb (BitVec.ofInt 128 F) 63 0) 128 == BitVec.ofInt 128 F) =
      decide ((BitVec.ofInt 64 F).toInt = F) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← BitVec.toInt_inj]
    simp only [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.toInt_signExtend_of_le (show 64 ≤ 128 by decide)]
    simp [BitVec.toInt_ofInt, BitVec.toInt, BitVec.extractLsb_toNat, Int.bmod]
    omega
  rw [key]; cases h : decide ((BitVec.ofInt 64 F).toInt = F) <;> simp_all <;> rfl

theorem imul_spec_eq {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (x y : BitVec w) :
    imul_spec (w / 8) (x.setWidth 64) (y.setWidth 64) =
      ((BitVec.ofInt w (x.toInt * y.toInt / (2 ^ w : Nat))).setWidth 64, (BitVec.ofInt w (x.toInt * y.toInt)).setWidth 64,
        (BitVec.ofInt (2 * w) (x.toInt * y.toInt)).setWidth 128,
        BitVec.ofBool (decide ((BitVec.ofInt w (x.toInt * y.toInt)).toInt ≠ x.toInt * y.toInt))) := by
  have hb := prod_bound (by omega) x y
  rcases hw with rfl | rfl | rfl | rfl <;>
  simp only [imul_spec, imul_spec_8, imul_spec_16, imul_spec_32, imul_spec_64, Nat.reduceDiv, Prod.mk.injEq,
    Sail.BitVec.truncate, sw_sw8, sw_sw16, sw_sw32, BitVec.setWidth_eq] <;>
  simp only [bits_of_int_eq_ofInt] <;>
  generalize x.toInt * y.toInt = F at hb ⊢ <;>
  simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hb <;>
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (apply BitVec.eq_of_toNat_eq
       simp [Sail.BitVec.extractLsb, Sail.BitVec.zeroExtend, BitVec.toNat_ofInt, BitVec.extractLsb_toNat,
         Nat.shiftRight_eq_div_pow]
       omega)
    | rfl
    | trivial
    | exact imul_cf_8 F hb
    | exact imul_cf_16 F hb
    | exact imul_cf_32 F hb
    | exact imul_cf_64 F hb

set_option maxHeartbeats 4000000 in
theorem run_imul1 {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0xF6 ∨ opc = 0xF7) {w : Nat} (hw : w = if opc = 0xF6 then 8 else osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (V : BitVec w) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_imul_op_en_m .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (((if w = 8 then js.putReg 16 0 (BitVec.ofInt 16 ((js.getReg w 0).toInt * V.toInt))
          else (js.putReg w 0 (BitVec.ofInt w ((js.getReg w 0).toInt * V.toInt))).putReg w 2
            (BitVec.ofInt w ((js.getReg w 0).toInt * V.toInt / (2 ^ w : Nat)))).setFlags
          (mulFlags (decide ((BitVec.ofInt w ((js.getReg w 0).toInt * V.toInt)).toInt ≠ (js.getReg w 0).toInt * V.toInt)))).setRip
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
  have hu' : ∀ (t : SState), t.regs.get? .janus_undef = some u → ∀ v : BitVec 32,
      (t.set .rflags v).regs.get? .janus_undef = some u := fun t ht v => by
    rw [get?_set_ne _ _ (by decide)]; exact ht
  have hflags : ∀ (t : SState) (rt : BitVec 32), t.regs.get? .rflags = some rt → t.regs.get? .janus_undef = some u →
      ∀ (c : BitVec 1) (k : SailM Unit), (do
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
        writeReg Register.rflags (_update_rflagsbits_of rflags_var c)
        k : SailM Unit).run t = k.run (t.set .rflags (mfl rt c u)) := by
    intro t rt hrt hut c k
    rw [← set_self hrt]
    simp only [run_bind, run_readReg (get?_set_same _ _ _), run_writeReg, set_set, run_undef_flg (hu' _ hut _), mfl]
  simp only [x86_imul_op_en_m, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hb, hsz, hsg, Int.toNat_natCast,
    ← bits3_zero, hX sg hsg4 hsg5, run_add_inc tr inc hinc htr, hlen, is_some, Bool.false_eq_true, ↓reduceIte,
    run_pure, nbytes_eq _ hW, run_rgfi_size h hW _ rex hrex (n := 0) (by decide) (Or.inl (by decide)), trunc128,
    imul_spec_eq hW, regLocOf_zero]
  simp only [regVal]
  have hfr' : ∀ j : Janus.Amd64.State, j.df = js.df →
      FlagsRel (mulFlags (decide ((BitVec.ofInt w ((js.getReg w 0).toInt * V.toInt)).toInt ≠ ((js.getReg w 0).toInt * V.toInt)))) j.df
        (mfl rf (BitVec.ofBool (decide ((BitVec.ofInt w ((js.getReg w 0).toInt * V.toInt)).toInt ≠ ((js.getReg w 0).toInt * V.toInt)))) u) := by
    intro j hj; rw [hj]; exact flagsRel_mfl hfr _ u
  rcases hW with rfl | hW16
  · simp only [show ((8 / 8 : Nat) : Int) = 1 from rfl]
    have hv16 : Sail.BitVec.truncate (BitVec.setWidth 128 (BitVec.ofInt (2 * 8) ((js.getReg 8 0).toInt * V.toInt))) 64 = (BitVec.ofInt 16 ((js.getReg 8 0).toInt * V.toInt)).setWidth 64 := by
      apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate]; try omega
    have hw16 := run_write_rgfi_size h hl (w := 16) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide))
      (BitVec.ofInt 16 ((js.getReg 8 0).toInt * V.toInt))
    simp only [regLocOf_zero, Nat.reduceDiv] at hw16
    rw [hv16, show (2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl, show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl,
      run_bind, hw16]
    simp only []
    generalize hV0 : (regWrite js 16 (Janus.Amd64.Loc.reg 0) (BitVec.ofInt 16 ((js.getReg 8 0).toInt * V.toInt))).regs (locReg (Janus.Amd64.Loc.reg 0)) = V0
    have hr1 : (setGpr s V0 (locReg (.reg 0))).regs.get? .rflags = some rf := by
      rw [get?_setGpr_of_not s V0 (by decide) rfl]; exact hr
    have hu1 : (setGpr s V0 (locReg (.reg 0))).regs.get? .janus_undef = some u := by
      rw [get?_setGpr_of_not s V0 (by decide) rfl]; exact hu
    have hl1 : (setGpr s V0 (locReg (.reg 0))).regs.get? .log_register_writes = some false := by
      rw [get?_setGpr_of_not s V0 (by decide) rfl]; exact hl
    have hc1 := hc.setGpr (r := locReg (.reg 0)) (by decide) V0
    have hrel1 := h.writeReg (w := 16) false (n := 0) (by decide) (BitVec.ofInt 16 ((js.getReg 8 0).toInt * V.toInt))
    simp only [regLocOf_zero, hV0] at hrel1
    rw [hflags _ _ hr1 hu1]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl1) _ htr, ?_, (hc1.set (by decide) _).set (by decide) _⟩
    exact hrel1.flagsRip _ _ (hfr' _ (regWrite_df _ _ _ _)) _
  · have hw8 : w ≠ 8 := by omega
    have hW' : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := Or.inr hW16
    have hm1 : ((w / 8 : Nat) : Int) ≠ 1 := by omega
    split
    · rename_i h1'; exact absurd h1' hm1
    simp only [hw8, ↓reduceIte]
    have hrl : ∀ k, regLocOf p.rex.isSome w k = .reg k := fun k => by unfold regLocOf; rw [if_neg hw8]
    have hwa := run_write_rgfi_size h hl hW' _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) (BitVec.ofInt w ((js.getReg w 0).toInt * V.toInt))
    simp only [hrl] at hwa
    rw [run_bind, run_bind, hwa]
    simp only []
    generalize hV0 : (regWrite js w (Janus.Amd64.Loc.reg 0) (BitVec.ofInt w ((js.getReg w 0).toInt * V.toInt))).regs (locReg (Janus.Amd64.Loc.reg 0)) = V0
    have hrel1 := h.writeReg (w := w) p.rex.isSome (n := 0) (by decide) (BitVec.ofInt w ((js.getReg w 0).toInt * V.toInt))
    simp only [hrl, hV0] at hrel1
    have hl1 : (setGpr s V0 (locReg (.reg 0))).regs.get? .log_register_writes = some false := by
      rw [get?_setGpr_of_not s V0 (by decide) rfl]; exact hl
    have hwd := run_write_rgfi_size hrel1 hl1 hW' _ rex hrex (n := 2) (by decide) (Or.inl (by decide))
      (BitVec.ofInt w (((js.getReg w 0).toInt * V.toInt) / (2 ^ w : Nat)))
    simp only [hrl] at hwd
    rw [show (2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl, hwd]
    simp only []
    generalize hV2 : (regWrite (regWrite js w (Janus.Amd64.Loc.reg 0) (BitVec.ofInt w ((js.getReg w 0).toInt * V.toInt))) w (Janus.Amd64.Loc.reg 2)
      (BitVec.ofInt w (((js.getReg w 0).toInt * V.toInt) / (2 ^ w : Nat)))).regs (locReg (Janus.Amd64.Loc.reg 2)) = V2
    have hrel2 := hrel1.writeReg (w := w) p.rex.isSome (n := 2) (by decide) (BitVec.ofInt w (((js.getReg w 0).toInt * V.toInt) / (2 ^ w : Nat)))
    simp only [hrl, hV2] at hrel2
    generalize hs2 : setGpr (setGpr s V0 (locReg (.reg 0))) V2 (locReg (.reg 2)) = s2 at hrel2 ⊢
    have hr2 : s2.regs.get? .rflags = some rf := by
      rw [← hs2, get?_setGpr_of_not _ V2 (by decide) rfl, get?_setGpr_of_not s V0 (by decide) rfl]; exact hr
    have hu2 : s2.regs.get? .janus_undef = some u := by
      rw [← hs2, get?_setGpr_of_not _ V2 (by decide) rfl, get?_setGpr_of_not s V0 (by decide) rfl]; exact hu
    have hl2' : s2.regs.get? .log_register_writes = some false := by
      rw [← hs2, get?_setGpr_of_not _ V2 (by decide) rfl, get?_setGpr_of_not s V0 (by decide) rfl]; exact hl
    have hc2 : X86Config s2 := by rw [← hs2]; exact (hc.setGpr (by decide) _).setGpr (by decide) _
    rw [hflags _ _ hr2 hu2]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl2') _ htr, ?_, (hc2.set (by decide) _).set (by decide) _⟩
    exact hrel2.flagsRip _ _ (hfr' _ (by rw [regWrite_df, regWrite_df])) _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_imul1 (opc : Nat) (hopc : opc = 0xF6 ∨ opc = 0xF7)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hm : _get_modr_m_reg m = BitVec.ofNat 3 5) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_imul_op_en_m .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases hopc with rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, hm, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **IMUL r/m** (one operand, `F6/F7 /5`): every ModRM form and width; `AX` or `rDX:rAX`, `CF = OF`. -/
theorem imul1_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o = 0xF6 ∨ o = 0xF7)
    (hext : m / 8 % 8 = 5)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  cases hmd : modrm (p.rex.getD 0) (m :: rest) with
  | none =>
    exfalso
    obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
    simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
    rcases ho with rfl | rfl <;> simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  generalize hw : (if o = 0xF6 then 8 else osz p) = w
  obtain ⟨hlk, hfs, hrep, rfl, hlen, rfl⟩ := decode_grp3 hpp ho (by omega) hmd hw.symm hd
  rw [step_of_decode hd] at hstep
  simp (config := {decide := true}) only [grp3, hext, ↓reduceIte, exec] at hstep
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
  simp only [hrd, ↓reduceIte, Except.ok.injEq] at hstep
  subst hstep
  have hreg4 : _get_modr_m_reg (BitVec.ofNat 8 m) = BitVec.ofNat 3 5 := by rw [(modrm_fields m hm256).2.1, hext]
  refine rm_frame hrel hcfg hcode hlim hpp (by unfold prefixGroup; omega) (by omega) (by omega)
    (by rcases ho with rfl | rfl <;> decide) hlk hmd (fun _ _ => hfs) hW (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => x86_imul_op_en_m .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_one_byte_imul1 o ho sr tr x hl rex _ sib hreg4 s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr _ _ _
  obtain ⟨s', hs', hrel', hc'⟩ := run_imul1 hrel hcfg hpr hrv o ho hw.symm m hm256 sib tr _ inc eaddr
    (hX true false false hok) hinc8 js.rip.toNat (by omega) (by omega) (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  rw [hinc'] at hrel'
  have hF : ∀ F : Int, BitVec.ofNat 16 ((BitVec.ofInt 8 (F / ((2 ^ 8 : Nat) : Int))).toNat * 256 + (BitVec.ofInt 8 F).toNat) =
      BitVec.ofInt 16 F := by
    intro F; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega
  by_cases h8 : w = 8
  · subst h8
    simp only [↓reduceIte] at hrel' ⊢
    rw [hF]
    exact hrel'
  · simp only [h8, ↓reduceIte] at hrel' ⊢; exact hrel'

end JanusX86.Proofs
