import JanusX86.Proofs.CallInd
import JanusX86.Proofs.ShiftSpec

/-! # BT r/m, imm8 (`0F BA /4`) and BT r, r (`0F A3`, register destination) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_two_byte_bt_ba (sr tr : BitVec 48) (x : BitVec 52) (mp : BitVec 8) (hl : _get_prefixes_lck x = 0#8)
    (rex m sib : BitVec 8) (hm : _get_modr_m_reg m = BitVec.ofNat 3 4) (s : SState) :
    (two_byte_opcode_execute .Mode_64bit sr tr x mp rex (BitVec.ofNat 8 0xBA) m sib).run s =
      (x86_bt_0f_ba .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xBA) m sib).run s := by
  simp (config := {decide := true}) only [two_byte_opcode_execute, ext_two_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, hm, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxRecDepth 100000 in
theorem run_two_byte_bt_a3 (sr tr : BitVec 48) (x : BitVec 52) (mp : BitVec 8) (hl : _get_prefixes_lck x = 0#8)
    (rex m sib : BitVec 8) (s : SState) :
    (two_byte_opcode_execute .Mode_64bit sr tr x mp rex (BitVec.ofNat 8 0xA3) m sib).run s =
      (x86_bt_0f_a3 .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xA3) m sib).run s := by
  simp (config := {decide := true}) only [two_byte_opcode_execute, ext_two_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem mod_nat (a b : Nat) (hb : 0 < b) : X86Sail.Functions.mod (a : Int) (b : Int) = ((a % b : Nat) : Int) := by
  unfold X86Sail.Functions.mod floor2
  have h1 : Int.tdiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := by simp [Int.tdiv]
  have h2 : Int.tmod (a : Int) (b : Int) = ((a % b : Nat) : Int) := by simp [Int.tmod]
  rw [h1, h2]
  have : ((b : Int) >b 0) = true := by simp; omega
  simp only [this, Bool.true_and]
  have h3 : ((((a % b : Nat) : Int) ≥b 0) || ((b : Int) <b 0) && (((a % b : Nat) : Int) ≤b 0)) = true := by simp; left; exact Int.emod_nonneg _ (by omega)
  rw [if_pos h3]
  have e : ((a / b : Nat) : Int) * (b : Int) + ((a % b : Nat) : Int) = a := by
    have := Nat.div_add_mod a b; rw [Nat.mul_comm] at this; exact_mod_cast this
  generalize ((a / b : Nat) : Int) * (b : Int) = P at e ⊢
  omega

/-- Janus' flags after `BT`: `CF` = the bit, the rest undefined. -/
def btFlags (b : Bool) : Janus.Amd64.Flags :=
  { cf := some b, pf := none, af := none, zf := none, sf := none, ovf := none }

/-- The model's `rflags` after `BT`: `CF` = the bit, `PF AF SF OF` from the undefined source. -/
def btfl (r : BitVec 32) (c : BitVec 1) (u : Nat) : BitVec 32 :=
  _update_rflagsbits_of (_update_rflagsbits_sf (_update_rflagsbits_af (_update_rflagsbits_pf
    (_update_rflagsbits_cf r c) (bits_of_int (u : Int) 1)) (bits_of_int (u : Int) 1)) (bits_of_int (u : Int) 1))
    (bits_of_int (u : Int) 1)

theorem flagsRel_bt {f0 : Janus.Amd64.Flags} {df : Bool} {r : BitVec 32} (hr : FlagsRel f0 df r) (b : Bool) (u : Nat) :
    FlagsRel (btFlags b) df (btfl r (BitVec.ofBool b) u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [btfl, btFlags, rf_get_cf_upd_cf, rf_get_cf_upd_pf, rf_get_cf_upd_af, rf_get_cf_upd_sf,
    rf_get_cf_upd_of, rf_get_df_upd_cf, rf_get_df_upd_pf, rf_get_df_upd_af, rf_get_df_upd_sf, rf_get_df_upd_of,
    rf_get_ac_upd_cf, rf_get_ac_upd_pf, rf_get_ac_upd_af, rf_get_ac_upd_sf, rf_get_ac_upd_of]
  all_goals first | exact hr.df | exact hr.ac | (intro v hv; cases hv; rfl) | (intro v hv; cases hv)

theorem run_btflags {s : SState} {u : Nat} (hu : s.regs.get? .janus_undef = some u) (t : SState) (rt : BitVec 32)
    (hrt : t.regs.get? .rflags = some rt) (hut : t.regs.get? .janus_undef = some u) (c : BitVec 1) :
    (do
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
      writeReg Register.rflags (_update_rflagsbits_sf rflags_var sailval)
      let rflags_var ← readReg Register.rflags
      let sailval ← undef_flg ()
      writeReg Register.rflags (_update_rflagsbits_of rflags_var sailval) : SailM Unit).run t =
      .ok () (t.set .rflags (btfl rt c u)) := by
  have hu' : ∀ v : BitVec 32, (t.set .rflags v).regs.get? .janus_undef = some u := fun v => by
    rw [get?_set_ne _ _ (by decide)]; exact hut
  rw [← set_self hrt]
  simp only [run_bind, run_readReg (get?_set_same _ _ _), run_writeReg, set_set, run_undef_flg (hu' _), btfl]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxHeartbeats 4000000 in
theorem run_bt_ba {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) {w : Nat} (hw : w = osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr te : Nat) (V : BitVec w) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 1)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hte : te = tr + inc) (hinc : inc < 8) {ds : List Nat} (hds : CodeAt s te ds) {v : Nat} {r : List Nat}
    (hle : Janus.Amd64.Decode.readLE 1 ds = some (v, r))
    (sr : Nat) (hl1 : sr ≤ te + 1) (hl2 : te + 1 ≤ sr + 15) (htr : te + 1 < 2 ^ 47) :
    ∃ s', (x86_bt_0f_ba .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 0xBA)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((js.setFlags (btFlags (V.getLsbD (v % w)))).setRip (BitVec.ofNat 64 (te + 1))) s' ∧ X86Config s' := by
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  have hW : w = 16 ∨ w = 32 ∨ w = 64 := by rw [hw]; rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (te + 1) hl1 hl2 htr
  have hl := hc.log
  have hrip := h.rip
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  have hinc' : (bits_of_int (inc : Int) 3) = BitVec.ofNat 3 inc := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have hadd : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48)).run s =
      .ok (BitVec.ofNat 48 te) s := by
    have ez : (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48).toNat = inc := by
      simp [Sail.BitVec.zeroExtend]; omega
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hadd1 : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 te) 0x000000000001#48).run s =
      .ok (BitVec.ofNat 48 (te + 1)) s := by
    rw [run_add_to_iptr _ _ (by simp; omega)]
    congr 2; simp; omega
  have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    have := size_int p false; simp only [Bool.false_eq_true, ↓reduceIte] at this; rw [this, hw]
  obtain ⟨-, hvv, -⟩ := readLE_sumLE _ ds hle
  have hvl : v < 256 := by
    rw [hvv, show 256 = 256 ^ 1 from rfl]
    exact sumLE_lt _ (fun j => by
      by_cases hj : j < ds.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hds.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
  have hrme : (rme_size .Mode_64bit 8 1 (Sail.BitVec.signExtend (BitVec.ofNat 48 te) 64) none 1 ":X"
      false false).run s = .ok (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * 1) v) 128) s := by
    simp only [rme_size, run_bind, run_load_code hc hrip 8 hds (by decide) hle (by omega), run_pure]
  have hbo : Sail.BitVec.truncate (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * 1) v) 128) 8 = BitVec.ofNat 8 v := by
    apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate, Sail.BitVec.zeroExtend]
  have hash : ash_left_int ((w / 8 : Nat) : Int) 3 = ((w : Nat) : Int) := by
    rcases hW with e | e | e <;> subst e <;> decide
  have hmodv : X86Sail.Functions.mod (Sail.BitVec.toNatInt (BitVec.ofNat 8 v)) (ash_left_int ((w / 8 : Nat) : Int) 3) =
      ((v % w : Nat) : Int) := by
    rw [hash, show Sail.BitVec.toNatInt (BitVec.ofNat 8 v) = ((v : Nat) : Int) by simp [Sail.BitVec.toNatInt]; omega]
    exact mod_nat v w (by omega)
  have hcr : (check_range 0 64 ((v % w : Nat) : Int)).run s = .ok ((v % w : Nat) : Int) s := by
    have : v % w < w := Nat.mod_lt _ (by omega)
    have hb : ((0 ≤b ((v % w : Nat) : Int)) && (((v % w : Nat) : Int) ≤b 64)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    simp only [check_range, run_bind, run_sail_assert_of hb, run_pure]
  have hbit : logbit_bits ((v % w : Nat) : Int) ((V.setWidth 64).setWidth 128) = BitVec.ofBool (V.getLsbD (v % w)) := by
    have : v % w < w := Nat.mod_lt _ (by omega)
    have h128 : v % w < 128 := by rcases hW with e | e | e <;> subst e <;> omega
    rw [logbit_eq _ _ h128]
    simp only [BitVec.getLsbD_setWidth]
    have h64 : v % w < 64 := by rcases hW with e | e | e <;> subst e <;> omega
    simp [h128, h64]
  simp only [x86_bt_0f_ba, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hsz, hsg, Int.toNat_natCast,
    show (0b001#3 : BitVec 3) = BitVec.ofNat 3 1 from rfl, hX sg hsg4 hsg5, hinc', hadd, hsel,
    show (8 : Int).toNat = 8 from rfl, hrme, run_pure, hbo, hadd1, hlen, is_some, Bool.false_eq_true, ↓reduceIte,
    hmodv, hcr, hbit]
  have hu' : ∀ v : BitVec 32, (s.set .rflags v).regs.get? .janus_undef = some u := fun v => by
    rw [get?_set_ne _ _ (by decide)]; exact hu
  simp only [run_readReg hr, run_writeReg, run_readReg (get?_set_same _ _ _), set_set, run_undef_flg (hu' _)]
  have hl' : (s.set .rflags (btfl rf (BitVec.ofBool (V.getLsbD (v % w))) u)).regs.get? .log_register_writes =
      some false := by rw [get?_set_ne _ _ (by decide)]; exact hl
  refine ⟨_, run_write_iptr hl' _ htr, ?_, (hc.set (by decide) _).set (by decide) _⟩
  exact h.flagsRip _ _ (flagsRel_bt hfr _ u) _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem decode_btba {bytes : List Nat} {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: 0xBA :: m :: rest, n)) (hext : m / 8 % 8 = 4)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ ∃ v r4, readLE 1 r3 = some (v, r4) ∧ len = n + 2 + c + 1 ∧
      len ≤ 15 ∧ i = .bit .bt (osz p) (rmDst p (osz p) mm.rm) (.imm v) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hex := modrm_ext hmd
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hex; subst hex
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have ho8 : (osz p = 8) = False := by rcases osz_cases p with e | e | e <;> simp [e]
  cases hr : readLE 1 r3 with
  | none => simp (config := {decide := true}) [twoByte, hmd, hext, immU8, hr] at hd
  | some vr =>
  obtain ⟨v, r4⟩ := vr
  simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, hou, true_and, and_true, immU8, hr,
    false_and, and_false, or_false, false_or, hext] at hd ⊢
  by_cases hl : 15 < n + 1 + 1 + c + 1 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
    cases rm <;>
    simp (config := {decide := true}) [hf, hk, hl, hrp, finish, withFS, rmDst, rmLoc, regLocOf, ho8, lockable] at hd ⊢
  all_goals (obtain ⟨rfl, rfl⟩ := hd; first | exact ⟨by omega, rfl⟩ | exact ⟨rfl, by omega, rfl⟩ | omega)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem modrmP2_bt {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hr : p.rep = 0) (o : Nat) (ho : o = 0xBA ∨ o = 0xA3) : modrmP2 x o = true := by
  unfold modrmP2; rw [mpref_norep hp hr]
  cases p.opsize <;> rcases ho with rfl | rfl <;> decide

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **BT r/m16/32/64, imm8** (`0F BA /4`): register and memory forms, every width. -/
theorem bt_ba_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: 0xBA :: m :: rest, n)) (hext : m / 8 % 8 = 4)
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
    simp (config := {decide := true}) [twoByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hlk, hfs, hrep, v, r4, hr4, rfl, hlen, rfl⟩ := decode_btba hpp hext hmd hd
  rw [step_of_decode hd] at hstep
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = 0x0F :: 0xBA :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := by rcases osz_cases p with e | e | e <;> simp [e]
  have hW' : osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := by rcases osz_cases p with e | e | e <;> simp [e]
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 2 + c + 1)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + 1) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  simp only [exec, execBit, readSrc] at hstep
  rw [hnext] at hstep
  cases hrd : readLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + 1)) (osz p) (rmDst p (osz p) mm.rm) with
  | error e => simp only [hrd] at hstep; cases hstep
  | ok X =>
  simp only [hrd, Except.ok.injEq] at hstep; subst hstep
  obtain ⟨hok, rfl⟩ := readLoc_loc hrd
  have hfld := (modrm_fields m hm256).2.1
  rw [hext] at hfld
  refine rm_frame2 hrel hcfg hcode hlim hpp (fun x rex hpr => modrmP2_bt hpr hrep 0xBA (Or.inl rfl)) hlk hmd
    (fun _ _ => hfs) hW (k := 1) (by decide) (by omega)
    (fun sr tr x rex sib => x86_bt_0f_ba .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xBA) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_two_byte_bt_ba sr tr x _ hl rex _ sib hfld s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 hc3 hX _ _ _ _
  obtain ⟨s', hs', hrel', hc'⟩ := run_bt_ba hrel hcfg hpr hrv rfl m hm256 sib tr (tr + inc) _ inc eaddr
    (hX true false false hok) rfl hinc8 (by rw [hinc']; exact hc3) hr4 js.rip.toNat (by omega) (by omega) (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  have hv : v < 256 := by
    obtain ⟨-, hvv, -⟩ := readLE_sumLE _ _ hr4
    rw [hvv, show 256 = 256 ^ 1 from rfl]
    exact sumLE_lt _ (fun j => by
      by_cases hj : j < r3.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hc3.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
  have hk : (BitVec.ofNat (osz p) v).toNat % osz p = v % osz p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show v < 2 ^ osz p by rcases hW' with e | e | e <;> rw [e] <;> omega)]
  rw [hk]; rw [hinc'] at hrel'
  exact hrel'

end JanusX86.Proofs
