import JanusX86.Proofs.Branch

/-! # CALL rel32 (`E8`) and RET (`C3`, `C2 imm16`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_read_sptr {js : Janus.Amd64.State} {s : SState} (h : Rel js s) :
    (read_sptr .Mode_64bit).run s = .ok (js.regs 4) s := by
  have := run_rgfi (s := s) (n := 4) (by decide) (h.gpr 4 (by decide))
  simp only [read_sptr, run_bind, in_64bit_mode, ↓reduceIte, run_pure]
  rw [show (4 : Int) = ((4 : Nat) : Int) from rfl, this]

theorem run_add_to_sptr_int (sp : BitVec 64) (D : Int) (hsp : sp.toNat < 2 ^ 48) (hD : -(2 ^ 32 : Int) ≤ D ∧ D < 2 ^ 32)
    (h0 : 0 ≤ (sp.toNat : Int) + D) (h1 : (sp.toNat : Int) + D < 2 ^ 47) (s : SState) :
    (add_to_sptr .Mode_64bit sp (bits_of_int D 64)).run s = .ok (BitVec.ofNat 64 ((sp.toNat : Int) + D).toNat) s := by
  have hsi : sp.toInt = sp.toNat := toInt_of_lt sp (by omega)
  have hdi : (bits_of_int D 64).toInt = D := bits_of_int_toInt _ _ (by omega) (by omega)
  have e : Sail.BitVec.truncate (bits_of_int (sp.toInt + (bits_of_int D 64).toInt) 65) 64 =
      BitVec.ofNat 64 ((sp.toNat : Int) + D).toNat := by
    rw [hsi, hdi]
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (sp.toNat : Int) + D = ((((sp.toNat : Int) + D).toNat : Nat) : Int) by omega, bits_of_int_natCast_toNat]
    simp only [Int.toNat_natCast]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hc : (BitVec.ofNat 64 ((sp.toNat : Int) + D).toNat).toInt = (sp.toNat : Int) + D := by
    rw [toInt_of_lt _ (by simp; omega)]; simp; omega
  simp only [add_to_sptr, in_64bit_mode, ↓reduceIte, run_bind, e, run_canonical_address_p, hc]
  rw [show decide (-(2 ^ 47 : Int) ≤ (sp.toNat : Int) + D ∧ (sp.toNat : Int) + D < 2 ^ 47) = true by
    simp only [decide_eq_true_eq]; omega]
  rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem sx49_48_128 (a : Nat) (ha : a < 2 ^ 47) :
    Sail.BitVec.truncate (Sail.BitVec.signExtend (Sail.BitVec.signExtend (BitVec.ofNat 48 a) 49) 128) (8 * 8) =
      BitVec.ofNat 64 a := by
  have hm : (BitVec.ofNat 48 a).msb = false := by rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp; omega
  have hm2 : (Sail.BitVec.signExtend (BitVec.ofNat 48 a) 49).msb = false := by
    simp only [Sail.BitVec.signExtend]; rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp; omega
  simp only [Sail.BitVec.truncate]
  have e2 := BitVec.signExtend_eq_setWidth_of_msb_false hm2 (v := 128)
  simp only [Sail.BitVec.signExtend] at e2 ⊢
  rw [e2, BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem sx48_64 (a : Nat) (ha : a < 2 ^ 47) :
    Sail.BitVec.signExtend (Sail.BitVec.truncate (BitVec.ofNat 64 a) 48) 64 = BitVec.ofNat 64 a := by
  have hm : (Sail.BitVec.truncate (BitVec.ofNat 64 a) 48).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [Sail.BitVec.truncate]; omega
  simp only [Sail.BitVec.signExtend]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate]; omega

theorem run_wme_push (asz : Nat) (eff : BitVec 64) (a : Nat) (ha : a < 2 ^ 47) (s : SState) :
    (wme_size .Mode_64bit asz 8 eff none 2 (Sail.BitVec.signExtend (Sail.BitVec.signExtend (BitVec.ofNat 48 a) 49) 128)
      false false).run s = (store_bytes_to_ea .Mode_64bit asz 8 eff none 2 (BitVec.ofNat 64 a) false false).run s := by
  unfold wme_size
  show (store_bytes_to_ea .Mode_64bit asz 8 eff none 2 (Sail.BitVec.truncate (Sail.BitVec.signExtend
    (Sail.BitVec.signExtend (BitVec.ofNat 48 a) 49) 128) (8 * 8)) false false).run s = _
  rw [sx49_48_128 a ha]

set_option maxHeartbeats 4000000 in
theorem run_call_e8 {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (m sib : BitVec 8) (tr : Nat) {ds : List Nat} (hds : CodeAt s tr ds) {v : Nat}
    {r : List Nat} (hle : Janus.Amd64.Decode.readLE 4 ds = some (v, r)) (sr : Nat) (hl1 : sr ≤ tr + 4)
    (hl2 : tr + 4 ≤ sr + 15) (htr : tr + 4 < 2 ^ 47)
    (hT : ((tr + 4) + Janus.Amd64.Decode.sext 32 64 v) % 2 ^ 64 < 2 ^ 47)
    (hacc : js.mem.accessible (js.regs 4 - 8).toNat 8 true = true) :
    ∃ s', (x86_call_e8_op_en_m .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 0xE8) m sib).run s =
      .ok () s' ∧
      Rel ((({ js with mem := js.mem.writeLE (js.regs 4 - 8).toNat 8 (tr + 4) }).setReg 4 (js.regs 4 - 8)).setRip
        (BitVec.ofNat 64 (((tr + 4) + Janus.Amd64.Decode.sext 32 64 v) % 2 ^ 64))) s' ∧ X86Config s' := by
  have hrip := h.rip
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  have hcr : (check_range 0 4 (4 : Int)).run s = .ok (4 : Int) s := by
    simp only [check_range, run_bind, run_sail_assert_of (show ((0 ≤b (4 : Int)) && ((4 : Int) ≤b 4)) = true by decide),
      run_pure]
  obtain ⟨-, hvv, -⟩ := readLE_sumLE _ ds hle
  have hvl : v < 2 ^ (8 * 4) := by
    rw [hvv, Nat.pow_mul]
    exact sumLE_lt _ (fun j => by
      by_cases hj : j < ds.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hds.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
  have hrime := run_rime_size_disp hc hrip 8 hds (k := 4) (Or.inr rfl) hle (by omega)
  have hadd1 : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (bits_of_int (4 : Int) 48)).run s =
      .ok (BitVec.ofNat 48 (tr + 4)) s := by
    have ez : (bits_of_int (4 : Int) 48).toNat = 4 := by decide
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hlen := check_len_ok sr (tr + 4) hl1 hl2 htr
  have hTe := target_eq (tr + 4) (Janus.Amd64.Decode.sext 32 64 v) (relI 4 v) (rel_sext 4 (Or.inr rfl) v hvl)
    (by omega) (by unfold relI; simp at hvl ⊢; split <;> omega) hT
  have hoff := rel_toInt48 4 (Or.inr rfl) v hvl
  have htr48 := toInt_ofNat48 (tr + 4) (by omega)
  have hb := h.acc_bound hacc
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  have hlt := (js.regs 4).isLt
  have hsp8 : 8 ≤ (js.regs 4).toNat := by
    have : (js.regs 4 - 8).toNat + 8 ≤ 2 ^ 47 := hb
    rw [BitVec.toNat_sub, h8] at this
    omega
  have hspm : (js.regs 4 - 8).toNat = (js.regs 4).toNat - 8 := by
    rw [BitVec.toNat_sub, h8]; omega
  have hsp : (add_to_sptr .Mode_64bit (js.regs 4) (bits_of_int (Neg.neg (8 : Int)) 64)).run s =
      .ok (js.regs 4 - 8) s := by
    rw [run_add_to_sptr_int _ _ (by omega) (by decide) (by omega) (by omega)]
    show EStateM.Result.ok _ s = _
    congr 1; apply BitVec.eq_of_toNat_eq; rw [hspm]; simp; omega
  have heff : Sail.BitVec.signExtend (Sail.BitVec.truncate (js.regs 4 - 8) 48) 64 = js.regs 4 - 8 := by
    have := sx48_64 (js.regs 4 - 8).toNat (by omega); rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  have hla : (ea_to_la .Mode_64bit (js.regs 4 - 8) 2 8).run s = .ok (js.regs 4 - 8) s :=
    run_ea_to_la _ ⟨by decide, by decide⟩ _ (by omega)
  obtain ⟨s1, hs1, hrel1, hcfg1, hreg1⟩ := run_store_core h hc 8 (n := 8) (by decide) _ _ 2 hla
    (BitVec.ofNat 64 (tr + 4)) false hacc
  have hdat := sx49_48_128 (tr + 4) (by omega)
  simp only [x86_call_e8_op_en_m, select_operand_size, in_64bit_mode, ↓reduceIte, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, run_bind, run_pure, hcr, hsel, show (8 : Int).toNat = 8 from rfl, show (4 : Int).toNat = 4 from rfl,
    hrime, hadd1, tsx48, hlen, is_some, run_read_sptr h, select_address_size_none, hsp, heff,
    run_alignment_checking h hc]
  rw [run_add_to_iptr_int _ _ (by rw [htr48, hoff]; omega) (by rw [htr48, hoff]; omega)]
  simp only [run_read_sptr h, hsp, hsel, run_alignment_checking h hc, heff, show (8 : Int).toNat = 8 from rfl,
    run_wme_push 8 _ (tr + 4) (by omega), hs1]
  rw [htr48, hoff, hTe.2.2]
  have hl1' := hcfg1.log
  have e1 : (SState.set s1 .rip (BitVec.ofNat 64 ((tr + 4 + Janus.Amd64.Decode.sext 32 64 v) % 2 ^ 64))).regs.get?
      .log_register_writes = some false := by rw [get?_set_ne _ _ (by decide)]; exact hl1'
  rw [run_write_iptr hl1' _ hT]
  simp only [write_sptr, in_64bit_mode, ↓reduceIte]
  have := run_write_rgfi e1 (n := 4) (by decide) (js.regs 4 - 8)
  rw [show (4 : Int) = ((4 : Nat) : Int) from rfl, this]
  refine ⟨_, rfl, ?_, ((hcfg1.set (by decide) _).setGpr (by decide) _)⟩
  have := (hrel1.setRipR (BitVec.ofNat 64 ((tr + 4 + Janus.Amd64.Decode.sext 32 64 v) % 2 ^ 64))).setReg
    (r := 4) (by decide) (js.regs 4 - 8)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show tr + 4 < 2 ^ 64 by omega)] at this
  exact this

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 in
theorem store_inv {m m' : Janus.Arm64.Memory} {a n v : Nat} (h : store m a n v = .ok m') :
    m.accessible a n true = true ∧ m' = m.writeLE a n v := by
  unfold store at h
  split at h
  · split at h
    · rename_i hacc; simp only [Except.ok.injEq] at h; exact ⟨hacc, h.symm⟩
    · simp at h
  · simp at h

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_call {bytes : List Nat} {p : Prefixes} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0xE8 :: rest, n))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ p.opsize = false ∧ ∃ v r, readLE 4 rest = some (v, r) ∧
      len = n + 1 + 4 ∧ len ≤ 15 ∧ i = .call (sext 32 64 v) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  cases hr : readLE 4 rest with
  | none => exfalso; simp (config := {decide := true}) [oneByte, hr] at hd
  | some vr =>
    obtain ⟨v, r⟩ := vr
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hr, finish, true_and, and_true,
      false_and, and_false, or_false, false_or] at hd
    by_cases hl5 : 15 < n + 5 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;>
      cases hk : p.lock <;> cases hos : p.opsize <;> cases hsg : p.seg <;>
      simp (config := {decide := true}) [hf, hk, hl5, hrp, hos, hsg, lockable, withFS] at hd ⊢
    all_goals first | (simp at hd; done) | (obtain ⟨rfl, rfl⟩ := hd; first | exact ⟨v, r, rfl, rfl, by omega, rfl⟩ | exact ⟨rfl, by omega, rfl⟩ | (simp; omega))

set_option maxRecDepth 100000 in
theorem run_one_byte_call (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xE8) m sib).run s =
      (x86_call_e8_op_en_m .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xE8) m sib).run s := by
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **CALL rel32** (`E8`): the return address pushed on the stack, `RSP` and the target. -/
theorem call_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0xE8 :: rest, n))
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hlk, hfs, hrep, hos, v, r, hr, rfl, hlen, rfl⟩ := decode_call hpp hd
  rw [step_of_decode hd] at hstep
  have hdrop : bytes.drop n = 0xE8 :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hcs : CodeAt s (js.rip.toNat + n + 1) rest := by
    have h2 : (bytes.drop n).drop 1 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 1)
    rw [show bytes.drop (n + 1) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 1) = js.rip.toNat + n + 1 by omega] at this
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim (by decide) (by decide)
    ⟨by decide, by decide, by decide⟩ (by rw [show modrmP1 0xE8 = false by decide]; simp [modrmSib])
  rw [show modrmP1 0xE8 = false by decide] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  rw [run_one_byte_call _ _ x hl0] at hf
  simp only [exec, push64] at hstep
  have hnk : (BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + 4)) % 2 ^ 64)).toNat = js.rip.toNat + n + 1 + 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  rw [hnk] at hstep
  split at hstep
  · rename_i hT
    rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 64 ∣ 2 ^ 64)] at hT
    cases hst : store js.mem (js.regs 4 - 8).toNat 8 (js.rip.toNat + n + 1 + 4) with
    | error e => simp only [hst] at hstep; cases hstep
    | ok m' =>
      simp only [hst, Except.ok.injEq] at hstep; subst hstep
      obtain ⟨hacc, rfl⟩ := store_inv hst
      obtain ⟨s', hs', hrel', hcfg'⟩ := run_call_e8 hrel hcfg hpr 0#8 0#8 (js.rip.toNat + n + 1) hcs hr js.rip.toNat
        (by omega) (by omega) (by omega) hT hacc
      exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hrel', hcfg'⟩
  · simp at hstep

end JanusX86.Proofs
