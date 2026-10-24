import JanusX86.Proofs.Setcc

/-! # Jcc rel32 (`0F 80–8F`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxHeartbeats 2000000 in
theorem run_jcc32 {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (opc : Nat) (ho : opc < 256) (m sib : BitVec 8) (tr : Nat) {ds : List Nat} (hds : CodeAt s tr ds) {v : Nat}
    {r : List Nat} (hle : Janus.Amd64.Decode.readLE 4 ds = some (v, r)) (sr : Nat) (hl1 : sr ≤ tr + 4)
    (hl2 : tr + 4 ≤ sr + 15) (htr : tr + 4 < 2 ^ 47) {b : Bool}
    (hcond : Janus.Amd64.condition (opc % 16) js.flags = some b)
    (hT : b = true → ((tr + 4) + Janus.Amd64.Decode.sext 32 64 v) % 2 ^ 64 < 2 ^ 47) :
    ∃ s', (x86_two_byte_jcc .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc) m sib).run s =
      .ok () s' ∧
      Rel (js.setRip (if b then BitVec.ofNat 64 (((tr + 4) + Janus.Amd64.Decode.sext 32 64 v) % 2 ^ 64)
        else BitVec.ofNat 64 (tr + 4))) s' ∧ X86Config s' := by
  obtain ⟨rf, hr, hfr⟩ := h.flags
  have hlen := check_len_ok_k sr tr 4 (by decide) hl1 hl2 htr
  have hsp := run_jcc_spec hr hfr opc ho hcond
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
  have h43 : bits_of_int (4 : Int) 3 = BitVec.ofNat 3 4 := by decide
  simp only [x86_two_byte_jcc, select_operand_size, in_64bit_mode, ↓reduceIte, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, run_bind, run_pure, hcr, h43, hlen, is_some, hsp]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, run_bind]
    have e : (bits_of_int (4 : Int) 48) = BitVec.ofNat 48 4 := by decide
    rw [e, run_add_to_iptr (BitVec.ofNat 48 tr) (BitVec.ofNat 48 4) (by simp; omega)]
    refine ⟨_, run_write_iptr hc.log _ (by simp; omega), ?_, hc.set (by decide) _⟩
    simp only [BitVec.toNat_ofNat, Bool.false_eq_true, ↓reduceIte]
    rw [show (tr % 2 ^ 48 + 4 % 2 ^ 48) = tr + 4 by omega]
    exact h.setRipR _
  · simp only [↓reduceIte, run_bind, hsel, show (8 : Int).toNat = 8 from rfl, show (4 : Int).toNat = 4 from rfl, hrime]
    have ht := hT rfl
    have hTe := target_eq (tr + 4) (Janus.Amd64.Decode.sext 32 64 v) (relI 4 v) (rel_sext 4 (Or.inr rfl) v hvl)
      (by omega) (by unfold relI; simp at hvl ⊢; split <;> omega) ht
    have hd : (BitVec.ofNat 64 (Janus.Amd64.Decode.sext 32 64 v)).toInt = relI 4 v := by
      rw [← sext_eq_32 v (by simpa using hvl), BitVec.toInt_signExtend_of_le (by decide)]
      simp only [BitVec.toInt, BitVec.toNat_ofNat, relI]; simp at hvl ⊢; split <;> split <;> omega
    have hb48 : (bits_of_int (4 + (BitVec.ofNat 64 (Janus.Amd64.Decode.sext 32 64 v)).toInt) 48).toInt = 4 + relI 4 v := by
      rw [hd]; exact bits_of_int_toInt _ _ (by unfold relI; simp at hvl ⊢; split <;> omega)
        (by unfold relI; simp at hvl ⊢; split <;> omega)
    have htr48 := toInt_ofNat48 tr (by omega)
    rw [run_add_to_iptr_int _ _ (by rw [htr48, hb48]; omega) (by rw [htr48, hb48]; omega)]
    rw [htr48, hb48]
    have hT2 : ((tr : Int) + (4 + relI 4 v)).toNat = ((tr + 4) + Janus.Amd64.Decode.sext 32 64 v) % 2 ^ 64 := by
      rw [← hTe.2.2]; congr 1; push_cast; omega
    rw [hT2]
    refine ⟨_, run_write_iptr hc.log _ ht, ?_, hc.set (by decide) _⟩
    exact h.setRipR _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_jcc32 {bytes : List Nat} {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: rest, n)) (ho : 0x80 ≤ o ∧ o < 0x90)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ p.opsize = false ∧ ∃ v r, readLE 4 rest = some (v, r) ∧
      len = n + 2 + 4 ∧ len ≤ 15 ∧ i = .jcc (o % 16) (sext 32 64 v) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hcs : o = 0x80 ∨ o = 0x81 ∨ o = 0x82 ∨ o = 0x83 ∨ o = 0x84 ∨ o = 0x85 ∨ o = 0x86 ∨ o = 0x87 ∨
      o = 0x88 ∨ o = 0x89 ∨ o = 0x8A ∨ o = 0x8B ∨ o = 0x8C ∨ o = 0x8D ∨ o = 0x8E ∨ o = 0x8F := by omega
  cases hr : readLE 4 rest with
  | none =>
    exfalso
    rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [twoByte, hr] at hd
  | some vr =>
    obtain ⟨v, r⟩ := vr
    rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp (config := {decide := true}) only [↓reduceIte, twoByte, hr, finish, true_and, and_true,
        false_and, and_false, or_false, false_or] at hd
      by_cases hl : 15 < n + 1 + 5 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
        cases hos : p.opsize <;> cases hsg : p.seg <;>
        simp (config := {decide := true}) [hf, hk, hl, hrp, hos, hsg, lockable, withFS] at hd ⊢
      all_goals first | (simp at hd; done) | (obtain ⟨rfl, rfl⟩ := hd; first | exact ⟨v, r, rfl, by omega, by omega, rfl⟩ | exact ⟨rfl, by omega, rfl⟩ | (refine ⟨by omega, by omega, rfl⟩) | (simp; omega))

set_option maxRecDepth 100000 in
theorem run_two_byte_jcc (opc : Nat) (hopc : 0x80 ≤ opc ∧ opc < 0x90)
    (sr tr : BitVec 48) (x : BitVec 52) (mp : BitVec 8) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (s : SState) :
    (two_byte_opcode_execute .Mode_64bit sr tr x mp rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_two_byte_jcc .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  have hcs : opc = 0x80 ∨ opc = 0x81 ∨ opc = 0x82 ∨ opc = 0x83 ∨ opc = 0x84 ∨ opc = 0x85 ∨ opc = 0x86 ∨ opc = 0x87 ∨
      opc = 0x88 ∨ opc = 0x89 ∨ opc = 0x8A ∨ opc = 0x8B ∨ opc = 0x8C ∨ opc = 0x8D ∨ opc = 0x8E ∨ opc = 0x8F := by omega
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [two_byte_opcode_execute, ext_two_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxRecDepth 100000 in
theorem modrmP2_jcc {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hr : p.rep = 0) (o : Nat) (ho : 0x80 ≤ o ∧ o < 0x90) : modrmP2 x o = false := by
  unfold modrmP2; rw [mpref_norep hp hr]
  have hcs : o = 0x80 ∨ o = 0x81 ∨ o = 0x82 ∨ o = 0x83 ∨ o = 0x84 ∨ o = 0x85 ∨ o = 0x86 ∨ o = 0x87 ∨
      o = 0x88 ∨ o = 0x89 ∨ o = 0x8A ∨ o = 0x8B ∨ o = 0x8C ∨ o = 0x8D ∨ o = 0x8E ∨ o = 0x8F := by omega
  cases p.opsize <;>
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **Jcc rel32** (`0F 80–8F`): all 16 conditions, taken and not taken. -/
theorem jcc32_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: rest, n)) (ho : 0x80 ≤ o ∧ o < 0x90)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hlk, hfs, hrep, hos, v, r, hr, rfl, hlen, rfl⟩ := decode_jcc32 hpp ho hd
  rw [step_of_decode hd] at hstep
  have hdrop : bytes.drop n = 0x0F :: o :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hcs : CodeAt s (js.rip.toNat + n + 2) rest := by
    have h2 : (bytes.drop n).drop 2 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 2)
    rw [show bytes.drop (n + 2) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 2) = js.rip.toNat + n + 2 by omega] at this
  obtain ⟨x, rex, hpr, hf⟩ := run_fetch_two hcfg hrip hcode hpp (by omega) hlim
  have hmp := modrmP2_jcc hpr hrep o ho
  have hf := hf (by rw [hmp]; simp [modrmSib])
  rw [hmp] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  rw [run_two_byte_jcc o ho _ _ x _ hl0] at hf
  simp only [exec] at hstep
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 2 + 4)) % 2 ^ 64) = BitVec.ofNat 64 (js.rip.toNat + n + 2 + 4) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1
  rw [hnext] at hstep
  cases hc : condition (o % 16) js.flags with
  | none => simp [hc] at hstep
  | some b =>
  simp only [hc] at hstep
  have hT : b = true → ((js.rip.toNat + n + 2 + 4) + sext 32 64 v) % 2 ^ 64 < 2 ^ 47 := by
    intro hb; subst hb
    simp only [↓reduceIte, branchTo] at hstep
    split at hstep
    · rename_i h; simpa [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd] using h
    · simp at hstep
  obtain ⟨s', hs', hrel', hcfg'⟩ := run_jcc32 hrel hcfg hpr o (by omega) 0#8 0#8 (js.rip.toNat + n + 2) hcs hr
    js.rip.toNat (by omega) (by omega) (by omega) hc hT
  refine ⟨s', run_janus_x86_step (by rw [hf, hs']), ?_, hcfg'⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hstep hrel'
    subst hstep; exact hrel'
  · simp only [↓reduceIte, branchTo] at hstep hrel'
    split at hstep
    · simp only [Except.ok.injEq] at hstep; subst hstep
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show js.rip.toNat + n + 2 + 4 < 2 ^ 64 by omega)]
    · simp at hstep

end JanusX86.Proofs
