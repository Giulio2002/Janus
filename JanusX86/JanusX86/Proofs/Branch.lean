import JanusX86.Proofs.MovOI

/-! # Branches: Jcc rel8 (`70–7F`), JMP rel8/rel32 (`EB/E9`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_add_to_iptr_int (a d : BitVec 48) (h0 : 0 ≤ a.toInt + d.toInt) (h1 : a.toInt + d.toInt < 2 ^ 47)
    (s : SState) :
    (add_to_iptr .Mode_64bit a d).run s = .ok (BitVec.ofNat 48 (a.toInt + d.toInt).toNat) s := by
  have ha1 : -2 ^ (48 - 1) ≤ a.toInt := BitVec.le_toInt a
  have ha2 : a.toInt < 2 ^ (48 - 1) := BitVec.toInt_lt
  have hd1 : -2 ^ (48 - 1) ≤ d.toInt := BitVec.le_toInt d
  have hd2 : d.toInt < 2 ^ (48 - 1) := BitVec.toInt_lt
  have hi : (bits_of_int (a.toInt + d.toInt) 49).toInt = a.toInt + d.toInt :=
    bits_of_int_toInt _ _ (by simp at *; omega) (by simp at *; omega)
  simp only [add_to_iptr, in_64bit_mode, ↓reduceIte, run_bind, run_canonical_address_p, hi]
  rw [show decide (-(2 ^ 47 : Int) ≤ a.toInt + d.toInt ∧ a.toInt + d.toInt < 2 ^ 47) = true by
    simp only [decide_eq_true_eq]; omega]
  simp only [↓reduceIte, run_pure]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have e : (bits_of_int (a.toInt + d.toInt) 49).toNat = (a.toInt + d.toInt).toNat := by
    rw [show a.toInt + d.toInt = (((a.toInt + d.toInt).toNat : Nat) : Int) by omega, bits_of_int_natCast_toNat]
    simp only [Int.toNat_natCast]; exact Nat.mod_eq_of_lt (by omega)
  rw [e]

theorem check_len_ok_k (sr tr j : Nat) (hj : j < 8) (h1 : sr ≤ tr + j) (h2 : tr + j ≤ sr + 15) (h3 : tr + j < 2 ^ 47) :
    check_instruction_length (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) (BitVec.ofNat 3 j) = none := by
  have e1 := toInt_ofNat48 sr (by omega)
  have e2 := toInt_ofNat48 tr (by omega)
  have e3 : (bits_of_int (tr : Int) 48).toInt = (tr : Int) := bits_of_int_toInt _ _ (by omega) (by omega)
  have e4 : (bits_of_int (sr : Int) 48).toInt = (sr : Int) := bits_of_int_toInt _ _ (by omega) (by omega)
  have e5 : Sail.BitVec.toNatInt (bits_of_int (((Sail.BitVec.toNatInt (BitVec.ofNat 3 j)).toNat : Nat) : Int) 3) =
      (j : Int) := by
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have e6 : (bits_of_int ((tr : Int) + (j : Int)) 49).toInt = (tr : Int) + j := bits_of_int_toInt _ _ (by omega) (by omega)
  have e7 : (bits_of_int ((tr : Int) + (j : Int) - (sr : Int)) 50).toInt = (tr : Int) + j - (sr : Int) :=
    bits_of_int_toInt _ _ (by omega) (by omega)
  unfold check_instruction_length
  simp only [e1, e2, e3, e4, e5, e6, e7]
  have : ((15 : Int) <b ((tr : Int) + j - (sr : Int))) = false := by simp; omega
  simp only [this, Bool.false_eq_true, ↓reduceIte]

theorem nib_all : ∀ o < 256, Sail.BitVec.truncate (BitVec.ofNat 8 o &&& 0x0F#8) 4 = BitVec.ofNat 4 (o % 16) := by
  decide +kernel

theorem eqb4_all : ∀ a < 16, ∀ j < 16, eq_bits_nat (BitVec.ofNat 4 a) j = decide (a = j) := by decide +kernel

theorem flag_true {o : Option Bool} {b : BitVec 1} (h : FlagEq o b) {v : Bool} (hv : o = some v) :
    (1#1 == b) = v ∧ (0#1 == b) = !v := by
  rw [h v hv]; cases v <;> decide

@[simp] theorem one_beq_ofBool (v : Bool) : (1#1 == BitVec.ofBool v) = v := by cases v <;> rfl
@[simp] theorem ofBool_beq_ofBool (a b : Bool) : (BitVec.ofBool a == BitVec.ofBool b) = (a == b) := by
  cases a <;> cases b <;> rfl
@[simp] theorem zero_beq_ofBool (v : Bool) : (0#1 == BitVec.ofBool v) = !v := by cases v <;> rfl

/-- The model's condition evaluation (`jcc_cmovcc_setcc_spec`) is Janus' `condition` wherever
Janus defines it. -/
theorem run_jcc_spec {s : SState} {r : BitVec 32} (hr : s.regs.get? .rflags = some r) {f : Janus.Amd64.Flags}
    {df : Bool} (hf : FlagsRel f df r) (o : Nat) (ho : o < 256) {b : Bool}
    (hc : Janus.Amd64.condition (o % 16) f = some b) :
    (jcc_cmovcc_setcc_spec (BitVec.ofNat 8 o)).run s = .ok b s := by
  have hn := nib_all o ho
  have hlt : o % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize o % 16 = cc at hn hlt hc
  simp only [jcc_cmovcc_setcc_spec, hn]
  unfold Janus.Amd64.condition at hc
  have hq : cc = 0 ∨ cc = 1 ∨ cc = 2 ∨ cc = 3 ∨ cc = 4 ∨ cc = 5 ∨ cc = 6 ∨ cc = 7 ∨ cc = 8 ∨ cc = 9 ∨
      cc = 10 ∨ cc = 11 ∨ cc = 12 ∨ cc = 13 ∨ cc = 14 ∨ cc = 15 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [eq_bits_nat, ↓reduceIte, Bool.false_eq_true, run_bind,
    run_readReg hr, run_pure, Nat.reduceDiv, Nat.reduceMod] at hc ⊢
  all_goals
    revert hc
    rcases e1 : f.cf with _ | c1 <;> rcases e2 : f.zf with _ | z1 <;> rcases e3 : f.sf with _ | s1 <;>
      rcases e4 : f.ovf with _ | o1 <;> rcases e5 : f.pf with _ | p1 <;>
    intro hc <;>
    simp only [Option.map_some, Option.map_none, reduceCtorEq, Option.some.injEq] at hc <;>
    (try simp only [hf.cf _ e1]) <;> (try simp only [hf.zf _ e2]) <;> (try simp only [hf.sf _ e3]) <;>
    (try simp only [hf.ovf _ e4]) <;> (try simp only [hf.pf _ e5]) <;>
    (try simp only [orM, andM, run_bind, run_readReg hr, run_pure, run_map, toBool]) <;>
    subst hc <;>
    (try cases c1) <;> (try cases z1) <;> (try cases s1) <;> (try cases o1) <;> (try cases p1) <;>
    (try simp only [hf.cf _ e1, hf.zf _ e2, hf.sf _ e3, hf.ovf _ e4, hf.pf _ e5, run_bind, run_readReg hr,
      run_pure, run_map, toBool]) <;>
    (first
      | rfl
      | (simp [run_bind, run_map, run_readReg hr, toBool, hf.sf _ e3, hf.ovf _ e4]; done)
      | (simp [run_bind, run_map, run_readReg hr, toBool, hf.zf _ e2, hf.sf _ e3, hf.ovf _ e4]; done)
      | (simp [run_bind, run_map, run_readReg hr, toBool, hf.cf _ e1, hf.zf _ e2]; done)
      | (simp [run_bind, run_map, run_readReg hr, toBool, hf.zf _ e2]; done))

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- The signed value of Janus' sign-extended 8-bit displacement. -/
theorem rel8_toInt (v : Nat) (hv : v < 256) :
    (BitVec.ofNat 64 (Janus.Amd64.Decode.sext 8 64 v)).toInt = if 128 ≤ v then (v : Int) - 256 else v := by
  rw [← sext_eq_8 v hv, BitVec.toInt_signExtend_of_le (by decide)]
  simp only [BitVec.toInt, BitVec.toNat_ofNat]
  split <;> split <;> omega

/-- A relative branch target in Janus' natural-number arithmetic against the signed sum. -/
theorem target_eq (next d : Nat) (dI : Int) (hd : (d : Int) = dI ∨ (d : Int) = dI + 2 ^ 64) (hn : next < 2 ^ 47)
    (hdI : -(2 ^ 32 : Int) ≤ dI ∧ dI < 2 ^ 32)
    (ht : (next + d) % 2 ^ 64 < 2 ^ 47) :
    0 ≤ (next : Int) + dI ∧ (next : Int) + dI < 2 ^ 47 ∧ ((next : Int) + dI).toNat = (next + d) % 2 ^ 64 := by
  omega

set_option maxHeartbeats 2000000 in
theorem run_jcc8 {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (opc : Nat) (ho : opc < 256) (m sib : BitVec 8) (tr : Nat) {ds : List Nat} (hds : CodeAt s tr ds) {v : Nat}
    {r : List Nat} (hle : Janus.Amd64.Decode.readLE 1 ds = some (v, r)) (sr : Nat) (hl1 : sr ≤ tr + 1)
    (hl2 : tr + 1 ≤ sr + 15) (htr : tr + 1 < 2 ^ 47) {b : Bool}
    (hcond : Janus.Amd64.condition (opc % 16) js.flags = some b)
    (hT : b = true → ((tr + 1) + Janus.Amd64.Decode.sext 8 64 v) % 2 ^ 64 < 2 ^ 47) :
    ∃ s', (x86_one_byte_jcc .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc) m sib).run s =
      .ok () s' ∧
      Rel (js.setRip (if b then BitVec.ofNat 64 (((tr + 1) + Janus.Amd64.Decode.sext 8 64 v) % 2 ^ 64)
        else BitVec.ofNat 64 (tr + 1))) s' ∧ X86Config s' := by
  obtain ⟨rf, hr, hfr⟩ := h.flags
  have hlen := check_len_ok_k sr tr 1 (by decide) hl1 hl2 htr
  have hsp := run_jcc_spec hr hfr opc ho hcond
  have hrip := h.rip
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  obtain ⟨hkl, hvv, -⟩ := readLE_sumLE _ ds hle
  have hv : v < 256 := by
    rw [hvv]; simp only [sumLE]
    have : ds.getD 0 0 < 256 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact hds.1 _ (List.getElem_mem _)
    omega
  have hrime := run_rime_size_disp hc hrip 8 hds (k := 1) (Or.inl rfl) hle (by omega)
  simp only [x86_one_byte_jcc, show (0b001#3 : BitVec 3) = BitVec.ofNat 3 1 from rfl, hlen, is_some,
    Bool.false_eq_true, ↓reduceIte, run_bind, run_pure, hsp]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, run_bind]
    rw [run_add_to_iptr (BitVec.ofNat 48 tr) 1#48 (by simp; omega)]
    refine ⟨_, run_write_iptr hc.log _ (by simp; omega), ?_, hc.set (by decide) _⟩
    simp only [BitVec.toNat_ofNat, Bool.false_eq_true, ↓reduceIte]
    rw [show (tr % 2 ^ 48 + 1 % 2 ^ 48) = tr + 1 by omega]
    exact h.setRipR _
  · simp only [↓reduceIte, run_bind, hsel, show (8 : Int).toNat = 8 from rfl, hrime]
    have ht := hT rfl
    have hd := rel8_toInt v hv
    have hTe := target_eq (tr + 1) (Janus.Amd64.Decode.sext 8 64 v) (if 128 ≤ v then (v : Int) - 256 else v)
      (by unfold Janus.Amd64.Decode.sext; split <;> (try split) <;> omega) (by omega) (by split <;> omega) ht
    have hb48 : (bits_of_int (1 + (BitVec.ofNat 64 (Janus.Amd64.Decode.sext 8 64 v)).toInt) 48).toInt =
        1 + (if 128 ≤ v then (v : Int) - 256 else v) := by
      rw [hd]; exact bits_of_int_toInt _ _ (by split <;> omega) (by split <;> omega)
    have htr48 := toInt_ofNat48 tr (by omega)
    rw [run_add_to_iptr_int _ _ (by rw [htr48, hb48]; omega) (by rw [htr48, hb48]; omega)]
    rw [htr48, hb48]
    have hT2 : ((tr : Int) + (1 + if 128 ≤ v then (v : Int) - 256 else v)).toNat =
        ((tr + 1) + Janus.Amd64.Decode.sext 8 64 v) % 2 ^ 64 := by
      rw [← hTe.2.2]; congr 1; push_cast; omega
    rw [hT2]
    refine ⟨_, run_write_iptr hc.log _ ht, ?_, hc.set (by decide) _⟩
    exact h.setRipR _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_jcc8 {bytes : List Nat} {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n)) (ho : 0x70 ≤ o ∧ o < 0x80)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ p.opsize = false ∧ ∃ v r, readLE 1 rest = some (v, r) ∧
      len = n + 2 ∧ len ≤ 15 ∧ i = .jcc (o % 16) (sext 8 64 v) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hcs : o = 0x70 ∨ o = 0x71 ∨ o = 0x72 ∨ o = 0x73 ∨ o = 0x74 ∨ o = 0x75 ∨ o = 0x76 ∨ o = 0x77 ∨
      o = 0x78 ∨ o = 0x79 ∨ o = 0x7A ∨ o = 0x7B ∨ o = 0x7C ∨ o = 0x7D ∨ o = 0x7E ∨ o = 0x7F := by omega
  cases hr : readLE 1 rest with
  | none =>
    exfalso
    rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [oneByte, hr] at hd
  | some vr =>
    obtain ⟨v, r⟩ := vr
    rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp (config := {decide := true}) only [↓reduceIte, oneByte, hr, finish, true_and, and_true,
        false_and, and_false, or_false, false_or] at hd
      by_cases hl : 15 < n + 2 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
        cases hos : p.opsize <;> cases hsg : p.seg <;>
        simp (config := {decide := true}) [hf, hk, hl, hrp, hos, hsg, lockable, withFS] at hd ⊢
      all_goals first | (simp at hd; done) | (obtain ⟨rfl, rfl⟩ := hd; first | exact ⟨v, r, rfl, rfl, by omega, rfl⟩ | exact ⟨rfl, by omega, rfl⟩ | (simp; omega))

set_option maxRecDepth 100000 in
theorem run_one_byte_jcc (opc : Nat) (hopc : 0x70 ≤ opc ∧ opc < 0x80)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_one_byte_jcc .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  have hcs : opc = 0x70 ∨ opc = 0x71 ∨ opc = 0x72 ∨ opc = 0x73 ∨ opc = 0x74 ∨ opc = 0x75 ∨ opc = 0x76 ∨ opc = 0x77 ∨
      opc = 0x78 ∨ opc = 0x79 ∨ opc = 0x7A ∨ opc = 0x7B ∨ opc = 0x7C ∨ opc = 0x7D ∨ opc = 0x7E ∨ opc = 0x7F := by omega
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

theorem modrmP1_jcc : ∀ o, 0x70 ≤ o ∧ o < 0x80 → modrmP1 o = false := by
  intro o h
  have hcs : o = 0x70 ∨ o = 0x71 ∨ o = 0x72 ∨ o = 0x73 ∨ o = 0x74 ∨ o = 0x75 ∨ o = 0x76 ∨ o = 0x77 ∨
      o = 0x78 ∨ o = 0x79 ∨ o = 0x7A ∨ o = 0x7B ∨ o = 0x7C ∨ o = 0x7D ∨ o = 0x7E ∨ o = 0x7F := by omega
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **Jcc rel8** (`70–7F`): all 16 conditions, taken and not taken. -/
theorem jcc8_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n)) (ho : 0x70 ≤ o ∧ o < 0x80)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hlk, hfs, hrep, hos, v, r, hr, rfl, hlen, rfl⟩ := decode_jcc8 hpp ho hd
  rw [step_of_decode hd] at hstep
  have hdrop : bytes.drop n = o :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hpg : prefixGroup o = 0 := by
    unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hmp : modrmP1 o = false := modrmP1_jcc o ho
  have hcs : CodeAt s (js.rip.toNat + n + 1) rest := by
    have h2 : (bytes.drop n).drop 1 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 1)
    rw [show bytes.drop (n + 1) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 1) = js.rip.toNat + n + 1 by omega] at this
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [hmp]; simp [modrmSib])
  rw [hmp] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  rw [run_one_byte_jcc o ho _ _ x hl0] at hf
  simp only [exec] at hstep
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 2)) % 2 ^ 64) = BitVec.ofNat 64 (js.rip.toNat + n + 1 + 1) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1
  rw [hnext] at hstep
  cases hc : condition (o % 16) js.flags with
  | none => simp [hc] at hstep
  | some b =>
  simp only [hc] at hstep
  have hT : b = true → ((js.rip.toNat + n + 1 + 1) + sext 8 64 v) % 2 ^ 64 < 2 ^ 47 := by
    intro hb; subst hb
    simp only [↓reduceIte, branchTo] at hstep
    split at hstep
    · rename_i h; simpa [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd] using h
    · simp at hstep
  obtain ⟨s', hs', hrel', hcfg'⟩ := run_jcc8 hrel hcfg hpr o (by omega) 0#8 0#8 (js.rip.toNat + n + 1) hcs hr
    js.rip.toNat (by omega) (by omega) (by omega) hc hT
  refine ⟨s', run_janus_x86_step (by rw [hf, hs']), ?_, hcfg'⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hstep hrel'
    subst hstep; exact hrel'
  · simp only [↓reduceIte, branchTo] at hstep hrel'
    split at hstep
    · simp only [Except.ok.injEq] at hstep; subst hstep
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show js.rip.toNat + n + 1 + 1 < 2 ^ 64 by omega)]
    · simp at hstep

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- The signed value of a `k`-byte displacement `v`. -/
def relI (k v : Nat) : Int := if 2 ^ (8 * k - 1) ≤ v then (v : Int) - 2 ^ (8 * k) else v

theorem rel_toInt48 (k : Nat) (hk : k = 1 ∨ k = 4) (v : Nat) (hv : v < 2 ^ (8 * k)) :
    (Sail.BitVec.signExtend (Sail.BitVec.truncate (BitVec.ofNat 64 (Janus.Amd64.Decode.sext (8 * k) 64 v)) 32) 48).toInt =
      relI k v := by
  have e : Sail.BitVec.truncate (BitVec.ofNat 64 (Janus.Amd64.Decode.sext (8 * k) 64 v)) 32 =
      BitVec.ofNat 32 (Janus.Amd64.Decode.sext (8 * k) 32 v) := by
    apply BitVec.eq_of_toNat_eq
    rcases hk with rfl | rfl <;> simp [Sail.BitVec.truncate, Janus.Amd64.Decode.sext] at hv ⊢ <;> split <;> omega
  rw [e]
  simp only [Sail.BitVec.signExtend]
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  simp only [BitVec.toInt, BitVec.toNat_ofNat, relI, Janus.Amd64.Decode.sext]
  rcases hk with rfl | rfl <;> simp at hv ⊢ <;> split <;> split <;> omega

theorem rel_sext (k : Nat) (hk : k = 1 ∨ k = 4) (v : Nat) (hv : v < 2 ^ (8 * k)) :
    (Janus.Amd64.Decode.sext (8 * k) 64 v : Int) = relI k v ∨
      (Janus.Amd64.Decode.sext (8 * k) 64 v : Int) = relI k v + 2 ^ 64 := by
  unfold relI Janus.Amd64.Decode.sext
  rcases hk with rfl | rfl <;> simp at hv ⊢ <;> split <;> omega

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxHeartbeats 2000000 in
theorem run_jmp_d {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (opc : Nat) (hopc : opc = 0xEB ∨ opc = 0xE9) {k : Nat} (hk : k = if opc = 0xEB then 1 else 4)
    (m sib : BitVec 8) (tr : Nat) {ds : List Nat} (hds : CodeAt s tr ds) {v : Nat}
    {r : List Nat} (hle : Janus.Amd64.Decode.readLE k ds = some (v, r)) (sr : Nat) (hl1 : sr ≤ tr + k)
    (hl2 : tr + k ≤ sr + 15) (htr : tr + k < 2 ^ 47)
    (hT : ((tr + k) + Janus.Amd64.Decode.sext (8 * k) 64 v) % 2 ^ 64 < 2 ^ 47) :
    ∃ s', (x86_near_jmp_op_en_d .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc) m sib).run s =
      .ok () s' ∧
      Rel (js.setRip (BitVec.ofNat 64 (((tr + k) + Janus.Amd64.Decode.sext (8 * k) 64 v) % 2 ^ 64))) s' ∧
      X86Config s' := by
  have hk14 : k = 1 ∨ k = 4 := by rcases hopc with rfl | rfl <;> simp [hk]
  have hrip := h.rip
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  have hb : (BitVec.ofNat 8 opc == 0xEB#8) = decide (opc = 0xEB) := by rcases hopc with rfl | rfl <;> decide
  have hsz : (if decide (opc = 0xEB) = true then (1 : Int) else 4) = ((k : Nat) : Int) := by
    rcases hopc with rfl | rfl <;> simp [hk]
  have hcr : (check_range 0 4 ((k : Nat) : Int)).run s = .ok ((k : Nat) : Int) s := by
    have hb : ((0 ≤b ((k : Nat) : Int)) && (((k : Nat) : Int) ≤b 4)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    simp only [check_range, run_bind, run_sail_assert_of hb, run_pure]
  obtain ⟨-, hvv, -⟩ := readLE_sumLE _ ds hle
  have hvl : v < 2 ^ (8 * k) := by
    rw [hvv, Nat.pow_mul]
    exact sumLE_lt _ (fun j => by
      by_cases hj : j < ds.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hds.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
  have hrime := run_rime_size_disp hc hrip 8 hds hk14 hle (by omega)
  have hadd1 : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (bits_of_int ((k : Nat) : Int) 48)).run s =
      .ok (BitVec.ofNat 48 (tr + k)) s := by
    have ez : (bits_of_int ((k : Nat) : Int) 48).toNat = k := by
      rw [bits_of_int_natCast_toNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hlen := check_len_ok sr (tr + k) hl1 hl2 htr
  have hTe := target_eq (tr + k) (Janus.Amd64.Decode.sext (8 * k) 64 v) (relI k v) (rel_sext k hk14 v hvl)
    (by omega) (by unfold relI; rcases hk14 with rfl | rfl <;> simp at hvl ⊢ <;> split <;> omega) hT
  have hoff := rel_toInt48 k hk14 v hvl
  have htr48 := toInt_ofNat48 (tr + k) (by omega)
  simp only [x86_near_jmp_op_en_d, select_operand_size, in_64bit_mode, ↓reduceIte, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, hb, run_bind, ite_pure, run_pure, hsz, hcr, hsel, show (8 : Int).toNat = 8 from rfl, Int.toNat_natCast,
    hrime, hadd1, hlen, is_some]
  rw [run_add_to_iptr_int _ _ (by rw [htr48, hoff]; omega) (by rw [htr48, hoff]; omega)]
  have hk2 : (((k : Nat) : Int) == 2) = false := by rcases hk14 with rfl | rfl <;> rfl
  simp only [run_pure, hk2, Bool.false_eq_true, ↓reduceIte]
  rw [htr48, hoff, hTe.2.2]
  exact ⟨_, run_write_iptr hc.log _ hT, h.setRipR _, hc.set (by decide) _⟩

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_jmp {bytes : List Nat} {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n)) (ho : o = 0xEB ∨ o = 0xE9)
    {k : Nat} (hk : k = if o = 0xEB then 1 else 4)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ p.opsize = false ∧ ∃ v r, readLE k rest = some (v, r) ∧
      len = n + 1 + k ∧ len ≤ 15 ∧ i = .jmp (sext (8 * k) 64 v) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  cases hr : readLE k rest with
  | none =>
    exfalso
    rcases ho with rfl | rfl <;> subst hk <;> (try simp (config := {decide := true}) only [↓reduceIte] at hr) <;>
      simp (config := {decide := true}) [oneByte, hr] at hd
  | some vr =>
    obtain ⟨v, r⟩ := vr
    rcases ho with rfl | rfl <;> subst hk <;> (try simp (config := {decide := true}) only [↓reduceIte] at hr ⊢)
    all_goals
      simp (config := {decide := true}) only [↓reduceIte, oneByte, hr, finish, true_and, and_true,
        false_and, and_false, or_false, false_or] at hd
      by_cases hl : 15 < n + 2 <;> by_cases hl5 : 15 < n + 5 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;>
        cases hk : p.lock <;> cases hos : p.opsize <;> cases hsg : p.seg <;>
        simp (config := {decide := true}) [hf, hk, hl, hl5, hrp, hos, hsg, lockable, withFS] at hd ⊢
      all_goals first | (simp at hd; done) | (obtain ⟨rfl, rfl⟩ := hd; first | exact ⟨v, r, rfl, rfl, by omega, rfl⟩ | exact ⟨rfl, by omega, rfl⟩ | (simp; omega))

set_option maxRecDepth 100000 in
theorem run_one_byte_jmp (opc : Nat) (hopc : opc = 0xEB ∨ opc = 0xE9)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_near_jmp_op_en_d .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases hopc with rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **JMP rel8/rel32** (`EB/E9`). -/
theorem jmp_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n)) (ho : o = 0xEB ∨ o = 0xE9)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  generalize hk : (if o = 0xEB then 1 else 4) = k
  obtain ⟨hlk, hfs, hrep, hos, v, r, hr, rfl, hlen, rfl⟩ := decode_jmp hpp ho hk.symm hd
  rw [step_of_decode hd] at hstep
  have hk14 : k = 1 ∨ k = 4 := by rcases ho with rfl | rfl <;> simp [← hk]
  have hdrop : bytes.drop n = o :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hpg : prefixGroup o = 0 := by
    unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hmp : modrmP1 o = false := by rcases ho with rfl | rfl <;> decide
  have hcs : CodeAt s (js.rip.toNat + n + 1) rest := by
    have h2 : (bytes.drop n).drop 1 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 1)
    rw [show bytes.drop (n + 1) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 1) = js.rip.toNat + n + 1 by omega] at this
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [hmp]; simp [modrmSib])
  rw [hmp] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  rw [run_one_byte_jmp o ho _ _ x hl0] at hf
  simp only [exec, branchTo] at hstep
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show js.rip.toNat + (n + 1 + k) < 2 ^ 64 by omega),
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 64 ∣ 2 ^ 64)] at hstep
  split at hstep
  · rename_i hT
    simp only [Except.ok.injEq] at hstep; subst hstep
    have hnk : (BitVec.ofNat 64 (js.rip.toNat + (n + 1 + k))).toNat = js.rip.toNat + n + 1 + k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [hnk] at hT ⊢
    have hT' : ((js.rip.toNat + n + 1 + k) + sext (8 * k) 64 v) % 2 ^ 64 < 2 ^ 47 := hT
    obtain ⟨s', hs', hrel', hcfg'⟩ := run_jmp_d hrel hcfg hpr o ho hk.symm 0#8 0#8 (js.rip.toNat + n + 1) hcs hr
      js.rip.toNat (by omega) (by omega) (by omega) hT'
    exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hrel', hcfg'⟩
  · simp at hstep

end JanusX86.Proofs
