import JanusX86.Proofs.TestEG

/-! # MOV r, imm (`B0–BF`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem oi_reg_all : ∀ opc < 256, Sail.BitVec.truncate (0x07#8 &&& BitVec.ofNat 8 opc) 3 = BitVec.ofNat 3 (opc % 8) := by
  decide +kernel

theorem oi_byte_all : ∀ opc < 256, ((176 ≤b Sail.BitVec.toNatInt (BitVec.ofNat 8 opc)) &&
    (Sail.BitVec.toNatInt (BitVec.ofNat 8 opc) ≤b 183)) = decide (0xB0 ≤ opc ∧ opc < 0xB8) := by
  decide +kernel

/-- The width of `MOV r, imm` and its immediate bytes. -/
def oiW (p : Janus.Amd64.Decode.Prefixes) (o : Nat) : Nat := if o < 0xB8 then 8 else osz p

set_option maxHeartbeats 2000000 in
theorem run_mov_oi {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (opc : Nat) (hopc : 0xB0 ≤ opc ∧ opc < 0xC0)
    (m sib : BitVec 8) (tr : Nat) {ds : List Nat} (hds : CodeAt s tr ds) {v : Nat} {r : List Nat}
    (hle : Janus.Amd64.Decode.readLE (oiW p opc / 8) ds = some (v, r))
    (sr : Nat) (hl1 : sr ≤ tr + oiW p opc / 8) (hl2 : tr + oiW p opc / 8 ≤ sr + 15)
    (htr : tr + oiW p opc / 8 < 2 ^ 47) :
    ∃ s', (x86_mov_op_en_oi .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc) m sib).run s =
      .ok () s' ∧
      Rel ((regWrite js (oiW p opc) (regLocOf p.rex.isSome (oiW p opc) (opc % 8 + 8 * (p.rex.getD 0 % 2)))
          (BitVec.ofNat (oiW p opc) v)).setRip (BitVec.ofNat 64 (tr + oiW p opc / 8))) s' ∧
      X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  generalize hw : oiW p opc = w at hle hl1 hl2 htr ⊢
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [← hw]; unfold oiW; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hsz : (if decide (0xB0 ≤ opc ∧ opc < 0xB8) = true then (1 : Int) else if rexW p = true then 8
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    rw [← hw]; unfold oiW osz; by_cases h8 : opc < 0xB8 <;> cases rexW p <;> cases p.opsize <;> simp [h8] <;> omega
  obtain ⟨-, hvv, -⟩ := readLE_sumLE _ ds hle
  have hvl : v < 2 ^ (8 * (w / 8)) := by
    rw [hvv, Nat.pow_mul]
    exact sumLE_lt _ (fun j => by
      by_cases hj : j < ds.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hds.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
  have hrip := h.rip
  have hrme : (rme_size .Mode_64bit 8 (w / 8) (Sail.BitVec.signExtend (BitVec.ofNat 48 tr) 64) none 1 ":X"
      false false).run s = .ok (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * (w / 8)) v) 128) s := by
    simp only [rme_size, run_bind, run_load_code hc hrip 8 hds (by rcases hW with e | e | e | e <;> subst e <;> decide)
      hle (by omega), run_pure]
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  have hadd2 : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (bits_of_int ((w / 8 : Nat) : Int) 48)).run s =
      .ok (BitVec.ofNat 48 (tr + w / 8)) s := by
    have ez : (bits_of_int ((w / 8 : Nat) : Int) 48).toNat = w / 8 := by
      rw [bits_of_int_natCast_toNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hlen := check_len_ok sr (tr + w / 8) hl1 hl2 htr
  have hval : Sail.BitVec.truncate (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * (w / 8)) v) 128) 64 =
      (BitVec.ofNat w v).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    rcases hW with e | e | e | e <;> subst e <;> simp [Sail.BitVec.truncate, Sail.BitVec.zeroExtend] at hvl ⊢ <;> omega
  have hidx : reg_index (BitVec.ofNat 3 (opc % 8)) rex 0#2 = BitVec.ofNat 4 (opc % 8 + 8 * (p.rex.getD 0 % 2)) := by
    rw [hrexb]; have := hidx_rm hrv opc; simp only [rmNum] at this; exact this
  have hn : opc % 8 + 8 * (p.rex.getD 0 % 2) < 16 := by omega
  have hn8 : opc % 8 + 8 * (p.rex.getD 0 % 2) < 8 ∨ p.rex.isSome = true := by
    cases e : p.rex with
    | none => left; simp; omega
    | some _ => right; rfl
  have hl := hc.log
  simp only [x86_mov_op_en_oi, run_bind, oi_byte_all opc (by omega), run_select_operand_size hp hrv, hsz, hsel,
    show (8 : Int).toNat = 8 from rfl, Int.toNat_natCast, hrme, hadd2, hlen, is_some, Bool.false_eq_true, ↓reduceIte,
    run_pure, oi_reg_all opc (by omega), hidx, nbytes_eq w hW, hval,
    run_write_rgfi_size h hl hW _ rex hrex hn hn8 (BitVec.ofNat w v)]
  have hn' := locReg_lt p.rex.isSome w _ hn
  refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn' rfl]; exact hl) _ htr, ?_,
    (hc.setGpr hn' _).set (by decide) _⟩
  exact (h.writeReg _ hn _).setRipR _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_movoi {bytes : List Nat} {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n)) (ho : 0xB0 ≤ o ∧ o < 0xC0)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ ∃ v r, readLE (oiW p o / 8) rest = some (v, r) ∧
      len = n + 1 + oiW p o / 8 ∧ len ≤ 15 ∧
      i = .mov (oiW p o) (regLocOf p.rex.isSome (oiW p o) (o % 8 + 8 * (p.rex.getD 0 % 2))) (.imm v) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have hk : (if osz p = 64 then 8 else if osz p = 16 then 2 else 4) = osz p / 8 := by
    rcases osz_cases p with e | e | e <;> simp [e]
  by_cases h8 : o < 0xB8
  · have hw : oiW p o = 8 := by simp [oiW, h8]
    rw [hw]
    have hcs : o = 0xB0 ∨ o = 0xB1 ∨ o = 0xB2 ∨ o = 0xB3 ∨ o = 0xB4 ∨ o = 0xB5 ∨ o = 0xB6 ∨ o = 0xB7 := by omega
    cases hr : readLE 1 rest with
    | none =>
      exfalso
      rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) [oneByte, immU8, hr] at hd
    | some vr =>
      obtain ⟨v, r⟩ := vr
      refine ?_
      rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp (config := {decide := true}) only [↓reduceIte, oneByte, hou, immU8, hr, finish, true_and, and_true,
          false_and, and_false, or_false, false_or] at hd
        by_cases hl : 15 < n + 1 + 1 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk' : p.lock <;>
          simp (config := {decide := true}) only [hf, hk', hl, hrp, lockable_mov, ↓reduceIte, Bool.false_eq_true,
            show ∀ b n, Janus.Amd64.Decode.reg8 b n = regLocOf b 8 n from fun _ _ => rfl, withFS_mov_ri] at hd ⊢ <;>
          (try simp at hd ⊢)
      all_goals first
        | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, rfl, rfl, v, r, rfl, rfl, by omega, rfl⟩)
        | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl⟩)
  · have hw : oiW p o = osz p := by simp [oiW, h8]
    rw [hw]
    have hreg : ∀ k, regLocOf p.rex.isSome (osz p) k = .reg k := by
      intro k; unfold regLocOf; rw [if_neg (by rcases osz_cases p with e | e | e <;> omega)]
    have hcs : o = 0xB8 ∨ o = 0xB9 ∨ o = 0xBA ∨ o = 0xBB ∨ o = 0xBC ∨ o = 0xBD ∨ o = 0xBE ∨ o = 0xBF := by omega
    cases hr : readLE (osz p / 8) rest with
    | none =>
      exfalso
      rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) [oneByte, hou, hk, hr] at hd
    | some vr =>
      obtain ⟨v, r⟩ := vr
      rw [hreg]
      rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp (config := {decide := true}) only [↓reduceIte, oneByte, hou, hk, hr, finish, true_and, and_true,
          false_and, and_false, or_false, false_or] at hd
        by_cases hl : 15 < n + 1 + osz p / 8 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk' : p.lock <;>
          simp (config := {decide := true}) only [hf, hk', hl, hrp, lockable_mov, ↓reduceIte, Bool.false_eq_true] at hd ⊢ <;>
          (try simp [withFS] at hd ⊢)
      all_goals first
        | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, rfl, rfl, v, r, rfl, rfl, by omega, rfl⟩)
        | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl⟩)
        | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, by simp⟩)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_movoi (opc : Nat) (hopc : 0xB0 ≤ opc ∧ opc < 0xC0)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_mov_op_en_oi .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  have hc : opc = 0xB0 ∨ opc = 0xB1 ∨ opc = 0xB2 ∨ opc = 0xB3 ∨ opc = 0xB4 ∨ opc = 0xB5 ∨ opc = 0xB6 ∨ opc = 0xB7 ∨ opc = 0xB8 ∨ opc = 0xB9 ∨ opc = 0xBA ∨ opc = 0xBB ∨ opc = 0xBC ∨ opc = 0xBD ∨ opc = 0xBE ∨ opc = 0xBF := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
      ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
      show (240#8 == 0#8) = false from rfl] <;> rfl

theorem modrmP1_oi : ∀ o, 0xB0 ≤ o ∧ o < 0xC0 → modrmP1 o = false := by
  intro opc h
  have hc : opc = 0xB0 ∨ opc = 0xB1 ∨ opc = 0xB2 ∨ opc = 0xB3 ∨ opc = 0xB4 ∨ opc = 0xB5 ∨ opc = 0xB6 ∨ opc = 0xB7 ∨ opc = 0xB8 ∨ opc = 0xB9 ∨ opc = 0xBA ∨ opc = 0xBB ∨ opc = 0xBC ∨ opc = 0xBD ∨ opc = 0xBE ∨ opc = 0xBF := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **MOV r, imm** (`B0–BF`, incl. `MOV r64, imm64`): every register, width and prefix sequence. -/
theorem movoi_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n)) (ho : 0xB0 ≤ o ∧ o < 0xC0)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hlk, hfs, hrep, v, r, hr, rfl, hlen, rfl⟩ := decode_movoi hpp ho hd
  rw [step_of_decode hd] at hstep
  obtain ⟨V, hV, hok, rfl⟩ := exec_mov hstep
  simp only [readSrc, Except.ok.injEq] at hV; subst hV
  have hdrop : bytes.drop n = o :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hpg : prefixGroup o = 0 := by
    unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hmp : modrmP1 o = false := modrmP1_oi o ho
  have hcs : CodeAt s (js.rip.toNat + n + 1) rest := by
    have h2 : (bytes.drop n).drop 1 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 1)
    rw [show bytes.drop (n + 1) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 1) = js.rip.toNat + n + 1 by omega] at this
  have hk1 : 1 ≤ oiW p o / 8 := by unfold oiW; split <;> (try rcases osz_cases p with e | e | e) <;> simp_all
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + oiW p o / 8)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + oiW p o / 8) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [hmp]; simp [modrmSib])
  rw [hmp] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  rw [run_one_byte_movoi o ho _ _ x hl0] at hf
  obtain ⟨s', hs', hrel', hcfg'⟩ := run_mov_oi hrel hcfg hpr hrv o ho 0#8 0#8 (js.rip.toNat + n + 1) hcs hr
    js.rip.toNat (by omega) (by omega) (by omega)
  refine ⟨s', run_janus_x86_step (by rw [hf, Nat.add_zero, hs']), ?_, hcfg'⟩
  rw [hnext, locWrite_regLocOf]
  exact hrel'

end JanusX86.Proofs
