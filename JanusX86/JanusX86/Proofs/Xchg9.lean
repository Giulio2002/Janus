import JanusX86.Proofs.Leave
import JanusX86.Proofs.Nop

/-! # XCHG rAX, r (`91–97`, `REX.B 90`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_xchg9 (opc : Nat) (hopc : 0x90 ≤ opc ∧ opc < 0x98)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hrb : opc = 0x90 → logbitp_bits 0 rex = true) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_xchg .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  have hc : opc = 0x90 ∨ opc = 0x91 ∨ opc = 0x92 ∨ opc = 0x93 ∨ opc = 0x94 ∨ opc = 0x95 ∨ opc = 0x96 ∨ opc = 0x97 := by
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := hrb rfl
    simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
      ↓reduceIte, Bool.false_eq_true, hl, this, Bool.and_false, run_bind, run_pure,
      show (240#8 == 0#8) = false from rfl] <;> rfl
  all_goals
    simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
      ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
      show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxHeartbeats 4000000 in
theorem run_xchg9 {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (opc : Nat) (hopc : 0x90 ≤ opc ∧ opc < 0x98)
    (m sib : BitVec 8) (tr sr : Nat) (hl1 : sr ≤ tr) (hl2 : tr ≤ sr + 15) (htr : tr < 2 ^ 47) :
    ∃ s', (x86_xchg .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc) m sib).run s =
      .ok () s' ∧
      Rel ((regWrite (regWrite js (osz p) (.reg 0) (regVal js (osz p) (.reg (rmNum p opc)))) (osz p)
        (.reg (rmNum p opc)) (regVal js (osz p) (.reg 0))).setRip (BitVec.ofNat 64 tr)) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW3 := osz_cases p
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := Or.inr hW3
  have hlen := check_len_ok sr tr hl1 hl2 htr
  have hl := hc.log
  have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) = ((osz p / 8 : Nat) : Int) := by
    unfold osz; cases rexW p <;> cases p.opsize <;> simp
  have hb : (BitVec.ofNat 8 opc == 0x86#8) = false := by
    have : opc = 0x90 ∨ opc = 0x91 ∨ opc = 0x92 ∨ opc = 0x93 ∨ opc = 0x94 ∨ opc = 0x95 ∨ opc = 0x96 ∨ opc = 0x97 := by
      omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h9 : (ash_int (Sail.BitVec.toNatInt (BitVec.ofNat 8 opc)) (Neg.neg 4) == 9) = true ∧
      (bits_of_int (ash_int (Sail.BitVec.toNatInt (BitVec.ofNat 8 opc)) (Neg.neg 4)) 4 == 0x9#4) = true := by
    have : opc = 0x90 ∨ opc = 0x91 ∨ opc = 0x92 ∨ opc = 0x93 ∨ opc = 0x94 ∨ opc = 0x95 ∨ opc = 0x96 ∨ opc = 0x97 := by
      omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hreg : ∀ k, regLocOf p.rex.isSome (osz p) k = .reg k := fun k => by
    unfold regLocOf; rw [if_neg (by rcases hW3 with e | e | e <;> omega)]
  have hn := rmNum_lt p opc
  obtain ⟨sg, hsg, -, -⟩ := run_select_segment_register hp (_get_modr_m_mod m) (_get_modr_m_r_m m) sib s
  have hidx : reg_index (Sail.BitVec.truncate (0x07#8 &&& BitVec.ofNat 8 opc) 3) rex 0b00#2 =
      BitVec.ofNat 4 (rmNum p opc) := by
    rw [oi_reg_all opc (by omega), hrexb]; exact hidx_rm hrv opc
  have hA := run_rgfi_size h hW _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) (s := s)
  have hR := run_rgfi_size h hW _ rex hrex hn (rmNum_8 p opc) (s := s)
  rw [hreg] at hA hR
  have hw0 := run_write_rgfi_size h hl hW _ rex hrex (n := 0) (by decide) (Or.inl (by decide))
    (regVal js (osz p) (.reg (rmNum p opc)))
  rw [hreg] at hw0
  have h1 := h.writeReg p.rex.isSome (n := 0) (by decide) (regVal js (osz p) (.reg (rmNum p opc)))
  rw [hreg] at h1
  have hn0 : locReg (Janus.Amd64.Loc.reg 0) < 16 := by decide
  have hl1' := hl; rw [← get?_setGpr_of_not s _ hn0 rfl] at hl1'
  have hw1 := run_write_rgfi_size h1 (by exact hl1') hW _ rex hrex hn (rmNum_8 p opc) (regVal js (osz p) (.reg 0))
  rw [hreg] at hw1
  simp only [x86_xchg, run_bind, run_select_operand_size hp hrv, hb, Bool.false_eq_true, ↓reduceIte, hsz,
    Int.toNat_natCast, hsg, h9.1, h9.2, nbytes_eq _ hW, show (0x0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl, hA, run_pure,
    show ((0 : Int)) = ((0 : Nat) : Int) from rfl, run_add_inc tr 0 (by decide) (by omega), Nat.add_zero, hlen,
    is_some, hidx, hR]
  rw [show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl, hw0]
  simp only [run_bind, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, trunc128, hw1]
  have hk := locReg_lt p.rex.isSome (osz p) (rmNum p opc) hn
  rw [hreg] at hk
  refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not _ _ hk rfl]; exact hl1') _ htr, ?_,
    ((hc.setGpr hn0 _).setGpr hk _).set (by decide) _⟩
  have h2 := h1.writeReg p.rex.isSome hn (regVal js (osz p) (.reg 0))
  rw [hreg] at h2
  exact h2.setRipR _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem decode_xchg9 {bytes : List Nat} {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n))
    (ho : (0x91 ≤ o ∧ o < 0x98) ∨ (o = 0x90 ∧ p.rex.getD 0 % 2 = 1))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ len = n + 1 ∧ len ≤ 15 ∧ i = .xchg (osz p) (.reg 0) (.reg (rmNum p o)) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have hrm : o - 0x90 + 8 * (p.rex.getD 0 % 2) = rmNum p o := by unfold rmNum; omega
  have hc : o = 0x90 ∨ o = 0x91 ∨ o = 0x92 ∨ o = 0x93 ∨ o = 0x94 ∨ o = 0x95 ∨ o = 0x96 ∨ o = 0x97 := by omega
  have hb : o = 0x90 → p.rex.getD 0 % 2 = 1 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have hb' := hb
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hou, true_and, and_true, finish, hrm,
      false_and, and_false, or_false, false_or] at hd ⊢
  all_goals
    try (have hb1 := hb rfl; simp only [hb1, show ¬ ((1 : Nat) = 0) by decide, and_false, ↓reduceIte] at hd)
    by_cases hl : 15 < n + 1 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, withFS, lockable] at hd
  all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, rfl, by omega, rfl⟩)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem logbitp0_rexByte1 {p : Prefixes} (hr : ∀ r, p.rex = some r → r < 16) (hb : p.rex.getD 0 % 2 = 1) :
    logbitp_bits 0 (BitVec.ofNat 8 (rexByte p)) = true := by
  unfold rexByte
  cases e : p.rex with
  | none => rw [e] at hb; simp at hb
  | some r => rw [e] at hb; simp only [Option.getD_some] at hb ⊢; rw [logbitp0_rex r (hr r e)]; simp [hb]

set_option maxHeartbeats 1000000 in
/-- **XCHG rAX, r** (`91–97`, and `90` with `REX.B`, i.e. `XCHG rAX, r8`), every operand size. -/
theorem xchg9_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n))
    (ho : (0x91 ≤ o ∧ o < 0x98) ∨ (o = 0x90 ∧ p.rex.getD 0 % 2 = 1))
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hlk, rfl, hlen, rfl⟩ := decode_xchg9 hpp ho hd
  rw [step_of_decode hd] at hstep
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hpg : prefixGroup o = 0 := by
    unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hmp : modrmP1 o = false := by
    have : o = 0x90 ∨ o = 0x91 ∨ o = 0x92 ∨ o = 0x93 ∨ o = 0x94 ∨ o = 0x95 ∨ o = 0x96 ∨ o = 0x97 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [hmp]; simp [modrmSib])
  rw [hmp] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hpr.rexb]; rfl
  rw [run_one_byte_xchg9 o (by omega) _ _ x hl0 rex _ _
    (fun e => by rw [hrexb]; exact logbitp0_rexByte1 hrv (by omega)) s] at hf
  have hnk : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1)) % 2 ^ 64) = BitVec.ofNat 64 (js.rip.toNat + n + 1) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1
  obtain ⟨s', hs', hrel', hcfg'⟩ := run_xchg9 hrel hcfg hpr hrv o (by omega) 0#8 0#8 (js.rip.toNat + n + 1)
    js.rip.toNat (by omega) (by omega) (by omega)
  simp only [exec, readLocRW, readLoc, writeLoc, hnk, Except.ok.injEq] at hstep
  subst hstep
  exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hrel', hcfg'⟩

end JanusX86.Proofs

