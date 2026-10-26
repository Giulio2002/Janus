import JanusX86.Proofs.Imul1

/-! # PUSH r (`50–57`), POP r (`58–5F`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_select_operand_size_d64 {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8}
    (hp : PfxRel p x rex) (hos : p.opsize = false) (ir ip : Bool) (s : SState) :
    (select_operand_size .Mode_64bit false rex false x true ir ip).run s = .ok (8 : Int) s := by
  have hopr := hp.opr
  rw [hos] at hopr
  simp only [select_operand_size, in_64bit_mode, hopr, ↓reduceIte, Bool.false_eq_true]
  cases logbitp_bits 3 rex && !ir <;> cases ip <;> simp <;> rfl

theorem loghead3_all : ∀ opc < 256, loghead_bits 3 (BitVec.ofNat 8 opc) = BitVec.ofNat 3 (opc % 8) := by
  decide +kernel

theorem and7_all : ∀ opc < 256, Sail.BitVec.truncate (BitVec.ofNat 8 opc &&& 0x07#8) 3 = BitVec.ofNat 3 (opc % 8) := by
  decide +kernel

theorem run_rgfi_size8 {s : SState} {n : Nat} (hn : n < 16) {v : BitVec 64} (h : gprVal s n = some v) (rex : BitVec 8) :
    (rgfi_size (bits_of_int (8 : Int) 4) (BitVec.ofNat 4 n) rex).run s = .ok v s := by
  simp (config := {decide := true}) only [rgfi_size, eq_bits_nat, ↓reduceIte, Bool.false_eq_true]
  exact run_rr64 hn h

theorem run_write_rgfi_size8 {s : SState} (hl : s.regs.get? .log_register_writes = some false) {n : Nat}
    (hn : n < 16) (v : BitVec 64) (rex : BitVec 8) :
    (write_rgfi_size (bits_of_int (8 : Int) 4) (BitVec.ofNat 4 n) v rex).run s = .ok () (setGpr s v n) := by
  simp (config := {decide := true}) only [write_rgfi_size, eq_bits_nat, ↓reduceIte, Bool.false_eq_true, wr64,
    toNatInt_ofNat4 n hn]
  exact run_write_rgfi hl hn v

theorem run_wme_z (asz : Nat) (eff : BitVec 64) (v : BitVec 64) (s : SState) :
    (wme_size .Mode_64bit asz 8 eff none 2 (Sail.BitVec.zeroExtend v 128) false false).run s =
      (store_bytes_to_ea .Mode_64bit asz 8 eff none 2 v false false).run s := by
  unfold wme_size
  show (store_bytes_to_ea .Mode_64bit asz 8 eff none 2 (Sail.BitVec.truncate (Sail.BitVec.zeroExtend v 128) (8 * 8))
    false false).run s = _
  congr 3; apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate, Sail.BitVec.zeroExtend]

set_option maxHeartbeats 4000000 in
theorem run_push_r {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (hos : p.opsize = false)
    (opc : Nat) (hopc : opc < 256) (m sib : BitVec 8) (tr sr : Nat) (hl1 : sr ≤ tr) (hl2 : tr ≤ sr + 15)
    (htr : tr < 2 ^ 47)
    (hacc : js.mem.accessible (js.regs 4 - 8).toNat 8 true = true) :
    ∃ s', (x86_push_general_register .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      m sib).run s = .ok () s' ∧
      Rel ((({ js with mem := js.mem.writeLE (js.regs 4 - 8).toNat 8 (js.regs (rmNum p opc)).toNat }).setReg 4
        (js.regs 4 - 8)).setRip (BitVec.ofNat 64 tr)) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
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
  have hn : rmNum p opc < 16 := by unfold rmNum; omega
  have hidx : reg_index (loghead_bits 3 (BitVec.ofNat 8 opc)) rex 0b00#2 = BitVec.ofNat 4 (rmNum p opc) := by
    rw [loghead3_all opc hopc, hrexb]; exact hidx_rm hrv opc
  obtain ⟨s1, hs1, hrel1, hcfg1, hreg1⟩ := run_store_core h hc 8 (n := 8) (by decide) _ _ 2 hla
    (js.regs (rmNum p opc)) false hacc
  have hdat : Sail.BitVec.truncate (Sail.BitVec.zeroExtend (js.regs (rmNum p opc)) 128) (8 * 8) =
      js.regs (rmNum p opc) := by
    apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate, Sail.BitVec.zeroExtend]
  have hlen := check_len_ok sr tr hl1 hl2 htr
  have hl1' := hcfg1.log
  simp only [x86_push_general_register, run_bind, run_select_operand_size_d64 hp hos, run_read_sptr h, hsp, hidx,
    run_rgfi_size8 hn (h.gpr _ hn), hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_pure, hsel,
    show (8 : Int).toNat = 8 from rfl, heff, run_alignment_checking h hc, run_wme_z]
  simp only [hs1, write_sptr, in_64bit_mode, ↓reduceIte, run_bind]
  have hw4 := run_write_rgfi hl1' (n := 4) (by decide) (js.regs 4 - 8)
  rw [show (4 : Int) = ((4 : Nat) : Int) from rfl, hw4]
  refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not _ _ (by decide) rfl]; exact hl1') _ htr, ?_,
    (hcfg1.setGpr (by decide) _).set (by decide) _⟩
  exact (hrel1.setReg (by decide) _).setRipR _

set_option maxHeartbeats 4000000 in
theorem run_pop_r {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (hos : p.opsize = false)
    (opc : Nat) (hopc : opc < 256) (m sib : BitVec 8) (tr sr : Nat) (hl1 : sr ≤ tr) (hl2 : tr ≤ sr + 15)
    (htr : tr < 2 ^ 47)
    (hacc : js.mem.accessible (js.regs 4).toNat 8 false = true)
    (hsp : (js.regs 4).toNat + 8 < 2 ^ 47) :
    ∃ s', (x86_pop_general_register .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      m sib).run s = .ok () s' ∧
      Rel (((js.setReg 4 (js.regs 4 + 8)).setReg (rmNum p opc)
        (BitVec.ofNat 64 (js.mem.readLE (js.regs 4).toNat 8))).setRip (BitVec.ofNat 64 tr)) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  have hsp4 : (js.regs 4).toNat < 2 ^ 48 := by omega
  have hadd : js.regs 4 + 8 = BitVec.ofNat 64 ((js.regs 4).toNat + 8) := by
    apply BitVec.eq_of_toNat_eq; simp
  have hspadd : (add_to_sptr .Mode_64bit (js.regs 4) (bits_of_int (8 : Int) 64)).run s =
      .ok (js.regs 4 + 8) s := by
    rw [run_add_to_sptr_int _ _ hsp4 (by omega) (by omega) (by omega), hadd]
    congr 2
  have hload := run_load_rel h hc 8 (n := 8) (by decide) (js.regs 4) (seg := 2) ⟨by decide, by decide⟩ ":R" false hacc
  have hv : Sail.BitVec.truncate (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * 8) (js.mem.readLE (js.regs 4).toNat 8)) 128) 64 =
      BitVec.ofNat 64 (js.mem.readLE (js.regs 4).toNat 8) := by
    apply BitVec.eq_of_toNat_eq
    have := Janus.Arm64.Memory.readLE_lt js.mem (js.regs 4).toNat 8
    simp [Sail.BitVec.truncate, Sail.BitVec.zeroExtend] at this ⊢
  have hn : rmNum p opc < 16 := by unfold rmNum; omega
  have hidx : reg_index (Sail.BitVec.truncate (BitVec.ofNat 8 opc &&& 0x07#8) 3) rex 0b00#2 =
      BitVec.ofNat 4 (rmNum p opc) := by
    rw [and7_all opc hopc, hrexb]; exact hidx_rm hrv opc
  have hlen := check_len_ok sr tr hl1 hl2 htr
  have hl := hc.log
  simp only [x86_pop_general_register, run_bind, run_select_operand_size_d64 hp hos, run_read_sptr h, hspadd,
    hsel, show (8 : Int).toNat = 8 from rfl, Int.reduceToNat, run_alignment_checking h hc, rme_size, hload, run_pure, hidx, hlen,
    is_some, Bool.false_eq_true, ↓reduceIte, write_sptr, in_64bit_mode, hv]
  have hw4 := run_write_rgfi hl (n := 4) (by decide) (js.regs 4 + 8)
  rw [show (4 : Int) = ((4 : Nat) : Int) from rfl, hw4]
  simp only [run_bind]
  have hl2' : (setGpr s (js.regs 4 + 8) 4).regs.get? .log_register_writes = some false := by
    rw [get?_setGpr_of_not _ _ (by decide) rfl]; exact hl
  rw [run_write_rgfi_size8 hl2' hn]
  simp only [run_bind]
  refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not _ _ hn rfl]; exact hl2') _ htr, ?_,
    (((hc.setGpr (by decide) _).setGpr hn _).set (by decide) _)⟩
  exact ((h.setReg (by decide) _).setReg hn _).setRipR _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_pushpop {bytes : List Nat} {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n)) (ho : 0x50 ≤ o ∧ o < 0x60)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ p.opsize = false ∧ len = n + 1 ∧ len ≤ 15 ∧
      i = (if o < 0x58 then .push (.loc (.reg (rmNum p o))) else .pop (rmNum p o)) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hcs : o = 0x50 ∨ o = 0x51 ∨ o = 0x52 ∨ o = 0x53 ∨ o = 0x54 ∨ o = 0x55 ∨ o = 0x56 ∨ o = 0x57 ∨
      o = 0x58 ∨ o = 0x59 ∨ o = 0x5A ∨ o = 0x5B ∨ o = 0x5C ∨ o = 0x5D ∨ o = 0x5E ∨ o = 0x5F := by omega
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, oneByte, finish, true_and, and_true,
      false_and, and_false, or_false, false_or, rmNum] at hd ⊢
    by_cases hl : 15 < n + 1 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;>
      cases hk : p.lock <;> cases hos : p.opsize <;> cases hsg : p.seg <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, hos, hsg, lockable, withFS] at hd
  all_goals (obtain ⟨rfl, rfl⟩ := hd; refine ⟨?_, ?_, ?_, ?_, rfl, by omega, ?_⟩ <;> first | rfl | assumption | (congr 3; omega) | (congr 1; omega))

set_option maxRecDepth 100000 in
theorem run_one_byte_push (opc : Nat) (hopc : 0x50 ≤ opc ∧ opc < 0x58)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_push_general_register .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  have hc : opc = 0x50 ∨ opc = 0x51 ∨ opc = 0x52 ∨ opc = 0x53 ∨ opc = 0x54 ∨ opc = 0x55 ∨ opc = 0x56 ∨ opc = 0x57 := by
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
      ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
      show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxRecDepth 100000 in
theorem run_one_byte_pop (opc : Nat) (hopc : 0x58 ≤ opc ∧ opc < 0x60)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_pop_general_register .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  have hc : opc = 0x58 ∨ opc = 0x59 ∨ opc = 0x5A ∨ opc = 0x5B ∨ opc = 0x5C ∨ opc = 0x5D ∨ opc = 0x5E ∨ opc = 0x5F := by
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
      ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
      show (240#8 == 0#8) = false from rfl] <;> rfl

theorem modrmP1_pp : ∀ o, 0x50 ≤ o ∧ o < 0x60 → modrmP1 o = false := by
  intro o h
  have hc : o = 0x50 ∨ o = 0x51 ∨ o = 0x52 ∨ o = 0x53 ∨ o = 0x54 ∨ o = 0x55 ∨ o = 0x56 ∨ o = 0x57 ∨
      o = 0x58 ∨ o = 0x59 ∨ o = 0x5A ∨ o = 0x5B ∨ o = 0x5C ∨ o = 0x5D ∨ o = 0x5E ∨ o = 0x5F := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **PUSH r64** (`50–57`, `REX.B` selects `R8–R15`; `PUSH RSP` pushes the old value). -/
theorem push_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n)) (ho : 0x50 ≤ o ∧ o < 0x58)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hlk, hfs, hrep, hos, rfl, hlen, hi⟩ := decode_pushpop hpp ⟨ho.1, by omega⟩ hd
  rw [if_pos ho.2] at hi; subst hi
  rw [step_of_decode hd] at hstep
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hpg : prefixGroup o = 0 := by
    unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hmp : modrmP1 o = false := modrmP1_pp o ⟨ho.1, by omega⟩
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [hmp]; simp [modrmSib])
  rw [hmp] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  rw [run_one_byte_push o ho _ _ x hl0] at hf
  simp only [exec, push64, readSrc, readLoc, State.getReg, BitVec.setWidth_eq] at hstep
  have hnk : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1)) % 2 ^ 64) = BitVec.ofNat 64 (js.rip.toNat + n + 1) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1
  rw [hnk] at hstep
  cases hst : store js.mem (js.regs 4 - 8).toNat 8 (js.regs (rmNum p o)).toNat with
  | error e => simp only [hst] at hstep; cases hstep
  | ok m' =>
    simp only [hst, Except.ok.injEq] at hstep; subst hstep
    obtain ⟨hacc, rfl⟩ := store_inv hst
    obtain ⟨s', hs', hrel', hcfg'⟩ := run_push_r hrel hcfg hpr hrv hos o (by omega) 0#8 0#8 (js.rip.toNat + n + 1)
      js.rip.toNat (by omega) (by omega) (by omega) hacc
    exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hrel', hcfg'⟩

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **POP r64** (`58–5F`; `POP RSP` loads `RSP`), for a stack slot that does not end at the top of
the lower half (`RSP + 8 < 2^47`: the model stops with a model error on a non-canonical new
`RSP`, Sail-x86 defect D7). -/
theorem pop_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n)) (ho : 0x58 ≤ o ∧ o < 0x60)
    (hsp : (js.regs 4).toNat + 8 < 2 ^ 47)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hlk, hfs, hrep, hos, rfl, hlen, hi⟩ := decode_pushpop hpp ⟨by omega, ho.2⟩ hd
  rw [if_neg (by omega)] at hi; subst hi
  rw [step_of_decode hd] at hstep
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hpg : prefixGroup o = 0 := by
    unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hmp : modrmP1 o = false := modrmP1_pp o ⟨by omega, ho.2⟩
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [hmp]; simp [modrmSib])
  rw [hmp] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  rw [run_one_byte_pop o ho _ _ x hl0] at hf
  simp only [exec] at hstep
  have hnk : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1)) % 2 ^ 64) = BitVec.ofNat 64 (js.rip.toNat + n + 1) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1
  rw [hnk] at hstep
  cases hld : load js.mem (js.regs 4).toNat 8 with
  | error e => simp only [hld] at hstep; cases hstep
  | ok v =>
    simp only [hld, Except.ok.injEq] at hstep; subst hstep
    unfold load at hld
    split at hld
    · rename_i hacc
      simp only [Except.ok.injEq] at hld; subst hld
      obtain ⟨s', hs', hrel', hcfg'⟩ := run_pop_r hrel hcfg hpr hrv hos o (by omega) 0#8 0#8 (js.rip.toNat + n + 1)
        js.rip.toNat (by omega) (by omega) (by omega) hacc hsp
      exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hrel', hcfg'⟩
    · simp at hld

end JanusX86.Proofs
