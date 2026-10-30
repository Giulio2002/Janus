import JanusX86.Proofs.Branch

/-! # CBW/CWDE/CDQE (`98`) and CWD/CDQ/CQO (`99`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_98 (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x98) m sib).run s =
      (x86_cbw_cwd_cdqe .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x98) m sib).run s := by
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxRecDepth 100000 in
theorem run_one_byte_99 (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x99) m sib).run s =
      (x86_cwd_cdq_cqo .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x99) m sib).run s := by
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

theorem logbitp_sw {w : Nat} (A : BitVec w) (i : Nat) (hi : i < w) (hw : w ≤ 64) :
    logbitp_bits (i : Int) (A.setWidth 64) = A.getLsbD i := by
  unfold logbitp_bits
  rw [if_pos (by simp [Sail.BitVec.length]; omega)]
  simp only [Sail.BitVec.access, Int.toNat_natCast]
  rw [getElem!_pos (A.setWidth 64) i (by omega), ← BitVec.getLsbD_eq_getElem]
  have h64 : i < 64 := by omega
  simp only [BitVec.getLsbD_setWidth, h64, decide_true, Bool.true_and]
  cases A.getLsbD i <;> rfl

theorem cwd_val {w : Nat} (hW : w = 16 ∨ w = 32 ∨ w = 64) (A : BitVec w) :
    (if logbitp_bits (ash_left_int ((w / 8 : Nat) : Int) 3 - 1) (A.setWidth 64) = true
      then sail_mask 64 (trunc (w / 8) 0xFFFFFFFFFFFFFFFF#64) else 0x0000000000000000#64) =
      (if A.msb then BitVec.allOnes w else 0).setWidth 64 := by
  have hm : A.msb = A.getLsbD (w - 1) := BitVec.msb_eq_getLsbD_last A
  rcases hW with rfl | rfl | rfl
  · rw [show ash_left_int ((16 / 8 : Nat) : Int) 3 - 1 = ((15 : Nat) : Int) by decide, logbitp_sw A 15 (by decide) (by decide),
      hm]; cases A.getLsbD (16 - 1) <;> decide
  · rw [show ash_left_int ((32 / 8 : Nat) : Int) 3 - 1 = ((31 : Nat) : Int) by decide, logbitp_sw A 31 (by decide) (by decide),
      hm]; cases A.getLsbD (32 - 1) <;> decide
  · rw [show ash_left_int ((64 / 8 : Nat) : Int) 3 - 1 = ((63 : Nat) : Int) by decide, logbitp_sw A 63 (by decide) (by decide),
      hm]; cases A.getLsbD (64 - 1) <;> decide

set_option maxHeartbeats 4000000 in
theorem run_cwd {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (m sib : BitVec 8) (tr sr : Nat) (hl1 : sr ≤ tr) (hl2 : tr ≤ sr + 15)
    (htr : tr < 2 ^ 47) :
    ∃ s', (x86_cwd_cdq_cqo .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 0x99)
      m sib).run s = .ok () s' ∧
      Rel ((js.putReg (osz p) 2 (if (js.getReg (osz p) 0).msb then BitVec.allOnes (osz p) else 0)).setRip
        (BitVec.ofNat 64 tr)) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW3 := osz_cases p
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := Or.inr hW3
  have hlen := check_len_ok sr tr hl1 hl2 htr
  have hl := hc.log
  have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) = ((osz p / 8 : Nat) : Int) := by
    unfold osz; cases rexW p <;> cases p.opsize <;> simp
  have hacc := run_rgfi_size h hW _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) (s := s)
  rw [regLocOf_zero] at hacc; simp only [regVal] at hacc
  generalize hv : (if (js.getReg (osz p) 0).msb then BitVec.allOnes (osz p) else 0) = v
  have hval := cwd_val hW3 (js.getReg (osz p) 0)
  rw [hv] at hval
  have hwr := run_write_rgfi_size h hl hW _ rex hrex (n := 2) (by decide) (Or.inl (by decide)) v
  simp only [x86_cwd_cdq_cqo, run_bind, run_select_operand_size hp hrv, Bool.false_eq_true, ↓reduceIte, hsz,
    Int.toNat_natCast, nbytes_eq _ hW, show (0x0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl, hacc, run_pure, hval,
    show (0x2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl]
  have hreg : regLocOf p.rex.isSome (osz p) 2 = .reg 2 := by
    unfold regLocOf; rw [if_neg (by rcases hW3 with e | e | e <;> omega)]
  rw [hreg] at hwr
  rw [show (2#4 : BitVec 4) = BitVec.ofNat 4 2 from rfl, hwr]
  have hn' : locReg (Janus.Amd64.Loc.reg 2) < 16 := by decide
  refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn' rfl]; exact hl) _ htr, ?_,
    (hc.setGpr hn' _).set (by decide) _⟩
  have := h.writeReg p.rex.isSome (n := 2) (by decide) v
  rw [hreg] at this
  exact this.setRipR _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions


theorem logbitp_eq {w : Nat} (x : BitVec w) (i : Nat) (hi : i < w) :
    logbitp_bits (i : Int) x = x.getLsbD i := by
  unfold logbitp_bits
  rw [if_pos (by simp [Sail.BitVec.length]; omega)]
  simp only [Sail.BitVec.access, Int.toNat_natCast]
  rw [getElem!_pos x i hi, ← BitVec.getLsbD_eq_getElem]
  cases x.getLsbD i <;> rfl

theorem cbw16 (A : BitVec 8) :
    (if logbitp_bits ((7 : Nat) : Int) (Sail.BitVec.truncate (A.setWidth 64) 32) = true then
      sail_mask 64 (trunc_signed ((2 : Nat) : Int).toNat (Sail.BitVec.signExtend
        (Sail.BitVec.truncate (Sail.BitVec.truncate (A.setWidth 64) 32) 8) 32))
    else Sail.BitVec.zeroExtend (Sail.BitVec.truncate (A.setWidth 64) 32) 64) = (A.signExtend 16).setWidth 64 := by
  rw [logbitp_eq _ 7 (by decide)]
  have hm : A.msb = A.getLsbD 7 := BitVec.msb_eq_getLsbD_last A
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  split <;> rename_i hc <;>
  simp [Sail.BitVec.truncate, Sail.BitVec.signExtend, Sail.BitVec.zeroExtend, sail_mask, trunc_signed,
    sail_mask_signed, Sail.BitVec.length, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hm] at hc ⊢ <;>
  all_goals (by_cases h8 : i < 8 <;> by_cases h16 : i < 16 <;> by_cases h32 : i < 32 <;>
    simp (disch := omega) [h8, h16, h32, hi, hc, BitVec.getLsbD_of_ge] <;> omega)

theorem cbw32 (A : BitVec 16) :
    (if logbitp_bits ((15 : Nat) : Int) (Sail.BitVec.truncate (A.setWidth 64) 32) = true then
      sail_mask 64 (trunc_signed ((4 : Nat) : Int).toNat (Sail.BitVec.signExtend
        (Sail.BitVec.truncate (Sail.BitVec.truncate (A.setWidth 64) 32) 16) 32))
    else Sail.BitVec.zeroExtend (Sail.BitVec.truncate (A.setWidth 64) 32) 64) = (A.signExtend 32).setWidth 64 := by
  rw [logbitp_eq _ 15 (by decide)]
  have hm : A.msb = A.getLsbD 15 := BitVec.msb_eq_getLsbD_last A
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  split <;> rename_i hc <;>
  simp [Sail.BitVec.truncate, Sail.BitVec.signExtend, Sail.BitVec.zeroExtend, sail_mask, trunc_signed,
    sail_mask_signed, Sail.BitVec.length, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hm] at hc ⊢ <;>
  all_goals (by_cases h8 : i < 16 <;> by_cases h32 : i < 32 <;>
    simp (disch := omega) [h8, h32, hi, hc, BitVec.getLsbD_of_ge] <;> omega)

theorem cbw64 (A : BitVec 32) :
    (if logbitp_bits ((31 : Nat) : Int) (Sail.BitVec.truncate (A.setWidth 64) 32) = true then
      sail_mask 64 (trunc_signed ((8 : Nat) : Int).toNat (Sail.BitVec.truncate (A.setWidth 64) 32))
    else Sail.BitVec.zeroExtend (Sail.BitVec.truncate (A.setWidth 64) 32) 64) = (A.signExtend 64).setWidth 64 := by
  rw [logbitp_eq _ 31 (by decide)]
  have hm : A.msb = A.getLsbD 31 := BitVec.msb_eq_getLsbD_last A
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  split <;> rename_i hc <;>
  simp [Sail.BitVec.truncate, Sail.BitVec.signExtend, Sail.BitVec.zeroExtend, sail_mask, trunc_signed,
    sail_mask_signed, Sail.BitVec.length, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hm] at hc ⊢ <;>
  all_goals (by_cases h32 : i < 32 <;>
    simp (disch := omega) [h32, hi, hc, BitVec.getLsbD_of_ge] <;> omega)

set_option maxHeartbeats 4000000 in
theorem run_cbw {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (m sib : BitVec 8) (tr sr : Nat) (hl1 : sr ≤ tr) (hl2 : tr ≤ sr + 15)
    (htr : tr < 2 ^ 47) :
    ∃ s', (x86_cbw_cwd_cdqe .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 0x98)
      m sib).run s = .ok () s' ∧
      Rel ((js.putReg (osz p) 0 ((js.getReg (osz p / 2) 0).signExtend (osz p))).setRip (BitVec.ofNat 64 tr)) s' ∧
      X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW3 := osz_cases p
  have hlen := check_len_ok sr tr hl1 hl2 htr
  have hl := hc.log
  have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) = ((osz p / 8 : Nat) : Int) := by
    unfold osz; cases rexW p <;> cases p.opsize <;> simp
  simp only [x86_cbw_cwd_cdqe, run_bind, run_select_operand_size hp hrv, Bool.false_eq_true, ↓reduceIte, hsz]
  have hreg : ∀ w, w ≠ 8 → regLocOf p.rex.isSome w 0 = .reg 0 := fun w hw => by
    unfold regLocOf; rw [if_neg hw]
  generalize hw : osz p = w at hW3 ⊢
  rcases hW3 with rfl | rfl | rfl
  · have hacc := run_rgfi_size h (w := 8) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) (s := s)
    rw [regLocOf_zero] at hacc; simp only [regVal] at hacc
    simp only [Nat.reduceDiv, show ((2 : Nat) : Int) = 2 from rfl, show ((4 : Nat) : Int) = 4 from rfl,
      show ((8 : Nat) : Int) = 8 from rfl, show ((1 : Nat) : Int) = 1 from rfl, show ((3 : Nat) : Int) = 3 from rfl]
    simp (config := {decide := true}) only [Nat.reduceDiv, check_range, run_bind, run_pure, ash_int, run_sail_assert_true,
      Sail.Int.shiftr, Sail.Int.shiftl, Sail.Nat.iterate, Int.neg_neg, ite_false, ite_true, Int.reduceNeg,
      ash_left_int, Int.reduceToNat]
    simp (config := {decide := true}) only [decide_true, Bool.and_true, Bool.true_and, run_sail_assert_true, run_bind,
      run_pure, Int.reduceDiv, Int.reduceMul, Int.reducePow, Int.reduceSub, Int.reduceToNat,
      Int.reduceLE, Int.reduceLT]
    simp only [show ((1 : Nat) : Int) = 1 from rfl, show ((2 : Nat) : Int) = 2 from rfl,
      show ((4 : Nat) : Int) = 4 from rfl, show ((3 : Nat) : Int) = 3 from rfl, Int.reduceMul, Int.reducePow,
      Int.reduceSub, show bits_of_int (1 : Int) 4 = BitVec.ofNat 4 (8 / 8) from rfl, hacc,
      show ((1 : Int) * (2 : Int) ^ (3 : Int) - 1) = ((7 : Nat) : Int) from rfl]
    rw [ite_pure, cbw16]
    have hwr := run_write_rgfi_size h hl (w := 16) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide))
      ((js.getReg 8 0).signExtend 16)
    rw [regLocOf_zero] at hwr
    simp only [run_pure, show bits_of_int (2 : Int) 4 = BitVec.ofNat 4 (16 / 8) from rfl,
      show (0x0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl, hwr]
    have hn' : locReg (Janus.Amd64.Loc.reg 0) < 16 := by decide
    refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn' rfl]; exact hl) _ htr, ?_,
      (hc.setGpr hn' _).set (by decide) _⟩
    have := h.writeReg p.rex.isSome (n := 0) (by decide) ((js.getReg 8 0).signExtend 16)
    rw [regLocOf_zero] at this
    exact this.setRipR _
  · have hacc := run_rgfi_size h (w := 16) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) (s := s)
    rw [regLocOf_zero] at hacc; simp only [regVal] at hacc
    simp only [Nat.reduceDiv, show ((2 : Nat) : Int) = 2 from rfl, show ((4 : Nat) : Int) = 4 from rfl,
      show ((8 : Nat) : Int) = 8 from rfl, show ((1 : Nat) : Int) = 1 from rfl, show ((3 : Nat) : Int) = 3 from rfl]
    simp (config := {decide := true}) only [Nat.reduceDiv, check_range, run_bind, run_pure, ash_int, run_sail_assert_true,
      Sail.Int.shiftr, Sail.Int.shiftl, Sail.Nat.iterate, Int.neg_neg, ite_false, ite_true, Int.reduceNeg,
      ash_left_int, Int.reduceToNat]
    simp (config := {decide := true}) only [decide_true, Bool.and_true, Bool.true_and, run_sail_assert_true, run_bind,
      run_pure, Int.reduceDiv, Int.reduceMul, Int.reducePow, Int.reduceSub, Int.reduceToNat,
      Int.reduceLE, Int.reduceLT]
    simp only [show ((1 : Nat) : Int) = 1 from rfl, show ((2 : Nat) : Int) = 2 from rfl,
      show ((4 : Nat) : Int) = 4 from rfl, show ((3 : Nat) : Int) = 3 from rfl, Int.reduceMul, Int.reducePow,
      Int.reduceSub, show bits_of_int (2 : Int) 4 = BitVec.ofNat 4 (16 / 8) from rfl, hacc,
      show ((2 : Int) * (2 : Int) ^ (3 : Int) - 1) = ((15 : Nat) : Int) from rfl]
    rw [ite_pure, cbw32]
    have hwr := run_write_rgfi_size h hl (w := 32) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide))
      ((js.getReg 16 0).signExtend 32)
    rw [regLocOf_zero] at hwr
    simp only [run_pure, show bits_of_int (4 : Int) 4 = BitVec.ofNat 4 (32 / 8) from rfl,
      show (0x0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl, hwr]
    have hn' : locReg (Janus.Amd64.Loc.reg 0) < 16 := by decide
    refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn' rfl]; exact hl) _ htr, ?_,
      (hc.setGpr hn' _).set (by decide) _⟩
    have := h.writeReg p.rex.isSome (n := 0) (by decide) ((js.getReg 16 0).signExtend 32)
    rw [regLocOf_zero] at this
    exact this.setRipR _
  · have hacc := run_rgfi_size h (w := 32) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) (s := s)
    rw [regLocOf_zero] at hacc; simp only [regVal] at hacc
    simp only [Nat.reduceDiv, show ((2 : Nat) : Int) = 2 from rfl, show ((4 : Nat) : Int) = 4 from rfl,
      show ((8 : Nat) : Int) = 8 from rfl, show ((1 : Nat) : Int) = 1 from rfl, show ((3 : Nat) : Int) = 3 from rfl]
    simp (config := {decide := true}) only [Nat.reduceDiv, check_range, run_bind, run_pure, ash_int, run_sail_assert_true,
      Sail.Int.shiftr, Sail.Int.shiftl, Sail.Nat.iterate, Int.neg_neg, ite_false, ite_true, Int.reduceNeg,
      ash_left_int, Int.reduceToNat]
    simp (config := {decide := true}) only [decide_true, Bool.and_true, Bool.true_and, run_sail_assert_true, run_bind,
      run_pure, Int.reduceDiv, Int.reduceMul, Int.reducePow, Int.reduceSub, Int.reduceToNat,
      Int.reduceLE, Int.reduceLT]
    simp only [show ((1 : Nat) : Int) = 1 from rfl, show ((2 : Nat) : Int) = 2 from rfl,
      show ((4 : Nat) : Int) = 4 from rfl, show ((3 : Nat) : Int) = 3 from rfl, Int.reduceMul, Int.reducePow,
      Int.reduceSub, show bits_of_int (4 : Int) 4 = BitVec.ofNat 4 (32 / 8) from rfl, hacc,
      show ((4 : Int) * (2 : Int) ^ (3 : Int) - 1) = ((31 : Nat) : Int) from rfl]
    rw [ite_pure, cbw64]
    have hwr := run_write_rgfi_size h hl (w := 64) (by decide) _ rex hrex (n := 0) (by decide) (Or.inl (by decide))
      ((js.getReg 32 0).signExtend 64)
    rw [regLocOf_zero] at hwr
    simp only [run_pure, show bits_of_int (8 : Int) 4 = BitVec.ofNat 4 (64 / 8) from rfl,
      show (0x0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl, hwr]
    have hn' : locReg (Janus.Amd64.Loc.reg 0) < 16 := by decide
    refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn' rfl]; exact hl) _ htr, ?_,
      (hc.setGpr hn' _).set (by decide) _⟩
    have := h.writeReg p.rex.isSome (n := 0) (by decide) ((js.getReg 32 0).signExtend 64)
    rw [regLocOf_zero] at this
    exact this.setRipR _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem decode_cbwcwd {bytes : List Nat} {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n)) (ho : o = 0x98 ∨ o = 0x99)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ len = n + 1 ∧ len ≤ 15 ∧ i = (if o = 0x98 then .cbw (osz p) else .cwd (osz p)) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  rcases ho with rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hou, true_and, and_true, finish,
      false_and, and_false, or_false, false_or] at hd ⊢
    by_cases hl : 15 < n + 1 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, withFS, lockable] at hd
  all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, rfl, by omega, rfl⟩)

set_option maxHeartbeats 1000000 in
/-- **CBW/CWDE/CDQE** (`98`) and **CWD/CDQ/CQO** (`99`), every operand size. -/
theorem cbwcwd_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n)) (ho : o = 0x98 ∨ o = 0x99)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hlk, rfl, hlen, rfl⟩ := decode_cbwcwd hpp ho hd
  rw [step_of_decode hd] at hstep
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hpg : prefixGroup o = 0 := by
    unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hmp : modrmP1 o = false := by rcases ho with rfl | rfl <;> decide
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [hmp]; simp [modrmSib])
  rw [hmp] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  have hnk : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1)) % 2 ^ 64) = BitVec.ofNat 64 (js.rip.toNat + n + 1) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1
  rcases ho with rfl | rfl
  · rw [run_one_byte_98 _ _ x hl0] at hf
    simp only [↓reduceIte, exec, Except.ok.injEq] at hstep; subst hstep
    obtain ⟨s', hs', hrel', hcfg'⟩ := run_cbw hrel hcfg hpr hrv 0#8 0#8 (js.rip.toNat + n + 1) js.rip.toNat
      (by omega) (by omega) (by omega)
    rw [hnk]
    exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hrel', hcfg'⟩
  · rw [run_one_byte_99 _ _ x hl0] at hf
    simp only [show ¬ ((0x99 : Nat) = 0x98) by decide, ↓reduceIte, exec, Except.ok.injEq] at hstep; subst hstep
    obtain ⟨s', hs', hrel', hcfg'⟩ := run_cwd hrel hcfg hpr hrv 0#8 0#8 (js.rip.toNat + n + 1) js.rip.toNat
      (by omega) (by omega) (by omega)
    rw [hnk]
    exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hrel', hcfg'⟩

end JanusX86.Proofs
