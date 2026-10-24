import JanusASL.Proofs.Step
import JanusASL.Proofs.AddSubImm

/-! # Proved: ADD/ADDS/SUB/SUBS (immediate), the whole encoding class

For every 32-bit word `w` whose bits 28:23 are `100010` (the A64 "Add/subtract (immediate)"
class `sf op S 100010 sh imm12 Rn Rd`, 2^26 words) and every Sail state related to a Janus state,
the generated ASL step completes and yields a state related to `Janus.Arm64.step w js`. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxHeartbeats 4000000 in
theorem run_DataProcImm_0 {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 34)
    (hk : (w / 2 ^ 29) % 4 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1)) (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (fld w 0 5) (fld w 5 5) (fld w 10 12) (fld w 22 1) (fld w 29 1) (fld w 30 1)
        (fld w 31 1)).run (s.set .SEE 18) := by
  have c0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (0x22#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, c0, andM, toBool, run_pure, run_readReg hs, Bool.false_eq_true, ite_false,
    show ((-1 : Int) < 18) = True from by decide, decide_true, ite_true, run_writeReg]

set_option maxHeartbeats 4000000 in
theorem run_DataProcImm_1 {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 34)
    (hk : (w / 2 ^ 29) % 4 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1)) (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (fld w 0 5) (fld w 5 5) (fld w 10 12) (fld w 22 1) (fld w 29 1) (fld w 30 1)
        (fld w 31 1)).run (s.set .SEE 19) := by
  have c0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (0x22#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have c1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (0x62#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, c0, c1, andM, toBool, run_pure, run_readReg hs, Bool.false_eq_true, ite_false,
    show ((-1 : Int) < 19) = True from by decide, decide_true, ite_true, run_writeReg]

set_option maxHeartbeats 4000000 in
theorem run_DataProcImm_2 {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 34)
    (hk : (w / 2 ^ 29) % 4 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1)) (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (fld w 0 5) (fld w 5 5) (fld w 10 12) (fld w 22 1) (fld w 29 1) (fld w 30 1)
        (fld w 31 1)).run (s.set .SEE 20) := by
  have c0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (0x22#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have c1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (0x62#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have c2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (0xa2#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, c0, c1, c2, andM, toBool, run_pure, run_readReg hs, Bool.false_eq_true, ite_false,
    show ((-1 : Int) < 20) = True from by decide, decide_true, ite_true, run_writeReg]

set_option maxHeartbeats 4000000 in
theorem run_DataProcImm_3 {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 34)
    (hk : (w / 2 ^ 29) % 4 = 3) {s : SState} (hs : s.regs.get? .SEE = some (-1)) (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (fld w 0 5) (fld w 5 5) (fld w 10 12) (fld w 22 1) (fld w 29 1) (fld w 30 1)
        (fld w 31 1)).run (s.set .SEE 21) := by
  have c0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (0x22#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have c1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (0x62#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have c2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (0xa2#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have c3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (0xe2#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, c0, c1, c2, c3, andM, toBool, run_pure, run_readReg hs, Bool.false_eq_true, ite_false,
    show ((-1 : Int) < 21) = True from by decide, decide_true, ite_true, run_writeReg]

/-- The immediate as the ASL decoder forms it: `ZeroExtend(imm12)` or `ZeroExtend(imm12:Zeros(12))`. -/
def aslImm (N : Nat) (sh : BitVec 1) (imm12 : BitVec 12) : BitVec N :=
  match sh with
  | 0 => Sail.BitVec.zeroExtend imm12 N
  | _ => Sail.BitVec.zeroExtend (imm12 +++ (Zeros (n := 12))) N




theorem run_decode_add_addsub_imm (Rd Rn : BitVec 5) (imm12 : BitVec 12) (sh S op sf : BitVec 1) (s : SState) :
    (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd.toNat (if sf == 1#1 then 64 else 32)
        (aslImm (if sf == 1#1 then 64 else 32) sh imm12) Rn.toNat (S == 1#1) (op == 1#1)).run s := by
  unfold decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate
  simp only [run_bind, run_undefined_bitvector]
  rfl

theorem run_decode_adds_addsub_imm (Rd Rn : BitVec 5) (imm12 : BitVec 12) (sh S op sf : BitVec 1) (s : SState) :
    (decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd.toNat (if sf == 1#1 then 64 else 32)
        (aslImm (if sf == 1#1 then 64 else 32) sh imm12) Rn.toNat (S == 1#1) (op == 1#1)).run s := by
  unfold decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate
  simp only [run_bind, run_undefined_bitvector]
  rfl

theorem run_decode_sub_addsub_imm (Rd Rn : BitVec 5) (imm12 : BitVec 12) (sh S op sf : BitVec 1) (s : SState) :
    (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd.toNat (if sf == 1#1 then 64 else 32)
        (aslImm (if sf == 1#1 then 64 else 32) sh imm12) Rn.toNat (S == 1#1) (op == 1#1)).run s := by
  unfold decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate
  simp only [run_bind, run_undefined_bitvector]
  rfl

theorem run_decode_subs_addsub_imm (Rd Rn : BitVec 5) (imm12 : BitVec 12) (sh S op sf : BitVec 1) (s : SState) :
    (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd.toNat (if sf == 1#1 then 64 else 32)
        (aslImm (if sf == 1#1 then 64 else 32) sh imm12) Rn.toNat (S == 1#1) (op == 1#1)).run s := by
  unfold decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate
  simp only [run_bind, run_undefined_bitvector]
  rfl
/-- What the generated ASL computes for an add/sub-immediate word, at width `N` (in Janus terms). -/
def aslAddSubImmSpecN (js : Janus.Arm64.State) (w N : Nat) : Janus.Arm64.State :=
  let res := Janus.Arm64.addSub (js.getXSP N (fld w 5 5).toNat) (aslImm N (fld w 22 1) (fld w 10 12))
    (fld w 30 1 == 1#1)
  if fld w 29 1 == 1#1 then (js.setX (fld w 0 5).toNat res.1).setFlags res.2
  else js.setXSP (fld w 0 5).toNat res.1

def aslAddSubImmSpec (js : Janus.Arm64.State) (w : Nat) : Janus.Arm64.State :=
  aslAddSubImmSpecN js w (if fld w 31 1 == 1#1 then 64 else 32)

set_option maxHeartbeats 8000000 in
theorem asl_addSubImm {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 34)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (aslAddSubImmSpec js w) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  have hcls : (w / 2 ^ 26) % 8 = 4 := by omega
  rw [run_DecodeA64_DPImm hw hcls]
  have hs0 : (stepEntry s (BitVec.ofNat 32 w)).regs.get? .SEE = some (-1) := by
    simp only [stepEntry]; repeat rw [get?_set_ne _ _ (by decide)]
    exact get?_set_SEE _ _
  have hk : (w / 2 ^ 29) % 4 < 4 := Nat.mod_lt _ (by decide)
  have hd : (fld w 0 5).toNat < 32 := fld_lt w 0 5
  have hn : (fld w 5 5).toNat < 32 := fld_lt w 5 5
  have hR := h.stepEntry (BitVec.ofNat 32 w)
  have hbt0 : (stepEntry s (BitVec.ofNat 32 w)).regs.get? .__BranchTaken = some false := by
    simp only [stepEntry]; repeat rw [get?_set_ne _ _ (by decide)]
    exact get?_set_BranchTaken _ _
  -- the four clauses
  rcases (show (w / 2 ^ 29) % 4 = 0 ∨ (w / 2 ^ 29) % 4 = 1 ∨ (w / 2 ^ 29) % 4 = 2 ∨ (w / 2 ^ 29) % 4 = 3 by omega)
    with hk | hk | hk | hk
  · rw [run_DataProcImm_0 hw hc hk hs0, run_decode_add_addsub_imm]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_imm
      (hR.set_other .SEE (18 : Int) rfl (by decide) (by decide) (by decide)) (width_cases w) hd hn
      (aslImm (if fld w 31 1 == 1#1 then 64 else 32) (fld w 22 1) (fld w 10 12)) (fld w 29 1 == 1#1)
      (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcImm_1 hw hc hk hs0, run_decode_adds_addsub_imm]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_imm
      (hR.set_other .SEE (19 : Int) rfl (by decide) (by decide) (by decide)) (width_cases w) hd hn
      (aslImm (if fld w 31 1 == 1#1 then 64 else 32) (fld w 22 1) (fld w 10 12)) (fld w 29 1 == 1#1)
      (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcImm_2 hw hc hk hs0, run_decode_sub_addsub_imm]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_imm
      (hR.set_other .SEE (20 : Int) rfl (by decide) (by decide) (by decide)) (width_cases w) hd hn
      (aslImm (if fld w 31 1 == 1#1 then 64 else 32) (fld w 22 1) (fld w 10 12)) (fld w 29 1 == 1#1)
      (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcImm_3 hw hc hk hs0, run_decode_subs_addsub_imm]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_imm
      (hR.set_other .SEE (21 : Int) rfl (by decide) (by decide) (by decide)) (width_cases w) hd hn
      (aslImm (if fld w 31 1 == 1#1 then 64 else 32) (fld w 22 1) (fld w 10 12)) (fld w 29 1 == 1#1)
      (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩

theorem toNat_append_zeros12 (x : BitVec 12) : (x +++ (0#12 : BitVec 12)).toNat = x.toNat * 4096 := by
  show (x ++ 0#12).toNat = _
  rw [BitVec.toNat_append]; simp [Nat.shiftLeft_eq]

theorem aslImm_eq (N : Nat) (hN : N = 32 ∨ N = 64) (w : Nat) (hw : w < 2 ^ 32) :
    aslImm N (fld w 22 1) (fld w 10 12) =
      BitVec.ofNat N (if Janus.Arm64.bit w 22 then Janus.Arm64.bits w 21 10 * 2 ^ 12 else Janus.Arm64.bits w 21 10) := by
  have h22 := fld_bit w 22 hw
  have hi := fld_toNat w 10 12 hw
  have hb : Janus.Arm64.bits w 21 10 = (w / 2 ^ 10) % 2 ^ 12 := by
    simp [Janus.Arm64.bits, Nat.shiftRight_eq_div_pow]
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with e | e
  · have h0 : fld w 22 1 = 0#1 := BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw, e]; rfl)
    have hbit : Janus.Arm64.bit w 22 = false := by rw [← h22, h0]; decide
    rw [h0, hbit]
    simp only [aslImm, Bool.false_eq_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    rcases hN with rfl | rfl <;> simp [Sail.BitVec.zeroExtend, hi, hb] <;> omega
  · have h1 : fld w 22 1 = 1#1 := BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw, e]; rfl)
    have hbit : Janus.Arm64.bit w 22 = true := by rw [← h22, h1]; decide
    rw [h1, hbit]
    simp only [aslImm, ite_true]
    apply BitVec.eq_of_toNat_eq
    rcases hN with rfl | rfl <;> simp [Sail.BitVec.zeroExtend, hb, Zeros, BitVec.zero, toNat_append_zeros12, hi] <;> omega

theorem specN_eq {w : Nat} (hw : w < 2 ^ 32) (js : Janus.Arm64.State) (N : Nat) (hN : N = 32 ∨ N = 64) :
    aslAddSubImmSpecN js w N =
      Janus.Arm64.execAddSubImm N js (Janus.Arm64.bit w 30) (Janus.Arm64.bit w 29) (Janus.Arm64.bit w 22)
        (Janus.Arm64.bits w 21 10) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0) := by
  unfold aslAddSubImmSpecN Janus.Arm64.execAddSubImm
  rw [bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw, fld_bit w 30 hw, fld_bit w 29 hw, aslImm_eq N hN w hw]

theorem spec_eq {w : Nat} (hw : w < 2 ^ 32) (js : Janus.Arm64.State) :
    aslAddSubImmSpec js w =
      if Janus.Arm64.bit w 31 then
        Janus.Arm64.execAddSubImm 64 js (Janus.Arm64.bit w 30) (Janus.Arm64.bit w 29) (Janus.Arm64.bit w 22)
          (Janus.Arm64.bits w 21 10) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)
      else
        Janus.Arm64.execAddSubImm 32 js (Janus.Arm64.bit w 30) (Janus.Arm64.bit w 29) (Janus.Arm64.bit w 22)
          (Janus.Arm64.bits w 21 10) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0) := by
  unfold aslAddSubImmSpec
  rw [fld_bit w 31 hw]
  cases Janus.Arm64.bit w 31
  · exact specN_eq hw js 32 (Or.inl rfl)
  · exact specN_eq hw js 64 (Or.inr rfl)

theorem spec_pc (js : Janus.Arm64.State) (w : Nat) : (aslAddSubImmSpec js w).pc = js.pc := by
  unfold aslAddSubImmSpec aslAddSubImmSpecN
  dsimp only
  split <;> simp [Janus.Arm64.State.setX, Janus.Arm64.State.setXSP, Janus.Arm64.State.writeZR,
    Janus.Arm64.State.writeSP, Janus.Arm64.State.setFlags] <;> split <;> rfl

/-- **ADD/ADDS/SUB/SUBS (immediate)**: for every word of the encoding class (bits 28:23 =
`100010`) and every related pair of states, Janus' `step` and the generated ASL agree. -/
theorem addSubImm_agree {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100010)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_addSubImm hw hc h (js.pc.toNat : Int)
  refine step_agree h ⟨s2, hrun, hrel, hbt⟩ (spec_pc js w) ?_
  rw [Janus.Arm64.step_of_decode (decode_addSubImm_class hw hc)]
  simp only [Janus.Arm64.exec, spec_eq hw]
  congr 1
  split <;> simp [Janus.Arm64.State.next, ← spec_pc js w, spec_eq hw, *]

end JanusASL.Proofs
