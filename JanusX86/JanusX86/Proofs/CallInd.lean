import JanusX86.Proofs.Stack

/-! # Indirect JMP and CALL (`FF /4`, `FF /2`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_ff_call (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hm : _get_modr_m_reg m = BitVec.ofNat 3 2) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xFF) m sib).run s =
      (x86_call_ff_2_op_en_m .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xFF) m sib).run s := by
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, hm, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxRecDepth 100000 in
theorem run_one_byte_ff_jmp (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hm : _get_modr_m_reg m = BitVec.ofNat 3 4) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xFF) m sib).run s =
      (x86_near_jmp_op_en_m .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xFF) m sib).run s := by
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, hm, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem t48 (T : BitVec 64) (hT : T.toNat < 2 ^ 47) : Sail.BitVec.truncate T 48 = BitVec.ofNat 48 T.toNat := by
  apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate]

theorem canT (T : BitVec 64) (hT : T.toNat < 2 ^ 47) :
    decide (-(2 ^ 47 : Int) ≤ T.toInt ∧ T.toInt < 2 ^ 47) = true := by
  rw [toInt_of_lt T (by omega)]; simp; omega

theorem hcr8 (s : SState) : (check_range 2 8 (8 : Int)).run s = .ok (8 : Int) s := by
  simp only [check_range, run_bind, run_sail_assert_of (show ((2 ≤b (8 : Int)) && ((8 : Int) ≤b 8)) = true by decide),
    run_pure]

set_option maxHeartbeats 4000000 in
theorem run_jmp_ind {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hos : p.opsize = false) (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr te : Nat) (T : BitVec 64) (inc : Nat)
    (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (64 / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((T.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hte : te = tr + inc) (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ te) (hl2 : te ≤ sr + 15) (htr : te < 2 ^ 47)
    (hT : T.toNat < 2 ^ 47) :
    ∃ s', (x86_near_jmp_op_en_m .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 0xFF)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧ Rel (js.setRip T) s' ∧ X86Config s' := by
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr te hl1 hl2 htr
  have hl := hc.log
  have hinc' : (bits_of_int (inc : Int) 3) = BitVec.ofNat 3 inc := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have hadd : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48)).run s =
      .ok (BitVec.ofNat 48 te) s := by
    have ez : (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48).toNat = inc := by
      simp [Sail.BitVec.zeroExtend]; omega
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  simp only [x86_near_jmp_op_en_m, h1, h2, h3, run_bind, run_select_operand_size_d64 hp hos, hcr8, hsg,
    Int.toNat_natCast, show (8 : Int).toNat = 64 / 8 from rfl, ← bits3_zero, hX sg hsg4 hsg5, hinc', hadd, hlen,
    is_some, Bool.false_eq_true, ↓reduceIte, run_pure, trunc128, BitVec.setWidth_eq, in_64bit_mode,
    run_canonical_address_p, canT T hT, Bool.not_true, t48 T hT]
  refine ⟨_, run_write_iptr hl _ hT, ?_, hc.set (by decide) _⟩
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact h.setRipR T

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem sx48_128 (a : Nat) (ha : a < 2 ^ 47) :
    Sail.BitVec.truncate (Sail.BitVec.signExtend (BitVec.ofNat 48 a) 128) (8 * 8) = BitVec.ofNat 64 a := by
  have hm : (BitVec.ofNat 48 a).msb = false := by rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp; omega
  simp only [Sail.BitVec.truncate, Sail.BitVec.signExtend]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem run_wme_push128 (asz : Nat) (eff : BitVec 64) (a : Nat) (ha : a < 2 ^ 47) (s : SState) :
    (wme_size .Mode_64bit asz 8 eff none 2 (Sail.BitVec.signExtend (BitVec.ofNat 48 a) 128) false false).run s =
      (store_bytes_to_ea .Mode_64bit asz 8 eff none 2 (BitVec.ofNat 64 a) false false).run s := by
  unfold wme_size
  show (store_bytes_to_ea .Mode_64bit asz 8 eff none 2 (Sail.BitVec.truncate (Sail.BitVec.signExtend
    (BitVec.ofNat 48 a) 128) (8 * 8)) false false).run s = _
  rw [sx48_128 a ha]

theorem setReg_setRip (J : Janus.Amd64.State) (r : Nat) (v t : BitVec 64) :
    (J.setRip t).setReg r v = (J.setReg r v).setRip t := by
  cases J; rfl

set_option maxHeartbeats 4000000 in
theorem run_call_ind {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hos : p.opsize = false) (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr te : Nat) (T : BitVec 64) (inc : Nat)
    (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (64 / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((T.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hte : te = tr + inc) (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ te) (hl2 : te ≤ sr + 15) (htr : te < 2 ^ 47)
    (hT : T.toNat < 2 ^ 47) (hacc : js.mem.accessible (js.regs 4 - 8).toNat 8 true = true) :
    ∃ s', (x86_call_ff_2_op_en_m .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 0xFF)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((({ js with mem := js.mem.writeLE (js.regs 4 - 8).toNat 8 te }).setReg 4 (js.regs 4 - 8)).setRip T) s' ∧
      X86Config s' := by
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr te hl1 hl2 htr
  have hl := hc.log
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  have hinc' : (bits_of_int (inc : Int) 3) = BitVec.ofNat 3 inc := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have hadd : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48)).run s =
      .ok (BitVec.ofNat 48 te) s := by
    have ez : (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48).toNat = inc := by
      simp [Sail.BitVec.zeroExtend]; omega
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
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
    (BitVec.ofNat 64 te) false hacc
  simp only [x86_call_ff_2_op_en_m, h1, h2, h3, run_bind, run_select_operand_size_d64 hp hos, hcr8, hsg,
    Int.toNat_natCast, show (8 : Int).toNat = 64 / 8 from rfl, ← bits3_zero, hX sg hsg4 hsg5, hinc', hadd, hlen,
    is_some, Bool.false_eq_true, ↓reduceIte, run_pure, trunc128, BitVec.setWidth_eq, in_64bit_mode,
    run_canonical_address_p, canT T hT, Bool.not_true, run_read_sptr h, select_address_size_none, hsp,
    run_alignment_checking h hc, hsel, heff]
  simp only [Nat.reduceDiv, run_wme_push128 8 _ te (by omega), hs1, t48 T hT]
  have hl1' := hcfg1.log
  rw [run_write_iptr hl1' _ hT]
  simp only [write_sptr, in_64bit_mode, ↓reduceIte]
  have e1 : (SState.set s1 .rip (BitVec.ofNat 64 T.toNat)).regs.get? .log_register_writes = some false := by
    rw [get?_set_ne _ _ (by decide)]; exact hl1'
  have := run_write_rgfi e1 (n := 4) (by decide) (js.regs 4 - 8)
  rw [show (4 : Int) = ((4 : Nat) : Int) from rfl, this]
  refine ⟨_, rfl, ?_, ((hcfg1.set (by decide) _).setGpr (by decide) _)⟩
  have := (hrel1.setRipR (BitVec.ofNat 64 T.toNat)).setReg (r := 4) (by decide) (js.regs 4 - 8)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, setReg_setRip] at this
  simpa [Nat.mod_eq_of_lt (show te < 2 ^ 64 by omega)] using this

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem decode_ffi {bytes : List Nat} {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0xFF :: m :: rest, n)) (he : m / 8 % 8 = 2 ∨ m / 8 % 8 = 4)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c)) (hlk : p.lock = false)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.rep = 0 ∧ p.opsize = false ∧ p.fs = false ∧ len = n + 1 + c ∧ len ≤ 15 ∧
      i = (if m / 8 % 8 = 2 then .callInd (rmDst p 64 mm.rm) else .jmpInd (rmDst p 64 mm.rm)) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp, hlk, Bool.false_eq_true] at hd
  have hex := modrm_ext hmd
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hex; subst hex
  rcases he with he | he
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, true_and, and_true, he,
      false_and, and_false, or_false, false_or] at hd ⊢
    by_cases hl : 15 < n + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases ho : p.opsize <;>
      cases hs : p.seg <;> cases rm <;>
      simp (config := {decide := true}) [hf, hl, hrp, ho, hs, finish, withFS, rmDst, rmLoc, regLocOf] at hd ⊢
  all_goals (obtain ⟨rfl, rfl⟩ := hd; first | exact ⟨by omega, rfl⟩ | exact ⟨rfl, by omega, rfl⟩)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

set_option maxHeartbeats 1000000 in
/-- **JMP r/m64** (`FF /4`): every register and memory form (every addressing mode, incl. RIP-relative
and SIB jump tables; Janus accepts no segment prefix here). -/
theorem jmp_ind_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0xFF :: m :: rest, n)) (he : m / 8 % 8 = 4) (hlk : p.lock = false)
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
    simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hrep, hos, hfs, rfl, hlen, rfl⟩ := decode_ffi hpp (Or.inr he) hmd hlk hd
  rw [if_neg (by omega)] at hd
  rw [step_of_decode hd] at hstep
  simp only [exec] at hstep
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  rw [hnext] at hstep
  cases hr : readLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c)) 64 (rmDst p 64 mm.rm) with
  | error e => simp only [hr] at hstep; cases hstep
  | ok T =>
  simp only [hr, branchTo] at hstep
  split at hstep
  · rename_i hT
    simp only [Except.ok.injEq] at hstep; subst hstep
    obtain ⟨hok, rfl⟩ := readLoc_loc hr
    have hm256 : m < 256 := by
      have hdrop : bytes.drop n = 0xFF :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
      exact hcode.1 m (by
        have : m ∈ bytes.drop n := by rw [hdrop]; simp
        exact List.mem_of_mem_drop this)
    have hfld := (modrm_fields m hm256).2.1
    rw [he] at hfld
    refine rm_frame hrel hcfg hcode hlim hpp (by decide) (by omega) (by omega)
      (by decide) hlk hmd (fun _ _ => hfs) (w := 64) (by decide) (k := 0) (by decide) (by omega)
      (fun sr tr x rex sib => x86_near_jmp_op_en_m .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xFF) (BitVec.ofNat 8 m) sib)
      (fun x rex _ hl sr tr sib => run_one_byte_ff_jmp sr tr x hl rex _ sib hfld s) ?_
    intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX _ _ _ _
    exact run_jmp_ind hrel hcfg hpr hos m hm256 sib tr (tr + inc) _ inc eaddr (hX true false false hok) rfl hinc8
      js.rip.toNat (by omega) (by omega) (by omega) hT
  · simp at hstep

set_option maxHeartbeats 1000000 in
/-- **CALL r/m64** (`FF /2`): every register and memory form; the return address pushed, `RSP`
and the target. -/
theorem call_ind_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0xFF :: m :: rest, n)) (he : m / 8 % 8 = 2) (hlk : p.lock = false)
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
    simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hrep, hos, hfs, rfl, hlen, rfl⟩ := decode_ffi hpp (Or.inl he) hmd hlk hd
  rw [if_pos he] at hd
  rw [step_of_decode hd] at hstep
  simp only [exec, push64] at hstep
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  rw [hnext] at hstep
  have hnk : (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c)).toNat = js.rip.toNat + n + 1 + c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  cases hr : readLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c)) 64 (rmDst p 64 mm.rm) with
  | error e => simp only [hr] at hstep; cases hstep
  | ok T =>
  simp only [hr] at hstep
  split at hstep
  · rename_i hT
    rw [hnk] at hstep
    cases hst : store js.mem (js.regs 4 - 8).toNat 8 (js.rip.toNat + n + 1 + c) with
    | error e => simp only [hst] at hstep; cases hstep
    | ok m' =>
    simp only [hst, Except.ok.injEq] at hstep; subst hstep
    obtain ⟨hacc, rfl⟩ := store_inv hst
    obtain ⟨hok, rfl⟩ := readLoc_loc hr
    have hm256 : m < 256 := by
      have hdrop : bytes.drop n = 0xFF :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
      exact hcode.1 m (by
        have : m ∈ bytes.drop n := by rw [hdrop]; simp
        exact List.mem_of_mem_drop this)
    have hfld := (modrm_fields m hm256).2.1
    rw [he] at hfld
    refine rm_frame hrel hcfg hcode hlim hpp (by decide) (by omega) (by omega)
      (by decide) hlk hmd (fun _ _ => hfs) (w := 64) (by decide) (k := 0) (by decide) (by omega)
      (fun sr tr x rex sib => x86_call_ff_2_op_en_m .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xFF) (BitVec.ofNat 8 m) sib)
      (fun x rex _ hl sr tr sib => run_one_byte_ff_call sr tr x hl rex _ sib hfld s) ?_
    intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX _ _ _ _
    have := run_call_ind hrel hcfg hpr hos m hm256 sib tr (tr + inc) _ inc eaddr (hX true false false hok) rfl hinc8
      js.rip.toNat (by omega) (by omega) (by omega) hT hacc
    rwa [hinc'] at this
  · simp at hstep

end JanusX86.Proofs
