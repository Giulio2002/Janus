import JanusX86.Proofs.AluAI

/-! # ALU (E, I) forms: `80/81/83 /0..7` and `TEST r/m, imm` (`F6/F7 /0`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem toNat_slice0 (len : Nat) (n : Int) : (Sail.get_slice_int len n 0).toNat = (n % (2 ^ len : Nat)).toNat := by
  simp only [Sail.get_slice_int, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.zero_add, BitVec.toNat_ofInt]
  have h2 : ((2 ^ (len + 1) : Nat) : Int) = ((2 ^ len : Nat) : Int) * 2 := by rw [Nat.pow_succ]; push_cast; rfl
  have hN : (0 : Int) < ((2 ^ len : Nat) : Int) := by have := Nat.two_pow_pos len; omega
  have hx : 0 ≤ n % ((2 ^ (len + 1) : Nat) : Int) := Int.emod_nonneg _ (by omega)
  rw [← Int.toNat_natCast (2 ^ len), ← Int.toNat_emod hx (by omega), h2,
    Int.emod_emod_of_dvd _ (Int.dvd_mul_right _ _)]
  rw [Int.toNat_natCast]

theorem bits_to_bool_eq : ∀ b : BitVec 1, bits_to_bool b = decide (b.toNat = 1) := by decide

theorem toNat_slice1 (j : Int) (i : Nat) : (Sail.get_slice_int 1 j i).toNat = (j % (2 ^ (i + 2) : Nat)).toNat / 2 ^ i % 2 := by
  simp only [Sail.get_slice_int, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow,
    Nat.pow_one, show i + 1 + 1 = i + 2 by omega]

theorem ite_pure {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then (pure a : SailM α) else pure b) = pure (if c then a else b) := by split <;> rfl

theorem ash_k : ash_left_int ((1 : Nat) : Int) 3 = 8 ∧ ash_left_int ((2 : Nat) : Int) 3 = 16 ∧
    ash_left_int ((4 : Nat) : Int) 3 = 32 ∧ ash_left_int ((8 : Nat) : Int) 3 = 64 := by decide

theorem run_logext (k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 4) (v : Nat) (hv : v < 2 ^ (8 * k)) (s : SState) :
    (binary_logext (ash_left_int (k : Int) 3) (v : Int)).run s =
      .ok (if 2 ^ (8 * k - 1) ≤ v then (v : Int) - 2 ^ (8 * k) else v) s := by
  obtain ⟨a1, a2, a4, a8⟩ := ash_k
  rcases hk with rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [binary_logext, a1, a2, a4, logbitp_int, binary_logapp, loghead_int, run_bind,
    run_sail_assert_true, run_pure, bits_to_bool_eq, toNat_slice1, Sail.BitVec.toNatInt, toNat_slice0] <;>
  simp only [ite_pure, run_pure] <;> simp <;> congr 1 <;> split <;> split <;> omega

theorem imm_head (k w : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 4) (he : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (hke : 8 * k ≤ w)
    (v : Nat) (hv : v < 2 ^ (8 * k)) :
    bits_of_int (loghead_int (ash_left_int ((w / 8 : Nat) : Int) 3) (if 2 ^ (8 * k - 1) ≤ v then (v : Int) - 2 ^ (8 * k) else v)) 64 =
      (BitVec.ofNat w (Janus.Amd64.Decode.sext (8 * k) w v)).setWidth 64 := by
  obtain ⟨a1, a2, a4, a8⟩ := ash_k
  apply BitVec.eq_of_toNat_eq
  rcases hk with rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl | rfl <;> (try omega) <;>
  simp only [Nat.reduceDiv] <;>
  simp (config := {decide := true}) only [loghead_int, a1, a2, a4, a8, bits_of_int, toNat_slice0, Sail.BitVec.toNatInt,
    Janus.Amd64.Decode.sext, BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;> simp <;> split <;> (try split) <;> omega

theorem imm_trunc (k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 4) (v : Nat) (hv : v < 2 ^ (8 * k)) :
    Sail.BitVec.toNatInt (Sail.BitVec.truncate (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * k) v) 128) 32) = (v : Int) := by
  rcases hk with rfl | rfl | rfl <;> simp [Sail.BitVec.toNatInt, Sail.BitVec.truncate, Sail.BitVec.zeroExtend] <;> omega

theorem ei_bytes : ∀ opc, (opc = 0x80 ∨ opc = 0x81 ∨ opc = 0x83 ∨ opc = 0xF6 ∨ opc = 0xF7) →
    ((BitVec.ofNat 8 opc == 0x80#8) || ((BitVec.ofNat 8 opc == 0x82#8) || (BitVec.ofNat 8 opc == 0xF6#8))) =
      decide (opc = 0x80 ∨ opc = 0xF6) ∧
    ((BitVec.ofNat 8 opc == 0x80#8) || ((BitVec.ofNat 8 opc == 0x82#8) || ((BitVec.ofNat 8 opc == 0x83#8) ||
      (BitVec.ofNat 8 opc == 0xF6#8)))) = decide (¬ (opc = 0x81 ∨ opc = 0xF7)) := by
  intro opc h; rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxHeartbeats 2000000 in
theorem run_alu_e_i {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (operation : Nat) (op : Janus.Amd64.AluOp)
    (hop : operation = sailOp op ∨ (operation = 7 ∧ op = .and))
    (opc : Nat) (hopc : opc = 0x80 ∨ opc = 0x81 ∨ opc = 0x83 ∨ opc = 0xF6 ∨ opc = 0xF7)
    {w : Nat} (hw : w = if opc = 0x80 ∨ opc = 0xF6 then 8 else osz p)
    {k : Nat} (hk : k = if opc = 0x81 ∨ opc = 0xF7 then immBytes w else 1)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr te : Nat) (V : BitVec w) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 k)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (J : BitVec w → Janus.Amd64.State)
    (hWr : ¬ (operation = 8 ∨ operation = 7) → ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 → ∀ y : BitVec w, ∃ s1,
      (x86_operand_to_reg_mem .Mode_64bit (w / 8) true false ((y.setWidth 64).setWidth 128) sg eaddr x rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run s = .ok () s1 ∧
      Rel (J y) s1 ∧ X86Config s1 ∧ (J y).df = js.df ∧ s1.regs.get? .rflags = s.regs.get? .rflags ∧
      s1.regs.get? .janus_undef = s.regs.get? .janus_undef)
    (hte : te = tr + inc) {ds : List Nat} (hds : CodeAt s te ds) {v : Nat} {r : List Nat}
    (hle : Janus.Amd64.Decode.readLE k ds = some (v, r))
    (sr : Nat) (hl1 : sr ≤ te + k) (hl2 : te + k ≤ sr + 15) (htr : te + k < 2 ^ 47)
    (cc : Bool) (hcf : (op = .adc ∨ op = .sbb) → js.flags.cf = some cc) :
    ∃ s', (x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i operation .Mode_64bit (BitVec.ofNat 48 sr)
      (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc) (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (((if operation = 8 ∨ operation = 7 then js
          else J (aluRes op V (BitVec.ofNat w (Janus.Amd64.Decode.sext (8 * k) w v)) cc).1).setFlags
          (aluRes op V (BitVec.ofNat w (Janus.Amd64.Decode.sext (8 * k) w v)) cc).2).setRip
          (BitVec.ofNat 64 (te + k))) s' ∧
      X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hlb : logbitp_bits 3 rex = rexW p := by rw [hrexb]; exact logbitp3_rexByte hrv
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨hb1, hb2⟩ := ei_bytes opc hopc
  have hes : (if decide (opc = 0x80 ∨ opc = 0xF6) = true then (1 : Int) else if rexW p = true then 8
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    subst hw; unfold osz
    by_cases h1 : opc = 0x80 ∨ opc = 0xF6 <;> cases hx : rexW p <;> cases hy : p.opsize <;> simp_all
  have his : (if decide (¬ (opc = 0x81 ∨ opc = 0xF7)) = true then (1 : Int) else if rexW p = true then 4
      else if p.opsize = true then 2 else 4) = ((k : Nat) : Int) := by
    subst hk hw; unfold osz immBytes
    rcases hopc with rfl | rfl | rfl | rfl | rfl <;> cases hx : rexW p <;> cases hy : p.opsize <;> simp_all
  have hk4 : k = 1 ∨ k = 2 ∨ k = 4 := by
    subst hk; unfold immBytes; split <;> (try split) <;> (try split) <;> simp
  have hkw : 8 * k ≤ w := by
    subst hk hw; unfold immBytes osz
    rcases hopc with rfl | rfl | rfl | rfl | rfl <;> cases hx : rexW p <;> cases hy : p.opsize <;> simp_all
  have hrip := h.rip
  obtain ⟨-, hvv, -⟩ := readLE_sumLE _ ds hle
  have hvl : v < 2 ^ (8 * k) := by
    rw [hvv, Nat.pow_mul]
    exact sumLE_lt _ (fun j => by
      by_cases hj : j < ds.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hds.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
  have hrme : (rme_size .Mode_64bit 8 k (Sail.BitVec.signExtend (BitVec.ofNat 48 te) 64) none 1 ":X"
      false false).run s = .ok (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * k) v) 128) s := by
    simp only [rme_size, run_bind, run_load_code hc hrip 8 hds (by omega) hle (by omega), run_pure]
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  have hadd1 : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (bits_of_int (inc : Int) 48)).run s =
      .ok (BitVec.ofNat 48 te) s := by
    have ez : (bits_of_int (inc : Int) 48).toNat = inc := by
      rw [bits_of_int_natCast_toNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hadd2 : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 te) (bits_of_int ((k : Nat) : Int) 48)).run s =
      .ok (BitVec.ofNat 48 (te + k)) s := by
    have ez : (bits_of_int ((k : Nat) : Int) 48).toNat = k := by
      rw [bits_of_int_natCast_toNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hlen := check_len_ok sr (te + k) hl1 hl2 htr
  have hk3 : bits_of_int ((k : Nat) : Int) 3 = BitVec.ofNat 3 k := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have hcr : (check_range 1 4 ((k : Nat) : Int)).run s = .ok ((k : Nat) : Int) s := by
    have hb : ((1 ≤b ((k : Nat) : Int)) && (((k : Nat) : Int) ≤b 4)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    simp only [check_range, run_bind, run_sail_assert_of hb, run_pure]
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  let c' := (_get_rflagsbits_cf rf == 1#1)
  have hc' : _get_rflagsbits_cf rf = BitVec.ofBool c' := bv1_ofBool _
  generalize hY : BitVec.ofNat w (Janus.Amd64.Decode.sext (8 * k) w v) = Y
  have hcc : aluRes op V Y c' = aluRes op V Y cc := by
    apply aluRes_c; intro hop
    have := hfr.cf cc (hcf hop)
    show (_get_rflagsbits_cf rf == 1#1) = cc
    rw [this]; cases cc <;> rfl
  have hspec : (gpr_arith_logic_spec (w / 8) operation (V.setWidth 64) (Y.setWidth 64) rf).run s =
      .ok ((aluRes op V Y cc).1.setWidth 64, (aluOut op rf (aluRes op V Y cc).2).1,
        (aluOut op rf (aluRes op V Y cc).2).2) s := by
    rw [← hcc]
    rcases hop with rfl | ⟨rfl, rfl⟩
    · exact run_gpr_arith_logic_spec op hW _ _ rf c' hc' s
    · rw [spec7 _ (by rcases hW with e | e | e | e <;> subst e <;> simp)]
      exact run_gpr_arith_logic_spec .and hW _ _ rf c' hc' s
  have himm := imm_head k w hk4 hW hkw v hvl
  rw [hY] at himm
  simp only [x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i, h1, h2, h3, run_bind, run_select_operand_size hp hrv,
    hb1, hb2, hes, his, hcr, hsg, hk3, hX sg hsg4 hsg5, hadd1, hsel, show (8 : Int).toNat = 8 from rfl,
    Int.toNat_natCast, hrme, run_pure, run_logext k hk4 v hvl, imm_trunc k hk4 v hvl, himm, hadd2, tsx48, hlen,
    is_some, Bool.false_eq_true, ↓reduceIte, run_readReg hr, trunc128, hspec]
  generalize hR : aluRes op V Y cc = R
  have hfR : FlagsRel R.2 js.df (wurf rf (aluOut op rf R.2).1 (aluOut op rf R.2).2 u) := by
    rw [← hR]; exact flagsRel_aluOut hfr op _ _ cc u
  by_cases hnw : operation = 8 ∨ operation = 7
  · have hb : (operation == 8 || operation == 7) = true := by rcases hnw with e | e <;> simp [e]
    simp only [hb, ↓reduceIte, run_pure, run_write_user_rflags hr hu hc.log, hnw]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hc.log) _ htr, ?_, ?_⟩
    · exact h.flagsRip R.2 _ hfR _
    · exact (hc.set (by decide) _).set (by decide) _
  · have hb : (operation == 8 || operation == 7) = false := by simp; omega
    simp only [hb, hnw, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨s1, hs1, hrel1, hcfg1, hdf1, hr1, hu1⟩ := hWr hnw sg hsg4 hsg5 R.1
    simp only [Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, hs1]
    have e1 : s1.regs.get? .rflags = some rf := by rw [hr1]; exact hr
    have e2 : s1.regs.get? .janus_undef = some u := by rw [hu1]; exact hu
    simp only [run_write_user_rflags e1 e2 hcfg1.log]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hcfg1.log) _ htr, ?_, ?_⟩
    · exact hrel1.flagsRip R.2 _ (by rw [hdf1]; exact hfR) _
    · exact (hcfg1.set (by decide) _).set (by decide) _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 in
/-- `execAlu` in a uniform shape (`aluRes`, the carry read only by `ADC`/`SBB`). -/
theorem execAlu_eq (js : State) (next : BitVec 64) (op : AluOp) (w : Nat) (dst : Loc) (src : Src) :
    execAlu js next op w dst src =
      match readSrc js next w src with
      | .error e => .error e
      | .ok Y =>
        match (if op = .cmp then readLoc js next w dst else readLocRW js next w dst) with
        | .error e => .error e
        | .ok X =>
          match (if op = .adc ∨ op = .sbb then js.flags.cf else some false) with
          | none => .error (.undefinedFlag js.rip.toNat)
          | some c =>
            if op = .cmp then .ok ((js.setFlags (aluRes op X Y c).2).setRip next)
            else
              match writeLoc js next w dst (aluRes op X Y c).1 with
              | .ok s' => .ok ((s'.setFlags (aluRes op X Y c).2).setRip next)
              | .error e => .error e := by
  unfold execAlu
  rcases readSrc js next w src with e | Y
  · rfl
  cases op <;> simp only [reduceCtorEq, ↓reduceIte, aluRes, or_self, or_false, false_or] <;>
    rcases (readLocRW js next w dst) with e | X <;> (try rcases (readLoc js next w dst) with e | X) <;> (try rfl) <;>
    rcases js.flags.cf with _ | c <;> rfl

open Janus.Amd64 in
/-- Janus' `execAlu`, any destination and source: what it read, wrote and computed. -/
theorem execAlu_any {js js' : State} {next : BitVec 64} {op : AluOp} {w : Nat} {dst : Loc} {src : Src}
    {Y : BitVec w} (hs : readSrc js next w src = .ok Y)
    (hJ : execAlu js next op w dst src = .ok js') :
    ∃ X c, (op = .cmp → readLoc js next w dst = .ok X) ∧ (op ≠ .cmp → readLocRW js next w dst = .ok X) ∧
      ((op = .adc ∨ op = .sbb) → js.flags.cf = some c) ∧
      (op = .cmp → js' = (js.setFlags (aluRes op X Y c).2).setRip next) ∧
      (op ≠ .cmp → ∃ j2, writeLoc js next w dst (aluRes op X Y c).1 = .ok j2 ∧
        js' = (j2.setFlags (aluRes op X Y c).2).setRip next) := by
  rw [execAlu_eq, hs] at hJ
  simp only at hJ
  split at hJ
  · simp at hJ
  rename_i X hX
  split at hJ
  · simp at hJ
  rename_i c hc
  refine ⟨X, c, fun h => by simpa [h] using hX, fun h => by simpa [h] using hX,
    fun h => by simpa [h] using hc, fun h => ?_, fun h => ?_⟩
  · subst h; simp only [↓reduceIte, Except.ok.injEq] at hJ; exact hJ.symm
  · simp only [h, ↓reduceIte] at hJ
    split at hJ
    · rename_i j2 hj2; exact ⟨j2, hj2, by simp at hJ; exact hJ.symm⟩
    · simp at hJ

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_e_i (opc : Nat) (hopc : opc = 0x80 ∨ opc = 0x81 ∨ opc = 0x83) (e : Nat) (he : e < 8)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hm : _get_modr_m_reg m = BitVec.ofNat 3 e) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i (sailOp (Janus.Amd64.Decode.aluOp e)) .Mode_64bit sr tr x rex
        (BitVec.ofNat 8 opc) m sib).run s := by
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    rcases hopc with rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
      ↓reduceIte, Bool.false_eq_true, Janus.Amd64.Decode.aluOp, sailOp, hl, hm, Bool.and_false, run_bind, run_pure,
      show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxRecDepth 100000 in
theorem run_one_byte_test_e_i (opc : Nat) (hopc : opc = 0xF6 ∨ opc = 0xF7)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hm : _get_modr_m_reg m = 0#3) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 7 .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases hopc with rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, hm, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem regWrite_df (js : Janus.Amd64.State) (w : Nat) (l : Janus.Amd64.Loc) (v : BitVec w) :
    (regWrite js w l v).df = js.df := by
  unfold regWrite; split <;> simp [Janus.Amd64.State.putReg, Janus.Amd64.State.putHigh, Janus.Amd64.State.setReg] <;>
    (try split) <;> rfl

/-- The model's write of a register `r/m` destination is Janus' `regWrite`. -/
theorem dstW_reg {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (rexP : Bool) (rex : BitVec 8) (hrex : (rex == 0#8) = !rexP)
    {n : Nat} (hn : n < 16) (hn8 : n < 8 ∨ rexP = true) (a : BitVec 3) (hidx : reg_index a rex 0#2 = BitVec.ofNat 4 n)
    (sg : Nat) (ad : BitVec 64) (x : BitVec 52) (sib : BitVec 8) (y : BitVec w) :
    ∃ s1, (x86_operand_to_reg_mem .Mode_64bit (w / 8) true false ((y.setWidth 64).setWidth 128) sg ad x rex a 3#2 sib).run s =
      .ok () s1 ∧ Rel (regWrite js w (regLocOf rexP w n) y) s1 ∧ X86Config s1 ∧
      (regWrite js w (regLocOf rexP w n) y).df = js.df ∧ s1.regs.get? .rflags = s.regs.get? .rflags ∧
      s1.regs.get? .janus_undef = s.regs.get? .janus_undef := by
  have hn' := locReg_lt rexP w n hn
  refine ⟨_, run_operand_to_reg h hc.log hw rexP rex hrex hn hn8 a hidx true false sg ad x sib y,
    h.writeReg rexP hn y, hc.setGpr hn' _, regWrite_df _ _ _ _, get?_setGpr_of_not s _ hn' rfl,
    get?_setGpr_of_not s _ hn' rfl⟩

open Janus.Amd64 Janus.Amd64.Decode in
/-- The model's write of a memory `r/m` destination is Janus' store. -/
theorem dstW_mem {js : State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {sg : Nat} (hsg : sg = 4 ↔ p.fs = true) (hsg5 : sg ≠ 5)
    (a : Addr) (hafs : a.fs = false) (next : BitVec 64) (rm : BitVec 3) {md : BitVec 2}
    (hmd : (md == 3#2) = false) (sib : BitVec 8)
    (hacc : js.mem.accessible (ea js next (if p.fs then { a with fs := true } else a)).toNat (w / 8) true = true)
    (y : BitVec w) :
    ∃ s1, (x86_operand_to_reg_mem .Mode_64bit (w / 8) true false ((y.setWidth 64).setWidth 128) sg (eaOff js next a)
      x rex rm md sib).run s = .ok () s1 ∧
      Rel (memWrite js (ea js next (if p.fs then { a with fs := true } else a)).toNat (w / 8) y.toNat) s1 ∧ X86Config s1 ∧
      (memWrite js (ea js next (if p.fs then { a with fs := true } else a)).toNat (w / 8) y.toNat).df = js.df ∧
      s1.regs.get? .rflags = s.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s.regs.get? .janus_undef := by
  obtain ⟨s1, h1, h2, h3, h4⟩ := run_operand_to_mem h hc hp hw hsg hsg5 true false a hafs next rm hmd sib y hacc
  exact ⟨s1, h1, h2, h3, rfl, by rw [h4], by rw [h4]⟩

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem modrm_ext {rx m : Nat} {rest : List Nat} {mm : ModRM} {r3 : List Nat} {c : Nat}
    (h : modrm rx (m :: rest) = some (mm, r3, c)) : mm.ext = m / 8 % 8 := by
  revert h
  unfold modrm
  simp only
  repeat' split
  all_goals intro h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, -⟩ := h; rfl)

/-- The `r/m` operand of a decoded ModRM as Janus' location (with `FS` relocation). -/
def rmDst (p : Janus.Amd64.Decode.Prefixes) (w : Nat) : Janus.Amd64.Decode.RM → Janus.Amd64.Loc
  | .r k => regLocOf p.rex.isSome w k
  | .m a => .mem (if p.fs then { a with fs := true } else a)

/-- Janus' immediate of the (E, I) forms, before truncation to the operand size. -/
def immEI (o w v : Nat) : Nat :=
  if o = 0x83 then Janus.Amd64.Decode.sext 8 w v else if w = 64 then Janus.Amd64.Decode.sext 32 64 v else v

open Janus.Amd64 Janus.Amd64.Decode in
theorem withFS_reg8 (op : AluOp) (w : Nat) (b : Bool) (n : Nat) (v : Nat) :
    withFS (.alu op w (reg8 b n) (.imm v)) = none := by
  unfold reg8; split <;> rfl

open Janus.Amd64 Janus.Amd64.Decode in
theorem withFS_reg8t (w : Nat) (b : Bool) (n : Nat) (v : Nat) :
    withFS (.test w (reg8 b n) (.imm v)) = none := by
  unfold reg8; split <;> rfl

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_ei {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (ho : o = 0x80 ∨ o = 0x81 ∨ o = 0x83 ∨ o = 0xF6 ∨ o = 0xF7)
    (hext : (o = 0xF6 ∨ o = 0xF7) → m / 8 % 8 = 0)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c)) (hlk : p.lock = false)
    {w : Nat} (hw : w = if o = 0x80 ∨ o = 0xF6 then 8 else osz p)
    {k : Nat} (hk : k = if o = 0x81 ∨ o = 0xF7 then immBytes w else 1)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.rep = 0 ∧ ∃ v r4, readLE k r3 = some (v, r4) ∧ len = n + 1 + c + k ∧ len ≤ 15 ∧
      i = (if o = 0xF6 ∨ o = 0xF7 then .test w (rmDst p w mm.rm) (.imm (immEI o w v))
        else .alu (aluOp (m / 8 % 8)) w (rmDst p w mm.rm) (.imm (immEI o w v))) ∧
      (∀ k', mm.rm = .r k' → p.fs = false) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp, hlk, Bool.false_eq_true] at hd
  have hex := modrm_ext hmd
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hex; subst hex
  have hib : ∀ q, (if q = 8 then 1 else if q = 16 then 2 else 4) = immBytes q := fun _ => rfl
  have ho8 : (osz p = 8) = False := by rcases osz_cases p with e | e | e <;> simp [e]
  have hib2 : (if osz p = 16 then 2 else 4) = immBytes (osz p) := by simp [immBytes, ho8]
  cases hr : readLE k r3 with
  | none =>
    exfalso
    rcases ho with rfl | rfl | rfl | rfl | rfl
    all_goals
      (try simp (config := {decide := true}) only [true_or, or_true, true_implies, forall_const] at hext)
      simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, immZ, immU8, immB, true_and, and_true,
        false_and, and_false, or_false, false_or, hib, hext, ho8, hib2] at hd hw hk
      subst hw hk
      simp [hr, hib] at hd
  | some vr =>
  obtain ⟨v, r4⟩ := vr
  rcases ho with rfl | rfl | rfl | rfl | rfl
  all_goals
    (try simp (config := {decide := true}) only [true_or, or_true, true_implies, forall_const] at hext)
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, immZ, immU8, immB, true_and, and_true,
      false_and, and_false, or_false, false_or, hib, hext, ho8, hib2] at hd hw hk ⊢
    subst hw hk
    simp only [hr, finish] at hd
    refine ⟨?_, v, r4, rfl, ?_⟩
    all_goals
      by_cases hl : 15 < n + 1 + c + 1 <;> by_cases hl2 : 15 < n + 1 + c + immBytes (osz p) <;>
      by_cases hrp : p.rep = 0 <;>
      cases hf : p.fs <;> cases rm <;> simp (config := {decide := true}) [hf, hl, hl2, hrp, ho8, rmDst, rmLoc, regLocOf,
        immEI, withFS_reg8, withFS_reg8t] at hd ⊢ <;> (try simp [withFS] at hd ⊢)
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl, fun _ h => by cases h⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl, fun _ _ => rfl⟩)
      | omega

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem immEI_eq {o w v : Nat} (ho : o = 0x80 ∨ o = 0x81 ∨ o = 0x83 ∨ o = 0xF6 ∨ o = 0xF7)
    {p : Janus.Amd64.Decode.Prefixes} (hw : w = if o = 0x80 ∨ o = 0xF6 then 8 else osz p)
    {k : Nat} (hk : k = if o = 0x81 ∨ o = 0xF7 then immBytes w else 1) (hv : v < 2 ^ (8 * k)) :
    BitVec.ofNat w (immEI o w v) = BitVec.ofNat w (Janus.Amd64.Decode.sext (8 * k) w v) := by
  subst hk hw
  rcases osz_cases p with e | e | e <;>
  rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [e, immEI, immBytes] at hv ⊢ <;>
  simp [Janus.Amd64.Decode.sext] <;> split <;> simp <;> omega

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem disp_drop {md : Nat} {bs : List Nat} {d : Nat} {r : List Nat} {k : Nat} (h : disp md bs = some (d, r, k)) :
    r = bs.drop k := by
  unfold disp at h
  split at h
  · split at h
    · rename_i _ _ e; simp at h; obtain ⟨-, rfl, rfl⟩ := h; exact (readLE_sumLE _ _ e).2.2
    · simp at h
  · split at h
    · split at h
      · rename_i _ _ e; simp at h; obtain ⟨-, rfl, rfl⟩ := h; exact (readLE_sumLE _ _ e).2.2
      · simp at h
    · simp at h; obtain ⟨-, rfl, rfl⟩ := h; simp

open Janus.Amd64 Janus.Amd64.Decode in
theorem modrm_drop {rx m : Nat} {rest : List Nat} {mm : ModRM} {r3 : List Nat} {c : Nat}
    (h : modrm rx (m :: rest) = some (mm, r3, c)) : r3 = rest.drop (c - 1) := by
  revert h
  unfold modrm
  simp only
  repeat' split
  all_goals intro h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, rfl⟩ := h; simp; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, rfl⟩ := h
       first
         | (obtain ⟨-, -, e⟩ := readLE_sumLE 4 _ ‹readLE 4 _ = some (_, _)›; simp only [e]; simp [List.drop_drop]; done)
         | (have e := disp_drop ‹disp _ _ = some (_, _, _)›; rw [e]
            simp only [show ∀ k, 2 + k - 1 = k + 1 from fun k => by omega,
              show ∀ k, 1 + k - 1 = k from fun k => by omega, List.drop_succ_cons])
         | exact (readLE_sumLE 4 _ ‹_›).2.2)

open Janus.Amd64 in
theorem exec_ei {js js' : State} {len o w : Nat} {D : Loc} {I : Nat} {Y : BitVec w} (hY : BitVec.ofNat w I = Y)
    (op : AluOp) (hop : (o = 0xF6 ∨ o = 0xF7) → op = .and)
    (hstep : exec (if o = 0xF6 ∨ o = 0xF7 then .test w D (.imm I) else .alu op w D (.imm I)) len js = .ok js') :
    ∃ X c, (((o = 0xF6 ∨ o = 0xF7) ∨ op = .cmp) →
        readLoc js (BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64)) w D = .ok X) ∧
      (¬ ((o = 0xF6 ∨ o = 0xF7) ∨ op = .cmp) →
        readLocRW js (BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64)) w D = .ok X) ∧
      ((op = .adc ∨ op = .sbb) → js.flags.cf = some c) ∧
      (((o = 0xF6 ∨ o = 0xF7) ∨ op = .cmp) →
        js' = (js.setFlags (aluRes op X Y c).2).setRip (BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64))) ∧
      (¬ ((o = 0xF6 ∨ o = 0xF7) ∨ op = .cmp) → ∃ j2,
        writeLoc js (BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64)) w D (aluRes op X Y c).1 = .ok j2 ∧
        js' = (j2.setFlags (aluRes op X Y c).2).setRip (BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64))) := by
  generalize hNX : BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64) = NX
  by_cases ht : o = 0xF6 ∨ o = 0xF7
  · have hop' := hop ht; subst hop'
    simp only [ht, ↓reduceIte, exec] at hstep
    rw [hNX] at hstep
    cases hr : readLoc js NX w D with
    | error e => simp [hr] at hstep
    | ok X =>
      simp only [hr, readSrc, hY, Except.ok.injEq] at hstep
      exact ⟨X, false, fun _ => rfl, fun h => absurd (Or.inl ht) h, by simp, fun _ => by simp [← hstep, aluRes],
        fun h => absurd (Or.inl ht) h⟩
  · simp only [ht, ↓reduceIte, exec] at hstep
    rw [hNX] at hstep
    obtain ⟨X, c, h1, h2, h3, h4, h5⟩ := execAlu_any (Y := Y) (by simp [readSrc, hY]) hstep
    refine ⟨X, c, fun h => h1 (by simpa [ht] using h), fun h => h2 (by simpa [ht] using h), h3,
      fun h => h4 (by simpa [ht] using h), fun h => h5 (by simpa [ht] using h)⟩

theorem modrmP1_ei : ∀ o, (o = 0x80 ∨ o = 0x81 ∨ o = 0x83 ∨ o = 0xF6 ∨ o = 0xF7) → modrmP1 o = true := by
  intro o h; rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 2000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **ADD/OR/ADC/SBB/AND/SUB/XOR/CMP r/m, imm** (`80/81/83 /0..7`) and **TEST r/m, imm**
(`F6/F7 /0`): every ModRM form (register, or memory with every addressing form incl. SIB,
RIP- and FS-relative), every width and prefix sequence Janus accepts without `LOCK`. -/
theorem alu_ei_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (ho : o = 0x80 ∨ o = 0x81 ∨ o = 0x83 ∨ o = 0xF6 ∨ o = 0xF7)
    (hext : (o = 0xF6 ∨ o = 0xF7) → m / 8 % 8 = 0) (hlk : p.lock = false)
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
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  generalize hw : (if o = 0x80 ∨ o = 0xF6 then 8 else osz p) = w
  generalize hk : (if o = 0x81 ∨ o = 0xF7 then immBytes w else 1) = k
  obtain ⟨hrep, v, r4, hr, rfl, hlen, rfl, hfs⟩ := decode_ei hpp ho hext hmd hlk hw.symm hk.symm hd
  rw [step_of_decode hd] at hstep
  have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hm256 : m < 256 := hcode.1 m (by
    have : m ∈ bytes.drop n := by rw [hdrop]; simp
    exact List.mem_of_mem_drop this)
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have ho256 : o < 256 := by omega
  have hpg : prefixGroup o = 0 := by
    unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hmp : modrmP1 o = true := modrmP1_ei o ho
  have hcs : CodeAt s (js.rip.toNat + n + 1 + 1) rest := by
    have h2 : (bytes.drop n).drop 2 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 2); rw [show bytes.drop (n + 2) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 2) = js.rip.toNat + n + 1 + 1 by omega] at this
  have hk4 : k = 1 ∨ k = 2 ∨ k = 4 := by
    rw [← hk]; unfold immBytes; split <;> (try split) <;> (try split) <;> simp
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [← hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c + k)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + k) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  have hrexP := rex_hrex hrv
  -- the immediate bytes
  have hmdc := modrm_drop hmd
  have hvl : v < 2 ^ (8 * k) := by
    obtain ⟨-, hvv, -⟩ := readLE_sumLE _ _ hr
    have hc3 : CodeAt s (js.rip.toNat + n + 1 + 1 + (c - 1)) r3 := by rw [hmdc]; exact hcs.drop (c - 1)
    rw [hvv, Nat.pow_mul]
    exact sumLE_lt _ (fun j => by
      by_cases hj : j < r3.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hc3.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
  have hY := immEI_eq ho hw.symm hk.symm hvl
  generalize hYd : BitVec.ofNat w (Janus.Amd64.Decode.sext (8 * k) w v) = Y at hY
  -- the operation
  generalize hop : (if o = 0xF6 ∨ o = 0xF7 then AluOp.and else aluOp (m / 8 % 8)) = op
  have hstep' : exec (if o = 0xF6 ∨ o = 0xF7 then .test w (rmDst p w mm.rm) (.imm (immEI o w v))
      else .alu op w (rmDst p w mm.rm) (.imm (immEI o w v))) (n + 1 + c + k) js = .ok js' := by
    rw [← hop]; split <;> simpa [*] using hstep
  obtain ⟨X, c0, hX1, hX2, hcf, hJ1, hJ2⟩ := exec_ei hY op (fun h => by rw [← hop]; simp [h]) hstep'
  rw [hnext] at hX1 hX2 hJ1 hJ2
  generalize hoper : (if o = 0xF6 ∨ o = 0xF7 then 7 else sailOp op) = operation
  have hope : operation = sailOp op ∨ (operation = 7 ∧ op = .and) := by
    rw [← hoper, ← hop]; split
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl rfl
  have hnw : (operation = 8 ∨ operation = 7) ↔ ((o = 0xF6 ∨ o = 0xF7) ∨ op = .cmp) := by
    rw [← hoper]; split
    · simp_all
    · rename_i h; simp only [h, false_or]
      rw [show (sailOp op = 8 ∨ sailOp op = 7) = (sailOp op = 8 ∨ sailOp op = 7) from rfl, sailOp_cmp]
  -- the model up to the (E, I) arm
  obtain ⟨md, rg, ext, rm⟩ := mm
  have hm4 : modrmSib (modrmP1 o) (m :: rest) = (BitVec.ofNat 8 m, (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8),
      1 + (if sibP m then 1 else 0)) := by rw [hmp, modrmSib_eq]
  have hsl : (1 + (if sibP m then 1 else 0)) ≤ (m :: rest).length := by
    cases rest with
    | cons _ _ => simp; split <;> omega
    | nil =>
      cases hs : sibP m
      · simp
      · exfalso
        unfold sibP at hs; simp at hs
        unfold modrm at hmd; simp [hs.1, hs.2] at hmd
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [hm4]; simp at hsl ⊢; omega)
  rw [hm4] at hf
  simp only at hf
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hpr.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  obtain ⟨hf1, hf2, hf3⟩ := modrm_fields m hm256
  have hdisp : (one_byte_opcode_execute .Mode_64bit (BitVec.ofNat 48 js.rip.toNat)
      (BitVec.ofNat 48 (js.rip.toNat + n + 1 + (1 + (if sibP m then 1 else 0)))) x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m)
      (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8)).run s =
      (x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i operation .Mode_64bit (BitVec.ofNat 48 js.rip.toNat)
      (BitVec.ofNat 48 (js.rip.toNat + n + 1 + 1 + (if sibP m then 1 else 0))) x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m)
      (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8)).run s := by
    rw [show js.rip.toNat + n + 1 + (1 + (if sibP m then 1 else 0)) = js.rip.toNat + n + 1 + 1 + (if sibP m then 1 else 0)
      by omega]
    rw [← hoper, ← hop]
    by_cases ht : o = 0xF6 ∨ o = 0xF7
    · simp only [ht, ↓reduceIte]
      rw [run_one_byte_test_e_i o ht _ _ x hl0 _ _ _ (by rw [hf2, hext ht]) s]
    · simp only [ht, ↓reduceIte]
      have h80 : o = 0x80 ∨ o = 0x81 ∨ o = 0x83 := by
        rcases ho with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact absurd (Or.inl h) ht
        · exact absurd (Or.inr h) ht
      have hh := run_one_byte_e_i o h80 (m / 8 % 8) (Nat.mod_lt _ (by decide)) (BitVec.ofNat 48 js.rip.toNat)
        (BitVec.ofNat 48 (js.rip.toNat + n + 1 + 1 + (if sibP m then 1 else 0))) x hl0 rex (BitVec.ofNat 8 m)
        (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8) hf2 s
      exact hh
  rw [hdisp] at hf
  have hk3 : k < 8 := by omega
  cases rm with
  | r k' =>
    obtain ⟨h3, rfl, rfl, -⟩ := modrm_r hmd
    have hfs' := hfs _ rfl
    have hsib : sibP m = false := sibP_reg m h3
    simp only [hsib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
    have hD : rmDst p w (.r (m % 8 + 8 * (p.rex.getD 0 % 2))) = regLocOf p.rex.isSome w (rmNum p m) := rfl
    rw [hD] at hX1 hX2 hJ2
    have hXv : X = regVal js w (regLocOf p.rex.isSome w (rmNum p m)) := by
      by_cases hh : (o = 0xF6 ∨ o = 0xF7) ∨ op = .cmp
      · have := hX1 hh; rw [readLoc_regLocOf] at this; simp at this; exact this.symm
      · have := hX2 hh; rw [readLocRW_regLocOf] at this; simp at this; exact this.symm
    subst hXv
    have hcs3 : CodeAt s (js.rip.toNat + n + 1 + 1) r3 := by rw [hmdc]; simpa using hcs
    obtain ⟨s', hs', hrel', hcfg'⟩ := run_alu_e_i hrel hcfg hpr hrv operation op hope o ho hw.symm hk.symm m hm256 0#8
      (js.rip.toNat + n + 1 + 1) (js.rip.toNat + n + 1 + 1) (regVal js w (regLocOf p.rex.isSome w (rmNum p m))) 0 0#64
      (fun sg _ _ => by
        rw [h3]
        exact run_operand_from_reg hrel hW _ rex hrex (rmNum_lt p m) (rmNum_8 p m) _
          (by rw [hrexb]; exact hidx_rm hrv m) true false sg x _ 0#8 _)
      (regWrite js w (regLocOf p.rex.isSome w (rmNum p m)))
      (fun _ sg _ _ y => by
        rw [h3]
        exact dstW_reg hrel hcfg hW _ rex hrex (rmNum_lt p m) (rmNum_8 p m) _ (by rw [hrexb]; exact hidx_rm hrv m)
          sg 0#64 x 0#8 y)
      rfl hcs3 hr js.rip.toNat (by omega) (by omega) (by omega) c0 hcf
    refine ⟨s', run_janus_x86_step (by rw [hf, hs']), ?_, hcfg'⟩
    rw [hYd] at hrel'
    by_cases hh : (o = 0xF6 ∨ o = 0xF7) ∨ op = .cmp
    · rw [hJ1 hh]; simp only [hnw.2 hh, ↓reduceIte] at hrel'
      exact hrel'
    · obtain ⟨j2, hj2, rfl⟩ := hJ2 hh
      rw [writeLoc_regLocOf] at hj2; simp only [Except.ok.injEq] at hj2; subst hj2
      have : ¬ (operation = 8 ∨ operation = 7) := fun e => hh (hnw.1 e)
      simp only [this, ↓reduceIte] at hrel'
      exact hrel'
  | m a =>
    obtain ⟨hc1, hc6, hmd3⟩ := modrm_c_ge hmd
    have hD : rmDst p w (.m a) = .mem (if p.fs then { a with fs := true } else a) := rfl
    rw [hD] at hX1 hX2 hJ2
    generalize hNX : BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + k) = NX at hX1 hX2 hJ1 hJ2
    have hXv : ∃ wr, js.mem.accessible (ea js NX (if p.fs then { a with fs := true } else a)).toNat (w / 8) wr = true ∧
        (¬ ((o = 0xF6 ∨ o = 0xF7) ∨ op = .cmp) → wr = true) ∧
        X = BitVec.ofNat w (js.mem.readLE (ea js NX (if p.fs then { a with fs := true } else a)).toNat (w / 8)) := by
      by_cases hh : (o = 0xF6 ∨ o = 0xF7) ∨ op = .cmp
      · obtain ⟨h1, h2⟩ := readLoc_mem (hX1 hh); exact ⟨false, h1, fun h => absurd hh h, h2⟩
      · obtain ⟨h1, h2⟩ := readLocRW_mem (hX2 hh); exact ⟨true, h1, fun _ => rfl, h2⟩
    obtain ⟨wr, hacc, hwr, rfl⟩ := hXv
    have hcs3 : CodeAt s (js.rip.toNat + n + 1 + c) r3 := by
      rw [hmdc]; have := hcs.drop (c - 1)
      rwa [show js.rip.toNat + n + 1 + 1 + (c - 1) = js.rip.toNat + n + 1 + c by omega] at this
    have hafs := (run_x86_effective_addr hrel hcfg hrel.rip hpr hrv hcs hm256 hmd (nimm := k) hk3 (by omega)).2.1
    obtain ⟨s', hs', hrel', hcfg'⟩ := run_alu_e_i hrel hcfg hpr hrv operation op hope o ho hw.symm hk.symm m hm256
      (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8)
      (js.rip.toNat + n + 1 + 1 + (if sibP m then 1 else 0)) (js.rip.toNat + n + 1 + c)
      (BitVec.ofNat w (js.mem.readLE (ea js NX (if p.fs then { a with fs := true } else a)).toNat (w / 8)))
      (c - 1 - (if sibP m then 1 else 0)) (eaOff js NX a)
      (fun sg hsg4 hsg5 => by
        have := run_operand_from_mem hrel hcfg hpr hrv hcs hm256 hmd (nimm := k) hk3 (by omega) hW hsg4 hsg5
          true false (wr := wr) (by rw [show js.rip.toNat + n + 1 + c + k = js.rip.toNat + n + 1 + c + k from rfl, hNX]; exact hacc)
        rw [hNX] at this
        simpa using this)
      (memWrite js (ea js NX (if p.fs then { a with fs := true } else a)).toNat (w / 8) ∘ BitVec.toNat)
      (fun hnw' sg hsg4 hsg5 y => by
        have hw' := hwr (fun e => hnw' (hnw.2 e)); subst hw'
        exact dstW_mem hrel hcfg hpr hW hsg4 hsg5 a hafs NX _ (by rw [beq2_3 _ (by omega)]; simpa using hmd3) _ hacc y)
      (by omega) hcs3 hr js.rip.toNat (by omega) (by omega) (by omega) c0 hcf
    refine ⟨s', run_janus_x86_step (by rw [hf, hs']), ?_, hcfg'⟩
    rw [hYd, show js.rip.toNat + n + 1 + c + k = js.rip.toNat + n + 1 + c + k from rfl, hNX] at hrel'
    by_cases hh : (o = 0xF6 ∨ o = 0xF7) ∨ op = .cmp
    · rw [hJ1 hh]; simp only [hnw.2 hh, ↓reduceIte] at hrel'; exact hrel'
    · obtain ⟨j2, hj2, rfl⟩ := hJ2 hh
      have hw' := hwr hh; subst hw'
      rw [writeLoc_mem _ hacc] at hj2; simp only [Except.ok.injEq] at hj2; subst hj2
      have : ¬ (operation = 8 ∨ operation = 7) := fun e => hh (hnw.1 e)
      simp only [this, ↓reduceIte, Function.comp] at hrel'
      exact hrel'

end JanusX86.Proofs
