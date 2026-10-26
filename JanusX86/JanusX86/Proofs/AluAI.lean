import JanusX86.Proofs.AluGE

/-! # ALU (A, I) forms: `AL/AX/EAX/RAX, imm` (`04/05 … 3C/3D`) and `TEST` (`A8/A9`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem byteop8_all : ∀ opc < 256, (0x00#8 == (0x01#8 &&& BitVec.ofNat 8 opc)) = decide (opc % 2 = 0) := by
  decide +kernel

theorem regLocOf_zero (b : Bool) (w : Nat) : regLocOf b w 0 = .reg 0 := by
  unfold regLocOf Janus.Amd64.Decode.reg8; split <;> simp

/-- Janus' immediate of width `w` from the raw little-endian value `v` (`immZ`/`immU8`). -/
def immVal (w v : Nat) : BitVec w := BitVec.ofNat w (if w = 64 then Janus.Amd64.Decode.sext 32 64 v else v)

/-- The number of immediate bytes of an `Iz` operand (`immZ`). -/
def immBytes (w : Nat) : Nat := if w = 8 then 1 else if w = 16 then 2 else 4

theorem tsx48 (a : Nat) : Sail.BitVec.truncate (Sail.BitVec.signExtend (BitVec.ofNat 48 a) 49) 48 = BitVec.ofNat 48 a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Sail.BitVec.truncate, Sail.BitVec.signExtend, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi]
  omega

theorem spec7 (k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8) (a b : BitVec 64) (r : BitVec 32) :
    gpr_arith_logic_spec k 7 a b r = gpr_arith_logic_spec k 3 a b r := by
  rcases hk with rfl | rfl | rfl | rfl <;> rfl

theorem rax_pair {w opc : Nat} {p : Janus.Amd64.Decode.Prefixes} (hw : w = if opc % 2 = 0 then 8 else osz p)
    (hD2 : ¬ (opc % 2 = 0 ∧ rexW p = true)) (v : Nat) (hv : v < 2 ^ (8 * immBytes w)) :
    (if (!decide (opc % 2 = 0) && ((w / 8 : Nat) : Int) == 8) = true then
        ((8 : Int), Sail.BitVec.signExtend (Sail.BitVec.truncate (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * immBytes w) v) 128) 32) 64)
      else (((immBytes w : Nat) : Int), Sail.BitVec.zeroExtend (Sail.BitVec.truncate (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * immBytes w) v) 128) 32) 64)) =
      (((w / 8 : Nat) : Int), (immVal w v).setWidth 64) := by
  have hcase : (w = 8 ∧ opc % 2 = 0) ∨ (w = 16 ∧ opc % 2 = 1) ∨ (w = 32 ∧ opc % 2 = 1) ∨ (w = 64 ∧ opc % 2 = 1) := by
    unfold osz at hw
    rcases Nat.mod_two_eq_zero_or_one opc with hb | hb <;> cases hx : rexW p <;> cases hy : p.opsize <;>
      simp_all
  rcases hcase with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ <;>
    simp (config := {decide := true}) only [immBytes, immVal, hb, ↓reduceIte, Nat.reduceMul, Nat.reduceDiv,
      decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and, Bool.false_eq_true,
      Prod.mk.injEq, true_and] at hv ⊢
  all_goals first
    | (show Sail.BitVec.signExtend (Sail.BitVec.truncate (Sail.BitVec.zeroExtend (BitVec.ofNat 32 v) 128) 32) 64 = _
       have e : Sail.BitVec.truncate (Sail.BitVec.zeroExtend (BitVec.ofNat 32 v) 128) 32 = BitVec.ofNat 32 v := by
         apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.zeroExtend, Sail.BitVec.truncate]
       rw [e]; exact sext_eq_32 v hv)
    | (apply BitVec.eq_of_toNat_eq
       simp [Sail.BitVec.zeroExtend, Sail.BitVec.truncate] <;> omega)

set_option maxHeartbeats 1000000 in
theorem run_alu_rax_i {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (operation : Nat) (op : Janus.Amd64.AluOp)
    (hop : operation = sailOp op ∨ (operation = 7 ∧ op = .and))
    (opc : Nat) (hopc : opc < 256) {w : Nat} (hw : w = if opc % 2 = 0 then 8 else osz p)
    (hD2 : ¬ (opc % 2 = 0 ∧ rexW p = true))
    (m sib : BitVec 8) (tr : Nat) {ds : List Nat} (hds : CodeAt s tr ds) {v : Nat} {r : List Nat}
    (hle : Janus.Amd64.Decode.readLE (immBytes w) ds = some (v, r))
    (sr : Nat) (hl1 : sr ≤ tr + immBytes w) (hl2 : tr + immBytes w ≤ sr + 15) (htr : tr + immBytes w < 2 ^ 47)
    (cc : Bool) (hcf : (op = .adc ∨ op = .sbb) → js.flags.cf = some cc) :
    ∃ s', (x86_add_adc_sub_sbb_or_and_xor_cmp_test_rax_i operation .Mode_64bit (BitVec.ofNat 48 sr)
      (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc) m sib).run s = .ok () s' ∧
      Rel (((if operation = 8 ∨ operation = 7 then js
          else regWrite js w (.reg 0) (aluRes op (js.getReg w 0) (immVal w v) cc).1).setFlags
          (aluRes op (js.getReg w 0) (immVal w v) cc).2).setRip (BitVec.ofNat 64 (tr + immBytes w))) s' ∧
      X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hlb : logbitp_bits 3 rex = rexW p := by rw [hrexb]; exact logbitp3_rexByte hrv
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hos : (if decide (opc % 2 = 0) = true then (1 : Int) else if rexW p = true then (if True then 4 else 8)
      else if p.opsize = true then 2 else 4) = ((immBytes w : Nat) : Int) := by
    subst hw; unfold osz immBytes
    rcases Nat.mod_two_eq_zero_or_one opc with hb | hb <;> cases hx : rexW p <;> cases hy : p.opsize <;>
      simp_all
  have hrs : (if rexW p = true then (8 : Int) else ((immBytes w : Nat) : Int)) = ((w / 8 : Nat) : Int) := by
    subst hw; unfold osz immBytes
    rcases Nat.mod_two_eq_zero_or_one opc with hb | hb <;> cases hx : rexW p <;> cases hy : p.opsize <;>
      simp_all
  have hrip := h.rip
  have hrme : (rme_size .Mode_64bit 8 (immBytes w) (Sail.BitVec.signExtend (BitVec.ofNat 48 tr) 64) none 1 ":X"
      false false).run s = .ok (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * immBytes w) v) 128) s := by
    simp only [rme_size, run_bind, run_load_code hc hrip 8 hds (by unfold immBytes; split <;> (try split) <;> omega)
      hle (by omega), run_pure]
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  simp only [x86_add_adc_sub_sbb_or_and_xor_cmp_test_rax_i, run_bind, run_select_operand_size hp hrv,
    byteop8_all opc hopc, hlb, hos, hrs, nbytes_eq w hW, hsel, Int.toNat_natCast, hrme]
  obtain ⟨-, hvv, -⟩ := readLE_sumLE _ ds hle
  have hvl : v < 2 ^ (8 * immBytes w) := by
    rw [hvv, Nat.pow_mul]
    exact sumLE_lt _ (fun j => by
      by_cases hj : j < ds.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hds.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
  have hadd : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (bits_of_int ((immBytes w : Nat) : Int) 48)).run s =
      .ok (BitVec.ofNat 48 (tr + immBytes w)) s := by
    have ez : (bits_of_int ((immBytes w : Nat) : Int) 48).toNat = immBytes w := by
      rw [bits_of_int_natCast_toNat]; unfold immBytes; split <;> (try split) <;> simp
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hlen := check_len_ok sr (tr + immBytes w) hl1 hl2 htr
  rw [show (Janus.Amd64.Loc.reg 0) = regLocOf p.rex.isSome w 0 from (regLocOf_zero _ _).symm,
    show js.getReg w 0 = regVal js w (regLocOf p.rex.isSome w 0) by rw [regLocOf_zero]; rfl]
  let c' := (_get_rflagsbits_cf rf == 1#1)
  have hc' : _get_rflagsbits_cf rf = BitVec.ofBool c' := bv1_ofBool _
  have hcc : aluRes op (regVal js w (regLocOf p.rex.isSome w 0)) (immVal w v) c' =
      aluRes op (regVal js w (regLocOf p.rex.isSome w 0)) (immVal w v) cc := by
    apply aluRes_c; intro hop
    have := hfr.cf cc (hcf hop)
    show (_get_rflagsbits_cf rf == 1#1) = cc
    rw [this]; cases cc <;> rfl
  have hspec : (gpr_arith_logic_spec (w / 8) operation ((regVal js w (regLocOf p.rex.isSome w 0)).setWidth 64)
      ((immVal w v).setWidth 64) rf).run s =
      .ok ((aluRes op (regVal js w (regLocOf p.rex.isSome w 0)) (immVal w v) cc).1.setWidth 64,
        (aluOut op rf (aluRes op (regVal js w (regLocOf p.rex.isSome w 0)) (immVal w v) cc).2).1,
        (aluOut op rf (aluRes op (regVal js w (regLocOf p.rex.isSome w 0)) (immVal w v) cc).2).2) s := by
    rw [← hcc]
    rcases hop with rfl | ⟨rfl, rfl⟩
    · exact run_gpr_arith_logic_spec op hW _ _ rf c' hc' s
    · rw [spec7 _ (by rcases hW with e | e | e | e <;> subst e <;> simp)]
      exact run_gpr_arith_logic_spec .and hW _ _ rf c' hc' s
  simp only [run_rgfi_size h hW _ rex hrex (n := 0) (by decide) (Or.inl (by decide)), hsel, Int.toNat_natCast, show (8 : Int).toNat = 8 from rfl, hrme,
    hadd, run_pure, tsx48, hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_readReg hr, rax_pair hw hD2 v hvl,
    hspec, nbytes_eq w hW]
  generalize hR : aluRes op (regVal js w (regLocOf p.rex.isSome w 0)) (immVal w v) cc = R
  have hfR : FlagsRel R.2 js.df (wurf rf (aluOut op rf R.2).1 (aluOut op rf R.2).2 u) := by
    rw [← hR]; exact flagsRel_aluOut hfr op _ _ cc u
  have htr' : tr + immBytes w < 2 ^ 47 := htr
  by_cases hnw : operation = 8 ∨ operation = 7
  · have hb : (operation == 8 || operation == 7) = true := by rcases hnw with e | e <;> simp [e]
    simp only [hb, ↓reduceIte, run_pure, run_write_user_rflags hr hu hc.log, hnw]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hc.log) _ htr', ?_, ?_⟩
    · exact h.flagsRip R.2 _ hfR _
    · exact (hc.set (by decide) _).set (by decide) _
  · have hb : (operation == 8 || operation == 7) = false := by simp; omega
    have hl := hc.log
    simp only [hb, hnw, Bool.false_eq_true, ↓reduceIte]
    rw [run_write_rgfi_size h hl hW _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) R.1]
    have hn2' := locReg_lt p.rex.isSome w 0 (by decide)
    generalize hv : (regWrite js w (regLocOf p.rex.isSome w 0) R.1).regs (locReg (regLocOf p.rex.isSome w 0)) = V2
    have e1 : (setGpr s V2 (locReg (regLocOf p.rex.isSome w 0))).regs.get? .rflags = some rf := by
      rw [get?_setGpr_of_not s V2 hn2' rfl]; exact hr
    have e2 : (setGpr s V2 (locReg (regLocOf p.rex.isSome w 0))).regs.get? .janus_undef = some u := by
      rw [get?_setGpr_of_not s V2 hn2' rfl]; exact hu
    have e3 : (setGpr s V2 (locReg (regLocOf p.rex.isSome w 0))).regs.get? .log_register_writes = some false := by
      rw [get?_setGpr_of_not s V2 hn2' rfl]; exact hl
    simp only [run_write_user_rflags e1 e2 e3]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact e3) _ htr', ?_, ?_⟩
    · have hrel := h.writeReg p.rex.isSome (n := 0) (by decide) R.1
      rw [hv] at hrel
      have hdf : (regWrite js w (regLocOf p.rex.isSome w 0) R.1).df = js.df := by
        unfold regWrite; split <;> simp [Janus.Amd64.State.putReg, Janus.Amd64.State.putHigh, Janus.Amd64.State.setReg] <;> split <;> rfl
      exact hrel.flagsRip R.2 _ (by rw [hdf]; exact hfR) _
    · exact ((hc.setGpr hn2' V2).set (by decide) _).set (by decide) _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 in
/-- Janus' `execAlu` with a register destination and an immediate source. -/
theorem execAlu_regdst_imm {js js' : State} {next : BitVec 64} {op : AluOp} {w : Nat}
    {d : Loc} {v : Nat}
    (hd : readLoc js next w d = .ok (regVal js w d))
    (hdrw : readLocRW js next w d = .ok (regVal js w d))
    (hw : ∀ v, writeLoc js next w d v = .ok (regWrite js w d v))
    (hJ : execAlu js next op w d (.imm v) = .ok js') :
    ∃ c, ((op = .adc ∨ op = .sbb) → js.flags.cf = some c) ∧
      js' = ((if op = .cmp then js else regWrite js w d (aluRes op (regVal js w d) (BitVec.ofNat w v) c).1).setFlags
        (aluRes op (regVal js w d) (BitVec.ofNat w v) c).2).setRip next := by
  unfold execAlu at hJ
  simp only [readSrc] at hJ
  cases op
  all_goals first
    | (simp only [hdrw, hw] at hJ
       first
       | (refine ⟨false, by simp, ?_⟩; simp only [Except.ok.injEq] at hJ; simp [← hJ, aluRes])
       | (cases hc : js.flags.cf with
          | none => simp [hc] at hJ
          | some c =>
            refine ⟨c, fun _ => rfl, ?_⟩
            simp [hc, hw] at hJ; simp [← hJ, aluRes]))
    | (simp only [hd] at hJ
       refine ⟨false, by simp, ?_⟩; simp only [Except.ok.injEq] at hJ; simp [← hJ, aluRes])

theorem modrmP1_ai : ∀ o < 256, ((o < 0x40 ∧ (o % 8 = 4 ∨ o % 8 = 5)) ∨ o = 0xA8 ∨ o = 0xA9) → modrmP1 o = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem run_one_byte_rax_i (k f : Nat) (hk : k < 8) (hf : f = 4 ∨ f = 5) (sr tr : BitVec 48) (x : BitVec 52)
    (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 (8 * k + f)) m sib).run s =
      (x86_add_adc_sub_sbb_or_and_xor_cmp_test_rax_i (sailOp (Janus.Amd64.Decode.aluOp k)) .Mode_64bit sr tr x rex
          (BitVec.ofNat 8 (8 * k + f)) m sib).run s := by
  match k, hk, f, hf with
  | 0, _, 4, _ | 0, _, 5, _ | 1, _, 4, _ | 1, _, 5, _ | 2, _, 4, _ | 2, _, 5, _
  | 3, _, 4, _ | 3, _, 5, _ | 4, _, 4, _ | 4, _, 5, _ | 5, _, 4, _ | 5, _, 5, _
  | 6, _, 4, _ | 6, _, 5, _ | 7, _, 4, _ | 7, _, 5, _ =>
    simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
      ↓reduceIte, Bool.false_eq_true, Janus.Amd64.Decode.aluOp, sailOp, hl, run_bind, run_pure,
      show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxRecDepth 100000 in
theorem run_one_byte_test_a (o : Nat) (ho : o = 0xA8 ∨ o = 0xA9) (sr tr : BitVec 48) (x : BitVec 52)
    (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) m sib).run s =
      (x86_add_adc_sub_sbb_or_and_xor_cmp_test_rax_i 7 .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) m sib).run s := by
  rcases ho with rfl | rfl <;>
    simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
      ↓reduceIte, Bool.false_eq_true, hl, run_bind, run_pure, show (240#8 == 0#8) = false from rfl] <;> rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_ai {bytes : List Nat} {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n))
    (ho : (o < 0x40 ∧ (o % 8 = 4 ∨ o % 8 = 5)) ∨ o = 0xA8 ∨ o = 0xA9)
    {w : Nat} (hw : w = if o % 2 = 0 then 8 else osz p)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ ∃ v r, readLE (immBytes w) rest = some (v, r) ∧
      len = n + 1 + immBytes w ∧ len ≤ 15 ∧
      i = (if o < 0x40 then .alu (aluOp (o / 8)) w (.reg 0) (.imm (if w = 64 then sext 32 64 v else v))
        else .test w (.reg 0) (.imm (if w = 64 then sext 32 64 v else v))) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hno : ¬ (o = 0x0F) := by omega
  have hosz := osz_cases p
  rcases ho with ⟨ho1, ho2 | ho2⟩ | rfl | rfl
  · have hw8 : w = 8 := by rw [hw]; simp; omega
    subst hw8
    have hc1 : o < 0x40 ∧ o % 8 < 6 := ⟨ho1, by omega⟩
    simp only [immBytes, ↓reduceIte]
    simp (config := {decide := true}) only [hno, ↓reduceIte, oneByte, ho1, ho2, immU8, true_and, and_true] at hd
    cases hr : readLE 1 rest with
    | none => simp [hr] at hd
    | some vr =>
      obtain ⟨v, r⟩ := vr
      simp only [hr, finish] at hd
      by_cases hlen : n + 1 + 1 > 15
      · simp [hlen] at hd
      by_cases hrp : p.rep = 0
      · cases hf : p.fs <;> cases hl : p.lock <;> simp [hlen, hrp, hf, hl, lockable, withFS] at hd
        obtain ⟨rfl, rfl⟩ := hd
        exact ⟨rfl, rfl, hrp, v, r, rfl, rfl, by omega, by simp [ho1]⟩
      · simp [hlen, hrp] at hd
  · have hw8 : w = osz p := by rw [hw]; simp; omega
    subst hw8
    have hc1 : o < 0x40 ∧ o % 8 < 6 := ⟨ho1, by omega⟩
    have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
      simp [osz, rexW]
    simp (config := {decide := true}) only [hno, ↓reduceIte, oneByte, ho1, ho2, immZ, true_and, and_true, hou] at hd
    have hk : (if osz p = 8 then 1 else if osz p = 16 then 2 else 4) = immBytes (osz p) := rfl
    rw [hk] at hd
    cases hr : readLE (immBytes (osz p)) rest with
    | none => simp [hr] at hd
    | some vr =>
      obtain ⟨v, r⟩ := vr
      simp only [hr, finish] at hd
      by_cases hlen : n + 1 + immBytes (osz p) > 15
      · simp [hlen] at hd
      by_cases hrp : p.rep = 0
      · cases hf : p.fs <;> cases hl : p.lock <;> simp [hlen, hrp, hf, hl, lockable, withFS] at hd
        obtain ⟨rfl, rfl⟩ := hd
        exact ⟨rfl, rfl, hrp, v, r, rfl, rfl, by omega, by simp [ho1]⟩
      · simp [hlen, hrp] at hd
  · have hw8 : w = 8 := by simp [hw]
    subst hw8
    simp only [immBytes, ↓reduceIte]
    simp (config := {decide := true}) only [hno, ↓reduceIte, oneByte, immU8, true_and, and_true] at hd
    cases hr : readLE 1 rest with
    | none => simp [hr] at hd
    | some vr =>
      obtain ⟨v, r⟩ := vr
      simp only [hr, finish] at hd
      by_cases hlen : n + 1 + 1 > 15
      · simp [hlen] at hd
      by_cases hrp : p.rep = 0
      · cases hf : p.fs <;> cases hl : p.lock <;> simp [hlen, hrp, hf, hl, lockable, withFS] at hd
        obtain ⟨rfl, rfl⟩ := hd
        exact ⟨rfl, rfl, hrp, v, r, rfl, rfl, by omega, by simp⟩
      · simp [hlen, hrp] at hd
  · have hw8 : w = osz p := by rw [hw]; simp
    subst hw8
    have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
      simp [osz, rexW]
    simp (config := {decide := true}) only [hno, ↓reduceIte, oneByte, immZ, true_and, and_true, hou] at hd
    have hk : (if osz p = 8 then 1 else if osz p = 16 then 2 else 4) = immBytes (osz p) := rfl
    rw [hk] at hd
    cases hr : readLE (immBytes (osz p)) rest with
    | none => simp [hr] at hd
    | some vr =>
      obtain ⟨v, r⟩ := vr
      simp only [hr, finish] at hd
      by_cases hlen : n + 1 + immBytes (osz p) > 15
      · simp [hlen] at hd
      by_cases hrp : p.rep = 0
      · cases hf : p.fs <;> cases hl : p.lock <;> simp [hlen, hrp, hf, hl, lockable, withFS] at hd
        obtain ⟨rfl, rfl⟩ := hd
        exact ⟨rfl, rfl, hrp, v, r, rfl, rfl, by omega, by simp⟩
      · simp [hlen, hrp] at hd

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem sailOp_cmp (op : Janus.Amd64.AluOp) : (sailOp op = 8 ∨ sailOp op = 7) ↔ op = .cmp := by
  cases op <;> simp [sailOp]

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **ADD/OR/ADC/SBB/AND/SUB/XOR/CMP AL/AX/EAX/RAX, imm** (`04/05 … 3C/3D`) and **TEST
AL/AX/EAX/RAX, imm** (`A8/A9`), every width and prefix sequence Janus accepts, except the
byte forms with `REX.W` (Sail-x86 defect D2: the model operates on all of `RAX`). -/
theorem alu_ai_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: rest, n))
    (ho : (o < 0x40 ∧ (o % 8 = 4 ∨ o % 8 = 5)) ∨ o = 0xA8 ∨ o = 0xA9)
    (hD2 : ¬ (o % 2 = 0 ∧ rexW p = true))
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  generalize hw : (if o % 2 = 0 then 8 else osz p) = w
  obtain ⟨hlk, hfs, hrep, v, r, hr, rfl, hlen, rfl⟩ := decode_ai hpp ho hw.symm hd
  rw [step_of_decode hd] at hstep
  have hdrop : bytes.drop n = o :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have ho256 : o < 256 := by omega
  have hpg : prefixGroup o = 0 := by
    unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hmp : modrmP1 o = false := modrmP1_ai o ho256 ho
  have hcs : CodeAt s (js.rip.toNat + n + 1) rest := by
    have h2 : (bytes.drop n).drop 1 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 1)
    rw [show bytes.drop (n + 1) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 1) = js.rip.toNat + n + 1 by omega] at this
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + immBytes w)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + immBytes w) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  have hib1 : 1 ≤ immBytes w := by unfold immBytes; split <;> (try split) <;> omega
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [hmp]; simp [modrmSib])
  rw [hmp] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  have hib : immBytes w ≤ 4 := by unfold immBytes; split <;> (try split) <;> omega
  by_cases hA : o < 0x40
  · simp only [hA, ↓reduceIte, exec] at hstep
    rw [hnext] at hstep
    obtain ⟨cc, hcf, rfl⟩ := execAlu_regdst_imm (d := .reg 0) rfl rfl (fun _ => rfl) hstep
    have ho' : o = 8 * (o / 8) + o % 8 := by omega
    rw [ho', run_one_byte_rax_i (o / 8) (o % 8) (by omega) (by omega) _ _ x hl0] at hf
    rw [← ho'] at hf
    obtain ⟨s', hs', hrel', hcfg'⟩ := run_alu_rax_i hrel hcfg hpr hrv (sailOp (aluOp (o / 8))) (aluOp (o / 8))
      (Or.inl rfl) o ho256 hw.symm hD2 0#8 0#8 (js.rip.toNat + n + 1) hcs hr js.rip.toNat (by omega) (by omega)
      (by omega) cc hcf
    simp only [sailOp_cmp] at hrel'
    refine ⟨s', run_janus_x86_step (by rw [hf, hs']), ?_, hcfg'⟩
    rw [show js.rip.toNat + n + 1 + immBytes w = js.rip.toNat + n + 1 + immBytes w from rfl]
    exact hrel'
  · simp only [hA, ↓reduceIte, exec] at hstep
    rw [hnext] at hstep
    have hA8 : o = 0xA8 ∨ o = 0xA9 := by omega
    simp only [readLoc, readSrc, Except.ok.injEq] at hstep
    subst hstep
    rw [run_one_byte_test_a o hA8 _ _ x hl0] at hf
    obtain ⟨s', hs', hrel', hcfg'⟩ := run_alu_rax_i hrel hcfg hpr hrv 7 .and (Or.inr ⟨rfl, rfl⟩) o ho256 hw.symm hD2
      0#8 0#8 (js.rip.toNat + n + 1) hcs hr js.rip.toNat (by omega) (by omega) (by omega) false (by simp)
    simp only [show (7 = 8 ∨ 7 = 7) from Or.inr rfl, ↓reduceIte, aluRes] at hrel'
    exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hrel', hcfg'⟩

end JanusX86.Proofs
