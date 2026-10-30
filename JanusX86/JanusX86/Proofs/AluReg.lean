import JanusX86.Proofs.AluDispatch
import JanusX86.Proofs.Fields
import JanusX86.Proofs.Ip
import JanusX86.Proofs.Regs

/-! # ALU instructions, register forms -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem byteop_all : ∀ opc < 256, (0#1 == Sail.BitVec.truncate (1#8 &&& BitVec.ofNat 8 opc) 1) = decide (opc % 2 = 0) := by
  decide +kernel

/-- Janus' operand size from the prefixes (`oneByte`'s `osz`). -/
def osz (p : Janus.Amd64.Decode.Prefixes) : Nat := if rexW p then 64 else if p.opsize then 16 else 32

theorem osz_cases (p : Janus.Amd64.Decode.Prefixes) : osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := by
  unfold osz; split <;> (try split) <;> simp

theorem size_int (p : Janus.Amd64.Decode.Prefixes) (b : Bool) :
    (if b = true then (1 : Int) else if rexW p = true then (if false = true then 4 else 8) else if p.opsize = true then 2 else 4) =
      (((if b then 8 else osz p) / 8 : Nat) : Int) := by
  unfold osz; cases b <;> cases rexW p <;> cases p.opsize <;> rfl

theorem run_select_segment_register {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8}
    (hp : PfxRel p x rex) (md : BitVec 2) (rm : BitVec 3) (sib : BitVec 8) (s : SState) :
    ∃ sg, (select_segment_register .Mode_64bit x md rm sib).run s = .ok sg s ∧ (sg = 4 ↔ p.fs = true) ∧
      sg ≠ 5 := by
  have hseg := hp.seg
  have hadr : (0x67#8 == _get_prefixes_adr x) = false := by rw [hp.adr]; decide
  cases hf : p.fs
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hseg
    simp only [select_segment_register, hseg, eq_bits_nat]
    simp (config := {decide := true}) only [↓reduceIte, run_bind, run_select_address_size x hadr]
    split
    · exact ⟨2, rfl, by simp, by decide⟩
    · exact ⟨3, rfl, by simp, by decide⟩
  · simp only [hf, ↓reduceIte] at hseg
    simp only [select_segment_register, hseg, eq_bits_nat]
    simp (config := {decide := true}) only [↓reduceIte]
    exact ⟨4, rfl, by simp, by decide⟩

theorem run_operand_from_reg {js : Janus.Amd64.State} {s : SState} (h : Rel js s) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (rexP : Bool) (rex : BitVec 8) (hrex : (rex == 0#8) = !rexP)
    {n : Nat} (hn : n < 16) (hn8 : n < 8 ∨ rexP = true) (a : BitVec 3) (hidx : reg_index a rex 0#2 = BitVec.ofNat 4 n)
    (iac mp : Bool) (sg : Nat) (x : BitVec 52) (tr : BitVec 48) (sib : BitVec 8) (ni : BitVec 3) :
    (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) iac mp sg x tr rex a 3#2 sib ni).run s =
      .ok (((regVal js w (regLocOf rexP w n)).setWidth 64).setWidth 128, 0, 0#64) s := by
  have e : bits_of_int ((w / 8 : Nat) : Int) 4 = BitVec.ofNat 4 (w / 8) := nbytes_eq w hw
  simp only [x86_operand_from_modr_m_and_sib_bytes, run_bind, run_pure, ↓reduceIte, e, hidx,
    run_rgfi_size h hw rexP rex hrex hn hn8, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
  simp (config := {decide := true}) only [↓reduceIte, run_pure, run_bind, run_rgfi_size h hw rexP rex hrex hn hn8]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem readLoc_regLocOf (js : Janus.Amd64.State) (next : BitVec 64) (w : Nat) (rexP : Bool) (n : Nat) :
    Janus.Amd64.readLoc js next w (regLocOf rexP w n) = .ok (regVal js w (regLocOf rexP w n)) := by
  unfold regLocOf Janus.Amd64.Decode.reg8
  split
  · split <;> rfl
  · rfl

theorem readLocRW_regLocOf (js : Janus.Amd64.State) (next : BitVec 64) (w : Nat) (rexP : Bool) (n : Nat) :
    Janus.Amd64.readLocRW js next w (regLocOf rexP w n) = .ok (regVal js w (regLocOf rexP w n)) := by
  unfold regLocOf Janus.Amd64.Decode.reg8
  split
  · split <;> rfl
  · rfl

theorem writeLoc_regLocOf (js : Janus.Amd64.State) (next : BitVec 64) (w : Nat) (rexP : Bool) (n : Nat)
    (v : BitVec w) :
    Janus.Amd64.writeLoc js next w (regLocOf rexP w n) v = .ok (regWrite js w (regLocOf rexP w n) v) := by
  unfold regLocOf Janus.Amd64.Decode.reg8
  split
  · split <;> rfl
  · rfl

/-- Janus' `execAlu` on register operands. -/
theorem execAlu_reg {js js' : Janus.Amd64.State} {next : BitVec 64} {op : Janus.Amd64.AluOp} {w : Nat}
    {d : Janus.Amd64.Loc} {sl : Janus.Amd64.Loc}
    (hd : Janus.Amd64.readLoc js next w d = .ok (regVal js w d))
    (hdrw : Janus.Amd64.readLocRW js next w d = .ok (regVal js w d))
    (hs : Janus.Amd64.readLoc js next w sl = .ok (regVal js w sl))
    (hw : ∀ v, Janus.Amd64.writeLoc js next w d v = .ok (regWrite js w d v))
    (hJ : Janus.Amd64.execAlu js next op w d (.loc sl) = .ok js') :
    ∃ c, ((op = .adc ∨ op = .sbb) → js.flags.cf = some c) ∧
      js' = ((if op = .cmp then js else regWrite js w d (aluRes op (regVal js w d) (regVal js w sl) c).1).setFlags
        (aluRes op (regVal js w d) (regVal js w sl) c).2).setRip next := by
  unfold Janus.Amd64.execAlu at hJ
  simp only [Janus.Amd64.readSrc, hs] at hJ
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

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem bv1_ofBool (b : BitVec 1) : b = BitVec.ofBool (b == 1#1) := by
  revert b; decide

theorem aluRes_c (op : Janus.Amd64.AluOp) {w : Nat} (x y : BitVec w) (c c' : Bool)
    (h : (op = .adc ∨ op = .sbb) → c = c') : aluRes op x y c = aluRes op x y c' := by
  cases op <;> simp [aluRes] at h ⊢ <;> simp [h]

theorem rex_hrex {p : Janus.Amd64.Decode.Prefixes} (hrv : ∀ r, p.rex = some r → r < 16) :
    (BitVec.ofNat 8 (rexByte p) == 0#8) = !p.rex.isSome := by
  unfold rexByte; cases e : p.rex with
  | none => rfl
  | some r =>
    have := hrv r e
    simp only [Option.isSome_some, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    intro h; have := congrArg BitVec.toNat h; simp at this; omega

theorem run_add_to_iptr0 (tr : Nat) (htr : tr < 2 ^ 47) (s : SState) :
    (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (Sail.BitVec.zeroExtend (bits_of_int 0 3) 48)).run s =
      .ok (BitVec.ofNat 48 tr) s := by
  have z : Sail.BitVec.zeroExtend (bits_of_int 0 3) 48 = 0#48 := by decide
  rw [z, run_add_to_iptr _ _ (by simp; omega)]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.add_zero, Nat.zero_mod]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem trunc128 (v : BitVec 64) : Sail.BitVec.truncate (BitVec.setWidth 128 v) 64 = v := by
  apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate]

theorem run_operand_to_reg {js : Janus.Amd64.State} {s : SState} (h : Rel js s)
    (hl : s.regs.get? .log_register_writes = some false) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (rexP : Bool) (rex : BitVec 8) (hrex : (rex == 0#8) = !rexP)
    {n : Nat} (hn : n < 16) (hn8 : n < 8 ∨ rexP = true) (a : BitVec 3) (hidx : reg_index a rex 0#2 = BitVec.ofNat 4 n)
    (iac mp : Bool) (sg : Nat) (ad : BitVec 64) (x : BitVec 52) (sib : BitVec 8) (v : BitVec w) :
    (x86_operand_to_reg_mem .Mode_64bit (w / 8) iac mp ((v.setWidth 64).setWidth 128) sg ad x rex a 3#2 sib).run s =
      .ok () (setGpr s ((regWrite js w (regLocOf rexP w n) v).regs (locReg (regLocOf rexP w n)))
        (locReg (regLocOf rexP w n))) := by
  simp only [x86_operand_to_reg_mem, show ((3#2 : BitVec 2) == 3#2) = true from rfl, ↓reduceIte, nbytes_eq w hw,
    hidx, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, trunc128]
  exact run_write_rgfi_size h hl hw rexP rex hrex hn hn8 v

end JanusX86.Proofs


namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- The common part of the register-form ALU theorems: the model computes Janus' ALU result
`aluRes op d s` and writes it to the destination register (unless `CMP`), its flags and `RIP`. -/
def aluNext (js : Janus.Amd64.State) (op : Janus.Amd64.AluOp) (w : Nat) (d : Janus.Amd64.Loc)
    (R : BitVec w × Janus.Amd64.Flags) (next : BitVec 64) : Janus.Amd64.State :=
  ((if op = .cmp then js else regWrite js w d R.1).setFlags R.2).setRip next

theorem run_alu_e_g_reg {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (op : Janus.Amd64.AluOp) (opc : Nat) (hopc : opc < 256)
    {w : Nat} (hw : w = if opc % 2 = 0 then 8 else osz p)
    (m : Nat) (hm : m < 256) (hmod : m / 64 = 3) {n1 n2 : Nat} (hn1 : n1 < 16) (hn2 : n2 < 16)
    (h81 : n1 < 8 ∨ p.rex.isSome = true) (h82 : n2 < 8 ∨ p.rex.isSome = true)
    (hidx1 : reg_index (BitVec.ofNat 3 (m % 8)) rex 0#2 = BitVec.ofNat 4 n1)
    (hidx2 : reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 = BitVec.ofNat 4 n2)
    (sr tr : Nat) (hl1 : sr ≤ tr) (hl2 : tr ≤ sr + 15) (htr : tr < 2 ^ 47) (sib : BitVec 8)
    (c : Bool) (hcf : (op = .adc ∨ op = .sbb) → js.flags.cf = some c) :
    ∃ s', (x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g (sailOp op) .Mode_64bit (BitVec.ofNat 48 sr)
      (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc) (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (aluNext js op w (regLocOf p.rex.isSome w n1)
        (aluRes op (regVal js w (regLocOf p.rex.isSome w n1)) (regVal js w (regLocOf p.rex.isSome w n2)) c)
        (BitVec.ofNat 64 tr)) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  obtain ⟨r, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  obtain ⟨sg, hsg, -, -⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  have hsz : (if decide (opc % 2 = 0) = true then (1 : Int) else if rexW p = true then 8
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    have := size_int p (decide (opc % 2 = 0)); simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [this, hw]; simp
  simp only [hmod] at hsg
  -- the carry-in the model reads
  let c' := (_get_rflagsbits_cf r == 1#1)
  have hc' : _get_rflagsbits_cf r = BitVec.ofBool c' := bv1_ofBool _
  have hcc : aluRes op (regVal js w (regLocOf p.rex.isSome w n1)) (regVal js w (regLocOf p.rex.isSome w n2)) c' =
      aluRes op (regVal js w (regLocOf p.rex.isSome w n1)) (regVal js w (regLocOf p.rex.isSome w n2)) c := by
    apply aluRes_c; intro hop
    have := hfr.cf c (hcf hop)
    show (_get_rflagsbits_cf r == 1#1) = c
    rw [this]; cases c <;> rfl
  have hlen := check_len_ok sr tr hl1 hl2 htr
  simp only [x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g, h1, h2, h3, hmod, run_bind,
    run_select_operand_size hp hrv, byteop_all opc hopc, hsz, nbytes_eq w hW, hidx2,
    run_rgfi_size h hW _ rex hrex hn2 h82, hsg, Int.toNat_natCast,
    run_operand_from_reg h hW _ rex hrex hn1 h81 _ hidx1, run_add_to_iptr0 tr htr, hlen, is_some,
    Bool.false_eq_true, ↓reduceIte, run_pure, run_readReg hr, trunc128,
    run_gpr_arith_logic_spec op hW _ _ r c' hc', hcc]
  generalize hR : aluRes op (regVal js w (regLocOf p.rex.isSome w n1)) (regVal js w (regLocOf p.rex.isSome w n2)) c = R
  have hfR : FlagsRel R.2 js.df (wurf r (aluOut op r R.2).1 (aluOut op r R.2).2 u) := by
    rw [← hR]; exact flagsRel_aluOut hfr op _ _ c u
  by_cases hcmp : op = .cmp
  · subst hcmp
    simp only [sailOp, show ((8 : Nat) == 8 || (8 : Nat) == 7) = true from rfl, ↓reduceIte, run_pure,
      run_write_user_rflags hr hu hc.log]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hc.log) tr htr, ?_, ?_⟩
    · simp only [aluNext, ↓reduceIte]
      exact h.flagsRip R.2 _ hfR _
    · exact (hc.set (by decide) _).set (by decide) _
  · have hop : (sailOp op == 8 || sailOp op == 7) = false := by cases op <;> simp_all [sailOp]
    have hl := hc.log
    simp only [hop, Bool.false_eq_true, ↓reduceIte, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
    simp only [run_operand_to_reg h hl hW _ rex hrex hn1 h81 _ hidx1]
    have hn1' := locReg_lt p.rex.isSome w n1 hn1
    generalize hv : (regWrite js w (regLocOf p.rex.isSome w n1) R.1).regs (locReg (regLocOf p.rex.isSome w n1)) = V
    have e1 : (setGpr s V (locReg (regLocOf p.rex.isSome w n1))).regs.get? .rflags = some r := by
      rw [get?_setGpr_of_not s V hn1' rfl]; exact hr
    have e2 : (setGpr s V (locReg (regLocOf p.rex.isSome w n1))).regs.get? .janus_undef = some u := by
      rw [get?_setGpr_of_not s V hn1' rfl]; exact hu
    have e3 : (setGpr s V (locReg (regLocOf p.rex.isSome w n1))).regs.get? .log_register_writes = some false := by
      rw [get?_setGpr_of_not s V hn1' rfl]; exact hl
    simp only [run_write_user_rflags e1 e2 e3]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact e3) tr htr, ?_, ?_⟩
    · simp only [aluNext, hcmp, ↓reduceIte]
      have hrel := h.writeReg p.rex.isSome hn1 R.1
      rw [hv] at hrel
      have hdf : (regWrite js w (regLocOf p.rex.isSome w n1) R.1).df = js.df := by
        unfold regWrite; split <;> simp [Janus.Amd64.State.putReg, Janus.Amd64.State.putHigh, Janus.Amd64.State.setReg] <;> split <;> rfl
      exact hrel.flagsRip R.2 _ (by rw [hdf]; exact hfR) _
    · exact ((hc.setGpr hn1' V).set (by decide) _).set (by decide) _

end JanusX86.Proofs
