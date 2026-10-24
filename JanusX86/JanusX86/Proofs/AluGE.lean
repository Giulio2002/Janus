import JanusX86.Proofs.AluClassMem

/-! # ALU (G, E) forms: register destination, register or memory source -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 in
/-- Janus' `execAlu` with a register destination and any source operand. -/
theorem execAlu_regdst {js js' : State} {next : BitVec 64} {op : AluOp} {w : Nat}
    {d : Loc} {sl : Loc} {V : BitVec w}
    (hd : readLoc js next w d = .ok (regVal js w d))
    (hdrw : readLocRW js next w d = .ok (regVal js w d))
    (hs : readLoc js next w sl = .ok V)
    (hw : ∀ v, writeLoc js next w d v = .ok (regWrite js w d v))
    (hJ : execAlu js next op w d (.loc sl) = .ok js') :
    ∃ c, ((op = .adc ∨ op = .sbb) → js.flags.cf = some c) ∧
      js' = ((if op = .cmp then js else regWrite js w d (aluRes op (regVal js w d) V c).1).setFlags
        (aluRes op (regVal js w d) V c).2).setRip next := by
  unfold execAlu at hJ
  simp only [readSrc, hs] at hJ
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

theorem run_alu_g_e {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (op : Janus.Amd64.AluOp) (opc : Nat) (hopc : opc < 256)
    {w : Nat} (hw : w = if opc % 2 = 0 then 8 else osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr te : Nat) (V : BitVec w) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib 0#3).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hinc : inc < 8) (hte : te = tr + inc) (htr : te < 2 ^ 47)
    {n2 : Nat} (hn2 : n2 < 16) (h82 : n2 < 8 ∨ p.rex.isSome = true)
    (hidx2 : reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 = BitVec.ofNat 4 n2)
    (sr : Nat) (hl1 : sr ≤ te) (hl2 : te ≤ sr + 15)
    (cc : Bool) (hcf : (op = .adc ∨ op = .sbb) → js.flags.cf = some cc) :
    ∃ s', (x86_add_adc_sub_sbb_or_and_xor_cmp_g_e (sailOp op) .Mode_64bit (BitVec.ofNat 48 sr)
      (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc) (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (aluNext js op w (regLocOf p.rex.isSome w n2)
        (aluRes op (regVal js w (regLocOf p.rex.isSome w n2)) V cc) (BitVec.ofNat 64 te)) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  obtain ⟨r, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  have hsz : (if decide (opc % 2 = 0) = true then (1 : Int) else if rexW p = true then 8
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    have := size_int p (decide (opc % 2 = 0)); simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [this, hw]; simp
  let c' := (_get_rflagsbits_cf r == 1#1)
  have hc' : _get_rflagsbits_cf r = BitVec.ofBool c' := bv1_ofBool _
  have hcc : aluRes op (regVal js w (regLocOf p.rex.isSome w n2)) V c' =
      aluRes op (regVal js w (regLocOf p.rex.isSome w n2)) V cc := by
    apply aluRes_c; intro hop
    have := hfr.cf cc (hcf hop)
    show (_get_rflagsbits_cf r == 1#1) = cc
    rw [this]; cases cc <;> rfl
  have hinc' : (bits_of_int (inc : Int) 3) = BitVec.ofNat 3 inc := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have hadd : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48)).run s =
      .ok (BitVec.ofNat 48 te) s := by
    have ez : (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48).toNat = inc := by
      simp [Sail.BitVec.zeroExtend]; omega
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hlen := check_len_ok sr te hl1 hl2 htr
  simp only [x86_add_adc_sub_sbb_or_and_xor_cmp_g_e, h1, h2, h3, run_bind,
    run_select_operand_size hp hrv, byteop_all opc hopc, hsz, nbytes_eq w hW, hidx2,
    run_rgfi_size h hW _ rex hrex hn2 h82, hsg, Int.toNat_natCast, hX sg hsg4 hsg5, hinc', hadd, hlen, is_some,
    Bool.false_eq_true, ↓reduceIte, run_pure, run_readReg hr, trunc128,
    run_gpr_arith_logic_spec op hW _ _ r c' hc', hcc]
  generalize hR : aluRes op (regVal js w (regLocOf p.rex.isSome w n2)) V cc = R
  have hfR : FlagsRel R.2 js.df (wurf r (aluOut op r R.2).1 (aluOut op r R.2).2 u) := by
    rw [← hR]; exact flagsRel_aluOut hfr op _ _ cc u
  by_cases hcmp : op = .cmp
  · subst hcmp
    simp only [sailOp, show ((8 : Nat) == 8) = true from rfl, ↓reduceIte, run_pure,
      run_write_user_rflags hr hu hc.log]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hc.log) te htr, ?_, ?_⟩
    · simp only [aluNext, ↓reduceIte]
      exact h.flagsRip R.2 _ hfR _
    · exact (hc.set (by decide) _).set (by decide) _
  · have hop : (sailOp op == 8) = false := by cases op <;> simp_all [sailOp]
    have hl := hc.log
    simp only [hop, Bool.false_eq_true, ↓reduceIte]
    rw [run_write_rgfi_size h hl hW _ rex hrex hn2 h82 R.1]
    have hn2' := locReg_lt p.rex.isSome w n2 hn2
    generalize hv : (regWrite js w (regLocOf p.rex.isSome w n2) R.1).regs (locReg (regLocOf p.rex.isSome w n2)) = V2
    have e1 : (setGpr s V2 (locReg (regLocOf p.rex.isSome w n2))).regs.get? .rflags = some r := by
      rw [get?_setGpr_of_not s V2 hn2' rfl]; exact hr
    have e2 : (setGpr s V2 (locReg (regLocOf p.rex.isSome w n2))).regs.get? .janus_undef = some u := by
      rw [get?_setGpr_of_not s V2 hn2' rfl]; exact hu
    have e3 : (setGpr s V2 (locReg (regLocOf p.rex.isSome w n2))).regs.get? .log_register_writes = some false := by
      rw [get?_setGpr_of_not s V2 hn2' rfl]; exact hl
    simp only [run_write_user_rflags e1 e2 e3]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact e3) te htr, ?_, ?_⟩
    · simp only [aluNext, hcmp, ↓reduceIte]
      have hrel := h.writeReg p.rex.isSome hn2 R.1
      rw [hv] at hrel
      have hdf : (regWrite js w (regLocOf p.rex.isSome w n2) R.1).df = js.df := by
        unfold regWrite; split <;> simp [Janus.Amd64.State.putReg, Janus.Amd64.State.putHigh, Janus.Amd64.State.setReg] <;> split <;> rfl
      exact hrel.flagsRip R.2 _ (by rw [hdf]; exact hfR) _
    · exact ((hc.setGpr hn2' V2).set (by decide) _).set (by decide) _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem modrm_r {rx m : Nat} {rest : List Nat} {md reg ext k : Nat} {r3 : List Nat} {c : Nat}
    (h : modrm rx (m :: rest) = some (⟨md, reg, ext, .r k⟩, r3, c)) :
    m / 64 = 3 ∧ k = m % 8 + 8 * (rx % 2) ∧ c = 1 ∧ r3 = rest := by
  revert h
  unfold modrm
  simp only
  repeat' split
  all_goals intro h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq, ModRM.mk.injEq, RM.r.injEq] at h; omega)
    | (simp only [Option.some.injEq, Prod.mk.injEq, ModRM.mk.injEq, RM.r.injEq] at h
       obtain ⟨⟨-, -, -, rfl⟩, rfl, rfl⟩ := h; exact ⟨by omega, rfl, rfl, rfl⟩)

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_ge {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o < 0x40) (ho2 : 2 ≤ o % 8) (ho3 : o % 8 < 4)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.rep = 0 ∧ len = n + 1 + c ∧ len ≤ 15 ∧
      i = .alu (aluOp (o / 8)) (if o % 2 = 0 then 8 else osz p)
        (regLocOf p.rex.isSome (if o % 2 = 0 then 8 else osz p) (regNum p m))
        (.loc (match mm.rm with
          | .r k => regLocOf p.rex.isSome (if o % 2 = 0 then 8 else osz p) k
          | .m a => .mem (if p.fs then { a with fs := true } else a))) ∧
      (∀ k, mm.rm = .r k → p.fs = false) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hno : ¬ (o = 0x0F) := by omega
  have hc1 : o < 0x40 ∧ o % 8 < 6 := ⟨ho, by omega⟩
  have hf4 : ¬ (o % 8 = 4) := by omega
  have hf5 : ¬ (o % 8 = 5) := by omega
  have hf2 : ¬ (o % 8 < 2) := by omega
  have hreg : mm.reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hreg; subst hreg
  simp only [hno, ↓reduceIte, oneByte, hc1, and_self, hf4, hf5, hmd, hf2, osz_eq] at hd
  have hrg : ∀ w, regLoc p.rex.isSome w (regNum p m) = regLocOf p.rex.isSome w (regNum p m) := fun _ => rfl
  simp only [hrg, finish] at hd
  by_cases hlen : n + 1 + c > 15
  · simp [hlen] at hd
  by_cases hr : p.rep = 0
  · simp only [hlen, hr, ↓reduceIte] at hd
    cases rm with
    | r k =>
      have hrm : ∀ w, rmLoc p.rex.isSome w (RM.r k) = regLocOf p.rex.isSome w k := fun _ => rfl
      simp only [hrm, lockable_alu_reg] at hd
      cases hf : p.fs <;> cases hl : p.lock <;> simp [hf, hl, withFS_alu_reg] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact ⟨rfl, hr, rfl, by omega, rfl, fun _ _ => rfl⟩
    | m a =>
      simp only [rmLoc, lockable_alu_reg] at hd
      cases hf : p.fs <;> cases hl : p.lock <;> simp [hf, hl, withFS] at hd
      · obtain ⟨rfl, rfl⟩ := hd
        exact ⟨rfl, hr, rfl, by omega, by simp, fun _ h => by cases h⟩
      · rcases regLocOf_cases p.rex.isSome (if o % 2 = 0 then 8 else osz p) (regNum p m) with ⟨r', e⟩ | ⟨r', e⟩ <;>
          rw [e] at hd <;> simp at hd <;> obtain ⟨rfl, rfl⟩ := hd <;>
          exact ⟨rfl, hr, rfl, by omega, by simp [e], fun _ h => by cases h⟩
  · simp [hlen, hr] at hd

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **ADD/OR/ADC/SBB/AND/SUB/XOR/CMP r, r/m** (opcodes `02/03 … 3A/3B`): every ModRM form
(register, or memory with every addressing form incl. SIB, RIP- and FS-relative), every width
and prefix sequence Janus accepts. -/
theorem alu_ge_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o < 0x40) (ho2 : 2 ≤ o % 8) (ho3 : o % 8 < 4)
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
    have hno : ¬ (o = 0x0F) := by omega
    have hc1 : o < 0x40 ∧ o % 8 < 6 := ⟨ho, by omega⟩
    simp [hno, oneByte, hc1, show ¬ (o % 8 = 4) by omega, show ¬ (o % 8 = 5) by omega, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hlk, hrep, rfl, hlen, rfl, hfs⟩ := decode_ge hpp ho ho2 ho3 hmd hd
  rw [step_of_decode hd] at hstep
  simp only [exec] at hstep
  generalize hw : (if o % 2 = 0 then 8 else osz p) = w at hstep
  have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hm256 : m < 256 := hcode.1 m (by
    have : m ∈ bytes.drop n := by rw [hdrop]; simp
    exact List.mem_of_mem_drop this)
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hpg : prefixGroup o = 0 := by
    unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hmp : modrmP1 o = true := modrmP1_eg o ho (by omega)
  have hcs : CodeAt s (js.rip.toNat + n + 1 + 1) rest := by
    have h2 : (bytes.drop n).drop 2 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 2); rw [show bytes.drop (n + 2) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 2) = js.rip.toNat + n + 1 + 1 by omega] at this
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c)) % 2 ^ 64) = BitVec.ofNat 64 (js.rip.toNat + n + 1 + c) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  rw [hnext] at hstep
  obtain ⟨md, rg, ext, rm⟩ := mm
  cases rm with
  | r k =>
    obtain ⟨h3, rfl, rfl, -⟩ := modrm_r hmd
    have hfs' := hfs _ rfl
    simp only at hstep
    obtain ⟨cc, hcf, rfl⟩ := execAlu_regdst (readLoc_regLocOf _ _ _ _ _) (readLocRW_regLocOf _ _ _ _ _)
      (readLoc_regLocOf _ _ _ _ _) (writeLoc_regLocOf _ _ _ _ _) hstep
    have hms : modrmSib (modrmP1 o) (m :: rest) = (BitVec.ofNat 8 m, 0#8, 1) := by
      simp [modrmSib, hmp, sibP_reg m h3]
    obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
      ⟨by omega, by omega, by omega⟩ (by rw [hms]; simp)
    rw [hms] at hf
    simp only at hf
    have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hpr.rexb]; rfl
    have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
    have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
    have ho' : o = 8 * (o / 8) + o % 8 := by omega
    rw [ho', run_one_byte_g_e (o / 8) (o % 8) (by omega) ⟨ho2, ho3⟩ _ _ x hl0] at hf
    rw [← ho'] at hf
    have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
      rw [← hw]; split
      · simp
      · rcases osz_cases p with e | e | e <;> simp [e]
    obtain ⟨s', hs', hrel', hcfg'⟩ := run_alu_g_e hrel hcfg hpr hrv (aluOp (o / 8)) o (by omega) hw.symm m hm256 0#8
      (js.rip.toNat + n + 1 + 1) (js.rip.toNat + n + 1 + 1)
      (regVal js w (regLocOf p.rex.isSome w (m % 8 + 8 * (p.rex.getD 0 % 2)))) 0 0#64
      (fun sg _ _ => by
        rw [h3]
        exact run_operand_from_reg hrel hW _ rex hrex (rmNum_lt p m) (rmNum_8 p m) _
          (by rw [hrexb]; exact hidx_rm hrv m) true false sg x _ 0#8 0#3)
      (by decide) rfl (by omega) (regNum_lt p m) (regNum_8 p m) (by rw [hrexb]; exact hidx_reg hrv m)
      js.rip.toNat (by omega) (by omega) cc hcf
    rw [show js.rip.toNat + n + 1 + 1 = js.rip.toNat + n + 1 + 1 from rfl] at hs'
    refine ⟨s', run_janus_x86_step (by rw [hf, hs']), hrel', hcfg'⟩
  | m a =>
    simp only at hstep
    generalize hNX : BitVec.ofNat 64 (js.rip.toNat + n + 1 + c) = NX at hstep
    cases hrd : readLoc js NX w (.mem (if p.fs then { a with fs := true } else a)) with
    | error e =>
      exfalso; unfold execAlu at hstep; simp [readSrc, hrd] at hstep
    | ok V =>
    obtain ⟨hacc, hV⟩ := readLoc_mem hrd
    obtain ⟨cc, hcf, rfl⟩ := execAlu_regdst (readLoc_regLocOf _ _ _ _ _) (readLocRW_regLocOf _ _ _ _ _)
      hrd (writeLoc_regLocOf _ _ _ _ _) hstep
    obtain ⟨hc1, hc6, hmd3⟩ := modrm_c_ge hmd
    have hsl : (1 + (if sibP m then 1 else 0)) ≤ (m :: rest).length := by
      cases rest with
      | cons _ _ => simp; split <;> omega
      | nil =>
        cases hs : sibP m
        · simp
        · exfalso
          unfold sibP at hs; simp at hs
          unfold modrm at hmd; simp [hs.1] at hmd
    obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
      ⟨by omega, by omega, by omega⟩ (by rw [hmp, modrmSib_eq]; simp at hsl ⊢; omega)
    rw [hmp, modrmSib_eq] at hf
    simp only at hf
    have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hpr.rexb]; rfl
    have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
    have ho' : o = 8 * (o / 8) + o % 8 := by omega
    rw [ho', run_one_byte_g_e (o / 8) (o % 8) (by omega) ⟨ho2, ho3⟩ _ _ x hl0] at hf
    rw [← ho'] at hf
    have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
      rw [← hw]; split
      · simp
      · rcases osz_cases p with e | e | e <;> simp [e]
    rw [← hNX] at hacc hV
    obtain ⟨s', hs', hrel', hcfg'⟩ := run_alu_g_e hrel hcfg hpr hrv (aluOp (o / 8)) o (by omega) hw.symm m hm256
      (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8)
      (js.rip.toNat + n + 1 + 1 + (if sibP m then 1 else 0)) (js.rip.toNat + n + 1 + c) V
      (c - 1 - (if sibP m then 1 else 0)) (eaOff js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c)) a)
      (fun sg hsg4 hsg5 => by
        rw [hV]
        have := run_operand_from_mem hrel hcfg hpr hrv hcs hm256 hmd (nimm := 0) (by decide) (by omega) hW hsg4 hsg5
          true false (by simpa using hacc)
        simpa using this)
      (by omega) (by omega) (by omega) (regNum_lt p m) (regNum_8 p m)
      (by rw [hrexb]; exact hidx_reg hrv m) js.rip.toNat (by omega) (by omega) cc hcf
    rw [show js.rip.toNat + n + 1 + (1 + (if sibP m then 1 else 0)) = js.rip.toNat + n + 1 + 1 + (if sibP m then 1 else 0)
      by omega] at hf
    rw [← hNX]
    exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hrel', hcfg'⟩

end JanusX86.Proofs
