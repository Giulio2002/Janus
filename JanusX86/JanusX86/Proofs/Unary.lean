import JanusX86.Proofs.Frame

/-! # INC/DEC (`FE/FF /0,/1`) and NOT/NEG (`F6/F7 /2,/3`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

/-- `write_user_rflags` against Janus' flags, one status flag at a time. -/
theorem flagsRel_wurf {f0 : Flags} {df : Bool} {r : BitVec 32} (hr : FlagsRel f0 df r) (f : Flags)
    (out undef : BitVec 32) (u : Nat)
    (hcf : FlagEq f.cf (if _get_rflagsbits_cf undef == 1#1 then bits_of_int (u : Int) 1 else _get_rflagsbits_cf out))
    (hpf : FlagEq f.pf (if _get_rflagsbits_pf undef == 1#1 then bits_of_int (u : Int) 1 else _get_rflagsbits_pf out))
    (haf : FlagEq f.af (if _get_rflagsbits_af undef == 1#1 then bits_of_int (u : Int) 1 else _get_rflagsbits_af out))
    (hzf : FlagEq f.zf (if _get_rflagsbits_zf undef == 1#1 then bits_of_int (u : Int) 1 else _get_rflagsbits_zf out))
    (hsf : FlagEq f.sf (if _get_rflagsbits_sf undef == 1#1 then bits_of_int (u : Int) 1 else _get_rflagsbits_sf out))
    (hof : FlagEq f.ovf (if _get_rflagsbits_of undef == 1#1 then bits_of_int (u : Int) 1 else _get_rflagsbits_of out)) :
    FlagsRel f df (wurf r out undef u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [wurf, rf_get_cf_upd_cf, rf_get_cf_upd_pf, rf_get_cf_upd_af, rf_get_cf_upd_zf, rf_get_cf_upd_sf, rf_get_cf_upd_of,
    rf_get_pf_upd_cf, rf_get_pf_upd_pf, rf_get_pf_upd_af, rf_get_pf_upd_zf, rf_get_pf_upd_sf, rf_get_pf_upd_of,
    rf_get_af_upd_cf, rf_get_af_upd_pf, rf_get_af_upd_af, rf_get_af_upd_zf, rf_get_af_upd_sf, rf_get_af_upd_of,
    rf_get_zf_upd_cf, rf_get_zf_upd_pf, rf_get_zf_upd_af, rf_get_zf_upd_zf, rf_get_zf_upd_sf, rf_get_zf_upd_of,
    rf_get_sf_upd_cf, rf_get_sf_upd_pf, rf_get_sf_upd_af, rf_get_sf_upd_zf, rf_get_sf_upd_sf, rf_get_sf_upd_of,
    rf_get_of_upd_cf, rf_get_of_upd_pf, rf_get_of_upd_af, rf_get_of_upd_zf, rf_get_of_upd_sf, rf_get_of_upd_of,
    rf_get_df_upd_cf, rf_get_df_upd_pf, rf_get_df_upd_af, rf_get_df_upd_zf, rf_get_df_upd_sf, rf_get_df_upd_of,
    rf_get_ac_upd_cf, rf_get_ac_upd_pf, rf_get_ac_upd_af, rf_get_ac_upd_zf, rf_get_ac_upd_sf, rf_get_ac_upd_of]
  all_goals first | assumption | exact hr.df | exact hr.ac

theorem Rel.setFlagsR {js : State} {s : SState} (h : Rel js s) (f : Flags) (r : BitVec 32) (hf : FlagsRel f js.df r) :
    Rel (js.setFlags f) (s.set .rflags r) := by
  obtain ⟨m, hm, hmr⟩ := h.fs
  refine ⟨?_, ?_, ⟨r, by simp, hf⟩, ⟨m, ?_, hmr⟩, h.mem, h.canon⟩
  · intro i hi; rw [gprVal_set_of_not _ rfl]; exact h.gpr i hi
  · rw [get?_set_ne _ _ (by decide)]; exact h.rip
  · rw [get?_set_ne _ _ (by decide)]; exact hm

theorem Rel.setRipR {js : State} {s : SState} (h : Rel js s) (v : BitVec 64) :
    Rel (js.setRip v) (s.set .rip v) := by
  obtain ⟨r, hr, hfr⟩ := h.flags
  have := h.flagsRip js.flags r hfr v
  rwa [set_self hr, show js.setFlags js.flags = js by cases js; rfl] at this

theorem locWrite_setFlags (js : State) (next : BitVec 64) (w : Nat) (D : Loc) (y : BitVec w) (f : Flags) :
    locWrite (js.setFlags f) next w D y = (locWrite js next w D y).setFlags f := by
  cases D <;> simp [locWrite, memWrite, regWrite, State.putReg, State.putHigh, State.setReg, State.setFlags, ea, eaOff] <;>
    (try split) <;> rfl

/-- The result and flags of Janus' `execUnary`. -/
def unRes (op : UnOp) {w : Nat} (x : BitVec w) (f : Flags) : BitVec w × Flags :=
  match op with
  | .inc => ((addFlags x 1 false).1, { (addFlags x 1 false).2 with cf := f.cf })
  | .dec => ((subFlags x 1 false).1, { (subFlags x 1 false).2 with cf := f.cf })
  | .not => (~~~x, f)
  | .neg => ((subFlags 0 x false).1, { (subFlags 0 x false).2 with cf := some (decide (x ≠ 0)) })

theorem execUnary_any {js js' : State} {next : BitVec 64} {op : UnOp} {w : Nat} {D : Loc}
    (h : execUnary js next op w D = .ok js') :
    locOK js next w D true ∧
      js' = ((locWrite js next w D (unRes op (locVal js next w D) js.flags).1).setFlags
        (unRes op (locVal js next w D) js.flags).2).setRip next := by
  unfold execUnary at h
  cases hr : readLocRW js next w D with
  | error e => simp [hr] at h
  | ok X =>
    obtain ⟨hok, rfl⟩ := readLocRW_loc hr
    refine ⟨hok, ?_⟩
    simp only [hr, writeLoc_loc hok] at h
    cases op <;> simp only [Except.ok.injEq] at h <;> simp [← h, unRes]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem bits3_zero : (BitVec.ofNat 3 0) = 0b000#3 := rfl

set_option maxHeartbeats 2000000 in
/-- The model's `INC`/`DEC` arm, any r/m operand (abstract read `hX` and write `hWr`). -/
theorem run_inc_dec {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (dec : Bool)
    (opc : Nat) (hopc : opc = 0xFE ∨ opc = 0xFF) {w : Nat} (hw : w = if opc = 0xFE then 8 else osz p)
    (m : Nat) (hm : m < 256) (hreg : m / 8 % 8 = if dec then 1 else 0) (sib : BitVec 8) (tr te : Nat)
    (V : BitVec w) (inc : Nat) (eaddr : BitVec 64) (NX : BitVec 64) (D : Janus.Amd64.Loc)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hWr : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      ∀ js0 s0, Rel js0 s0 → X86Config s0 → js0.regs = js.regs → js0.mem = js.mem → js0.fsBase = js.fsBase →
      ∀ y : BitVec w, ∃ s1,
        (x86_operand_to_reg_mem .Mode_64bit (w / 8) true false ((y.setWidth 64).setWidth 128) sg eaddr x rex
          (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run s0 = .ok () s1 ∧
        Rel (locWrite js0 NX w D y) s1 ∧ X86Config s1 ∧
        s1.regs.get? .rflags = s0.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s0.regs.get? .janus_undef)
    (hte : te = tr + inc) (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ te) (hl2 : te ≤ sr + 15) (htr : te < 2 ^ 47) :
    ∃ s', (x86_inc_dec_fe_ff .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (((locWrite js NX w D (unRes (if dec then .dec else .inc) V js.flags).1).setFlags
        (unRes (if dec then .dec else .inc) V js.flags).2).setRip (BitVec.ofNat 64 te)) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hopc' : opc < 256 := by omega
  have hsz : (if decide (opc % 2 = 0) = true then (1 : Int) else if rexW p = true then 8
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    have := size_int p (decide (opc % 2 = 0)); simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [this, hw]; rcases hopc with rfl | rfl <;> simp
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hinc' : (bits_of_int (inc : Int) 3) = BitVec.ofNat 3 inc := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have hadd : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48)).run s =
      .ok (BitVec.ofNat 48 te) s := by
    have ez : (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48).toNat = inc := by
      simp [Sail.BitVec.zeroExtend]; omega
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hlen := check_len_ok sr te hl1 hl2 htr
  generalize hop : (if dec then Janus.Amd64.AluOp.sub else .add) = op
  have hregop : (if (BitVec.ofNat 3 (m / 8 % 8) == 0b000#3) = true then 0 else 4) = sailOp op := by
    rw [hreg, ← hop]; cases dec <;> rfl
  let c' := (_get_rflagsbits_cf rf == 1#1)
  have hc' : _get_rflagsbits_cf rf = BitVec.ofBool c' := bv1_ofBool _
  have hone : (0x0000000000000001#64 : BitVec 64) = (1 : BitVec w).setWidth 64 := by
    rcases hW with e | e | e | e <;> subst e <;> rfl
  have hspec := run_gpr_arith_logic_spec op hW V 1 rf c' hc' s
  rw [← hone] at hspec
  have hR : aluRes op V 1 c' = ((unRes (if dec then .dec else .inc) V js.flags).1,
      (aluRes op V 1 c').2) := by rw [← hop]; cases dec <;> rfl
  simp only [x86_inc_dec_fe_ff, h1, h2, h3, run_bind, run_select_operand_size hp hrv, byteop8_all opc hopc', hsz,
    hsg, ← bits3_zero, hX sg hsg4 hsg5, hinc', hadd, hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_pure,
    run_readReg hr, trunc128, Int.toNat_natCast, hregop, hspec]
  rw [run_write_user_rflags hr hu hc.log]
  simp only
  generalize hF : (unRes (if dec then .dec else .inc) V js.flags).2 = F
  have hfF : FlagsRel F js.df (wurf rf (_update_rflagsbits_cf (aluOut op rf (aluRes op V 1 c').snd).fst
      (_get_rflagsbits_cf rf)) (aluOut op rf (aluRes op V 1 c').snd).snd u) := by
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := mk0_bits
    rw [← hF]; subst hop
    cases dec <;>
    refine flagsRel_wurf hfr _ _ _ u ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [aluOut, isLogic, aluRes, unRes, outArith, Bool.false_eq_true, ↓reduceIte, m1, m2, m3, m4, m5, m6,
      rf_get_cf_upd_cf, rf_get_cf_upd_pf, rf_get_cf_upd_af, rf_get_cf_upd_zf, rf_get_cf_upd_sf, rf_get_cf_upd_of,
      rf_get_pf_upd_cf, rf_get_pf_upd_pf, rf_get_pf_upd_af, rf_get_pf_upd_zf, rf_get_pf_upd_sf, rf_get_pf_upd_of,
      rf_get_af_upd_cf, rf_get_af_upd_pf, rf_get_af_upd_af, rf_get_af_upd_zf, rf_get_af_upd_sf, rf_get_af_upd_of,
      rf_get_zf_upd_cf, rf_get_zf_upd_pf, rf_get_zf_upd_af, rf_get_zf_upd_zf, rf_get_zf_upd_sf, rf_get_zf_upd_of,
      rf_get_sf_upd_cf, rf_get_sf_upd_pf, rf_get_sf_upd_af, rf_get_sf_upd_zf, rf_get_sf_upd_sf, rf_get_sf_upd_of,
      rf_get_of_upd_cf, rf_get_of_upd_pf, rf_get_of_upd_af, rf_get_of_upd_zf, rf_get_of_upd_sf, rf_get_of_upd_of] <;>
    first | exact flagEq_fbit _ | exact hfr.cf
  have hrel0 := h.setFlagsR F _ hfF
  have hc0 := hc.set (r := .rflags) (by decide) (wurf rf (_update_rflagsbits_cf (aluOut op rf (aluRes op V 1 c').snd).fst
      (_get_rflagsbits_cf rf)) (aluOut op rf (aluRes op V 1 c').snd).snd u)
  obtain ⟨s1, hs1, hrel1, hcfg1, -, -⟩ := hWr sg hsg4 hsg5 _ _ hrel0 hc0 rfl rfl rfl (aluRes op V 1 c').1
  simp only [Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, hs1]
  refine ⟨_, run_write_iptr hcfg1.log _ htr, ?_, (hcfg1.set (by decide) _)⟩
  have := hrel1.setRipR (BitVec.ofNat 64 te)
  rw [locWrite_setFlags, hR] at this
  exact this

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem not_trunc {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (V : BitVec w) :
    sail_mask 64 (trunc (w / 8) (~~~((V.setWidth 64).setWidth 128))) = (~~~V).setWidth 64 := by
  rcases hW with rfl | rfl | rfl | rfl <;>
  apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
  simp [sail_mask, trunc, Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Sail.BitVec.length, BitVec.getLsbD_setWidth] <;>
  omega

theorem neg_cf {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (V : BitVec w) :
    (if (0x00000000000000000000000000000000#128 == (V.setWidth 64).setWidth 128) = true then 0#1 else 1#1) =
      BitVec.ofBool (decide (V ≠ 0)) := by
  by_cases h : V = 0
  · subst h; simp
  · have : ((V.setWidth 64).setWidth 128 : BitVec 128) ≠ 0 := by
      intro e; apply h
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat e
      rcases hW with rfl | rfl | rfl | rfl <;> simp at this <;> simp <;> omega
    have h0 : (0#128 = BitVec.setWidth 128 (BitVec.setWidth 64 V)) = False := eq_false (fun e => this e.symm)
    have h1 : (V = 0#w) = False := eq_false h
    simp [h0, h1]

set_option maxHeartbeats 2000000 in
/-- The model's `NOT`/`NEG` arm, any r/m operand. -/
theorem run_not_neg {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (neg : Bool)
    (opc : Nat) (hopc : opc = 0xF6 ∨ opc = 0xF7) {w : Nat} (hw : w = if opc = 0xF6 then 8 else osz p)
    (m : Nat) (hm : m < 256) (hreg : m / 8 % 8 = if neg then 3 else 2) (sib : BitVec 8) (tr te : Nat)
    (V : BitVec w) (inc : Nat) (eaddr : BitVec 64) (NX : BitVec 64) (D : Janus.Amd64.Loc)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hWr : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      ∀ js0 s0, Rel js0 s0 → X86Config s0 → js0.regs = js.regs → js0.mem = js.mem → js0.fsBase = js.fsBase →
      ∀ y : BitVec w, ∃ s1,
        (x86_operand_to_reg_mem .Mode_64bit (w / 8) true false ((y.setWidth 64).setWidth 128) sg eaddr x rex
          (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run s0 = .ok () s1 ∧
        Rel (locWrite js0 NX w D y) s1 ∧ X86Config s1 ∧
        s1.regs.get? .rflags = s0.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s0.regs.get? .janus_undef)
    (hte : te = tr + inc) (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ te) (hl2 : te ≤ sr + 15) (htr : te < 2 ^ 47) :
    ∃ s', (x86_not_neg_f6_f7 .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (((locWrite js NX w D (unRes (if neg then .neg else .not) V js.flags).1).setFlags
        (unRes (if neg then .neg else .not) V js.flags).2).setRip (BitVec.ofNat 64 te)) s' ∧ X86Config s' := by
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hopc' : opc < 256 := by omega
  have hsz : (if decide (opc % 2 = 0) = true then (1 : Int) else if rexW p = true then 8
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    have := size_int p (decide (opc % 2 = 0)); simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [this, hw]; rcases hopc with rfl | rfl <;> simp
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hinc' : (bits_of_int (inc : Int) 3) = BitVec.ofNat 3 inc := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have hadd : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48)).run s =
      .ok (BitVec.ofNat 48 te) s := by
    have ez : (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48).toNat = inc := by
      simp [Sail.BitVec.zeroExtend]; omega
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hlen := check_len_ok sr te hl1 hl2 htr
  simp only [x86_not_neg_f6_f7, h1, h2, h3, run_bind, run_select_operand_size hp hrv, byteop8_all opc hopc', hsz,
    hsg, ← bits3_zero, hX sg hsg4 hsg5, hinc', hadd, hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_pure,
    run_readReg hr, trunc128, Int.toNat_natCast, hreg]
  cases neg
  · -- NOT: no flags
    simp (config := {decide := true}) only [Bool.false_eq_true, ↓reduceIte, eq_bits_nat, run_pure, not_trunc hW V]
    obtain ⟨s1, hs1, hrel1, hcfg1, -, -⟩ := hWr sg hsg4 hsg5 _ _ h hc rfl rfl rfl (~~~V)
    simp only [Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, hs1]
    refine ⟨_, run_write_iptr hcfg1.log _ htr, ?_, (hcfg1.set (by decide) _)⟩
    have := hrel1.setRipR (BitVec.ofNat 64 te)
    simp only [unRes, show ∀ j : Janus.Amd64.State, j.setFlags js.flags = j → True from fun _ _ => trivial]
    rwa [show (locWrite js NX w D (~~~V)).setFlags js.flags = locWrite js NX w D (~~~V) by
      rw [← locWrite_setFlags]; congr 1]
  · -- NEG
    simp (config := {decide := true}) only [↓reduceIte, eq_bits_nat, run_pure]
    let c' := (_get_rflagsbits_cf rf == 1#1)
    have hc' : _get_rflagsbits_cf rf = BitVec.ofBool c' := bv1_ofBool _
    have hspec := run_gpr_arith_logic_spec .sub hW 0 V rf c' hc' s
    rw [show ((0 : BitVec w).setWidth 64) = 0x0000000000000000#64 by simp] at hspec
    simp only [sailOp] at hspec
    simp only [hspec, neg_cf hW V]
    rw [run_write_user_rflags hr hu hc.log]
    simp only
    generalize hF : (unRes .neg V js.flags).2 = F
    have hfF : FlagsRel F js.df (wurf rf (_update_rflagsbits_cf (aluOut .sub rf (aluRes .sub 0 V c').snd).fst
        (BitVec.ofBool (decide (V ≠ 0)))) (aluOut .sub rf (aluRes .sub 0 V c').snd).snd u) := by
      obtain ⟨m1, m2, m3, m4, m5, m6⟩ := mk0_bits
      rw [← hF]
      refine flagsRel_wurf hfr _ _ _ u ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [aluOut, isLogic, aluRes, unRes, outArith, Bool.false_eq_true, ↓reduceIte, m1, m2, m3, m4, m5, m6,
        rf_get_cf_upd_cf, rf_get_cf_upd_pf, rf_get_cf_upd_af, rf_get_cf_upd_zf, rf_get_cf_upd_sf, rf_get_cf_upd_of,
        rf_get_pf_upd_cf, rf_get_pf_upd_pf, rf_get_pf_upd_af, rf_get_pf_upd_zf, rf_get_pf_upd_sf, rf_get_pf_upd_of,
        rf_get_af_upd_cf, rf_get_af_upd_pf, rf_get_af_upd_af, rf_get_af_upd_zf, rf_get_af_upd_sf, rf_get_af_upd_of,
        rf_get_zf_upd_cf, rf_get_zf_upd_pf, rf_get_zf_upd_af, rf_get_zf_upd_zf, rf_get_zf_upd_sf, rf_get_zf_upd_of,
        rf_get_sf_upd_cf, rf_get_sf_upd_pf, rf_get_sf_upd_af, rf_get_sf_upd_zf, rf_get_sf_upd_sf, rf_get_sf_upd_of,
        rf_get_of_upd_cf, rf_get_of_upd_pf, rf_get_of_upd_af, rf_get_of_upd_zf, rf_get_of_upd_sf, rf_get_of_upd_of] <;>
      first | exact flagEq_fbit _ | (intro v hv; cases hv; rfl)
    have hrel0 := h.setFlagsR F _ hfF
    have hc0 := hc.set (r := .rflags) (by decide) (wurf rf (_update_rflagsbits_cf (aluOut .sub rf (aluRes .sub 0 V c').snd).fst
        (BitVec.ofBool (decide (V ≠ 0)))) (aluOut .sub rf (aluRes .sub 0 V c').snd).snd u)
    obtain ⟨s1, hs1, hrel1, hcfg1, -, -⟩ := hWr sg hsg4 hsg5 _ _ hrel0 hc0 rfl rfl rfl (aluRes .sub 0 V c').1
    simp only [Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, hs1]
    refine ⟨_, run_write_iptr hcfg1.log _ htr, ?_, (hcfg1.set (by decide) _)⟩
    have := hrel1.setRipR (BitVec.ofNat 64 te)
    rw [locWrite_setFlags] at this
    exact this

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

def unOpOf (e : Nat) : Janus.Amd64.UnOp :=
  if e = 0 then .inc else if e = 1 then .dec else if e = 2 then .not else .neg

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_un {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (ho : ((o = 0xFE ∨ o = 0xFF) ∧ m / 8 % 8 < 2) ∨ ((o = 0xF6 ∨ o = 0xF7) ∧ (m / 8 % 8 = 2 ∨ m / 8 % 8 = 3)))
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c)) (hlk : p.lock = false)
    {w : Nat} (hw : w = if o = 0xFE ∨ o = 0xF6 then 8 else osz p)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.rep = 0 ∧ p.fs = false ∧ len = n + 1 + c ∧ len ≤ 15 ∧ i = .unary (unOpOf (m / 8 % 8)) w (rmDst p w mm.rm) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp, hlk, Bool.false_eq_true] at hd
  have hex := modrm_ext hmd
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have ho8 : (osz p = 8) = False := by rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hex; subst hex
  generalize he : m / 8 % 8 = e at ho hd ⊢
  rcases ho with ⟨rfl | rfl, he2⟩ | ⟨rfl | rfl, rfl | rfl⟩
  all_goals
    (try (have he' : e = 0 ∨ e = 1 := by omega
          rcases he' with rfl | rfl))
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, true_and, and_true,
      false_and, and_false, or_false, false_or, ho8, finish, he] at hd hw ⊢
    subst hw
    by_cases hl : 15 < n + 1 + c <;> by_cases hrp : p.rep = 0 <;>
      cases hf : p.fs <;> cases rm <;> simp (config := {decide := true}) [hf, hl, hrp, ho8, rmDst, rmLoc, regLocOf,
        unOpOf] at hd ⊢ <;> (try simp [withFS] at hd ⊢)
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; simp; omega)
      | omega

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_inc_dec (opc : Nat) (hopc : opc = 0xFE ∨ opc = 0xFF) (e : Nat) (he : e = 0 ∨ e = 1)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hm : _get_modr_m_reg m = BitVec.ofNat 3 e) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_inc_dec_fe_ff .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases he with rfl | rfl <;> rcases hopc with rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, hm, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxRecDepth 100000 in
theorem run_one_byte_not_neg (opc : Nat) (hopc : opc = 0xF6 ∨ opc = 0xF7) (e : Nat) (he : e = 2 ∨ e = 3)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hm : _get_modr_m_reg m = BitVec.ofNat 3 e) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_not_neg_f6_f7 .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases he with rfl | rfl <;> rcases hopc with rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, hm, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

theorem modrmP1_un : ∀ o, (o = 0xFE ∨ o = 0xFF ∨ o = 0xF6 ∨ o = 0xF7) → modrmP1 o = true := by
  intro o h; rcases h with rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **INC/DEC r/m** (`FE/FF /0,/1`) and **NOT/NEG r/m** (`F6/F7 /2,/3`): every ModRM form, every
width and prefix sequence Janus accepts without `LOCK`. -/
theorem unary_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (ho : ((o = 0xFE ∨ o = 0xFF) ∧ m / 8 % 8 < 2) ∨ ((o = 0xF6 ∨ o = 0xF7) ∧ (m / 8 % 8 = 2 ∨ m / 8 % 8 = 3)))
    (hlk : p.lock = false)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  cases hmd : modrm (p.rex.getD 0) (m :: rest) with
  | none =>
    exfalso
    obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
    simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
    rcases ho with ⟨rfl | rfl, -⟩ | ⟨rfl | rfl, -⟩ <;> simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  generalize hw : (if o = 0xFE ∨ o = 0xF6 then 8 else osz p) = w
  obtain ⟨hrep, hfs, rfl, hlen, rfl⟩ := decode_un hpp ho hmd hlk hw.symm hd
  rw [step_of_decode hd] at hstep
  simp only [exec] at hstep
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [← hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have ho4 : o = 0xFE ∨ o = 0xFF ∨ o = 0xF6 ∨ o = 0xF7 := by omega
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + 0) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  rw [hnext] at hstep
  obtain ⟨hok, rfl⟩ := execUnary_any hstep
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hfld := (modrm_fields m hm256).2.1
  by_cases hid : o = 0xFE ∨ o = 0xFF
  · have he : m / 8 % 8 = 0 ∨ m / 8 % 8 = 1 := by omega
    have hop : unOpOf (m / 8 % 8) = (if decide (m / 8 % 8 = 1) then .dec else .inc) := by
      rcases he with h | h <;> simp [h, unOpOf]
    rw [hop]
    refine rm_frame hrel hcfg hcode hlim hpp (by unfold prefixGroup; omega) (by omega) (by omega)
      (modrmP1_un o ho4) hlk hmd (fun _ _ => hfs) hW (k := 0) (by decide) (by omega)
      (fun sr tr x rex sib => x86_inc_dec_fe_ff .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
      (fun x rex _ hl sr tr sib => run_one_byte_inc_dec o hid (m / 8 % 8) he sr tr x hl rex _ sib hfld s) ?_
    intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr _ _ _
    obtain ⟨s', hs', hrel', hc'⟩ := run_inc_dec hrel hcfg hpr hrv (decide (m / 8 % 8 = 1)) o hid
      (by rw [← hw]; rcases hid with rfl | rfl <;> simp) m hm256
      (by rcases he with h | h <;> simp [h]) sib tr
      (tr + inc) (locVal js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + 0)) w (rmDst p w mm.rm)) inc eaddr _ _
      (hX true false true hok) (fun sg h4 h5 => hWr true false sg h4 h5 hok) rfl hinc8 js.rip.toNat (by omega) (by omega)
      (by omega)
    refine ⟨s', hs', ?_, hc'⟩
    rwa [hinc', show js.rip.toNat + n + 1 + c = js.rip.toNat + n + 1 + c + 0 from rfl] at hrel'
  · have hnn : o = 0xF6 ∨ o = 0xF7 := by omega
    have he : m / 8 % 8 = 2 ∨ m / 8 % 8 = 3 := by omega
    have hop : unOpOf (m / 8 % 8) = (if decide (m / 8 % 8 = 3) then .neg else .not) := by
      rcases he with h | h <;> simp [h, unOpOf]
    rw [hop]
    refine rm_frame hrel hcfg hcode hlim hpp (by unfold prefixGroup; omega) (by omega) (by omega)
      (modrmP1_un o ho4) hlk hmd (fun _ _ => hfs) hW (k := 0) (by decide) (by omega)
      (fun sr tr x rex sib => x86_not_neg_f6_f7 .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
      (fun x rex _ hl sr tr sib => run_one_byte_not_neg o hnn (m / 8 % 8) he sr tr x hl rex _ sib hfld s) ?_
    intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr _ _ _
    obtain ⟨s', hs', hrel', hc'⟩ := run_not_neg hrel hcfg hpr hrv (decide (m / 8 % 8 = 3)) o hnn
      (by rw [← hw]; rcases hnn with rfl | rfl <;> simp) m hm256
      (by rcases he with h | h <;> simp [h]) sib tr
      (tr + inc) (locVal js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + 0)) w (rmDst p w mm.rm)) inc eaddr _ _
      (hX true false true hok) (fun sg h4 h5 => hWr true false sg h4 h5 hok) rfl hinc8 js.rip.toNat (by omega) (by omega)
      (by omega)
    refine ⟨s', hs', ?_, hc'⟩
    rwa [hinc', show js.rip.toNat + n + 1 + c = js.rip.toNat + n + 1 + c + 0 from rfl] at hrel'

end JanusX86.Proofs
