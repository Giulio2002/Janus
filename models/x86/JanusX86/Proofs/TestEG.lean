import JanusX86.Proofs.Mov

/-! # TEST r/m, r (`84/85`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxHeartbeats 2000000 in
theorem run_test_e_g {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0x84 ∨ opc = 0x85) {w : Nat} (hw : w = if opc % 2 = 0 then 8 else osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (V : BitVec w) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g 7 .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex
      (BitVec.ofNat 8 opc) (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((js.setFlags (Janus.Amd64.logicFlags (V &&& regVal js w (regLocOf p.rex.isSome w (regNum p m))))).setRip
        (BitVec.ofNat 64 (tr + inc))) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  have hopc' : opc < 256 := by omega
  have hsz : (if decide (opc % 2 = 0) = true then (1 : Int) else if rexW p = true then 8
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := size_w rfl hw
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  let c' := (_get_rflagsbits_cf rf == 1#1)
  have hc' : _get_rflagsbits_cf rf = BitVec.ofBool c' := bv1_ofBool _
  have hspec := run_gpr_arith_logic_spec .and hW V (regVal js w (regLocOf p.rex.isSome w (regNum p m))) rf c' hc' s
  simp only [sailOp] at hspec
  rw [← spec7 _ (by rcases hW with e | e | e | e <;> subst e <;> simp)] at hspec
  simp only [x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g, h1, h2, h3, run_bind, run_select_operand_size hp hrv,
    byteop_all opc hopc', hsz, nbytes_eq w hW, show reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 =
      BitVec.ofNat 4 (regNum p m) by rw [hrexb]; exact hidx_reg hrv m,
    run_rgfi_size h hW _ rex hrex (regNum_lt p m) (regNum_8 p m), hsg, ← bits3_zero, hX sg hsg4 hsg5,
    run_add_inc tr inc hinc htr, hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_pure, run_readReg hr, trunc128,
    Int.toNat_natCast, hspec, show ((7 : Nat) == 8 || (7 : Nat) == 7) = true from rfl,
    run_write_user_rflags hr hu hc.log]
  refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hc.log) _ htr, ?_,
    (hc.set (by decide) _).set (by decide) _⟩
  exact h.flagsRip _ _ (flagsRel_aluOut hfr .and _ _ c' u) _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem withFS_test_rr (w : Nat) (b : Bool) (n n' : Nat) :
    withFS (.test w (regLocOf b w n) (.loc (regLocOf b w n'))) = none := by
  rcases regLocOf_cases b w n with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] <;>
  rcases regLocOf_cases b w n' with ⟨r', e'⟩ | ⟨r', e'⟩ <;> rw [e'] <;> rfl

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_test {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o = 0x84 ∨ o = 0x85)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {w : Nat} (hw : w = if o % 2 = 0 then 8 else osz p)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.rep = 0 ∧ len = n + 1 + c ∧ len ≤ 15 ∧
      i = .test w (rmDst p w mm.rm) (.loc (regLocOf p.rex.isSome w (regNum p m))) ∧
      (∀ k', mm.rm = .r k' → p.fs = false) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hreg : mm.reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have ho8 : (osz p = 8) = False := by rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hreg; subst hreg
  rcases ho with rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, true_and, and_true,
      false_and, and_false, or_false, false_or, finish] at hd hw ⊢
    subst hw
    by_cases hl : 15 < n + 1 + c <;> by_cases hrp : p.rep = 0 <;>
      cases hf : p.fs <;> cases hk : p.lock <;> cases rm <;>
      simp (config := {decide := true}) only [hf, hk, hl, hrp, rmDst_r, rmDst_m, rmLoc_r, rmLoc_m, regLoc_eq,
        withFS_test_rr, ↓reduceIte, Bool.false_eq_true, ho8] at hd ⊢ <;>
      (try simp [withFS, lockable] at hd ⊢)
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, rfl, fun _ h => by cases h⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; simp; omega)
      | omega

set_option maxRecDepth 100000 in
theorem run_one_byte_test (opc : Nat) (hopc : opc = 0x84 ∨ opc = 0x85)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g 7 .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases hopc with rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **TEST r/m, r** (`84/85`): every ModRM form (incl. FS-relative), width and prefix sequence. -/
theorem test_eg_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o = 0x84 ∨ o = 0x85)
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
    rcases ho with rfl | rfl <;> simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  generalize hw : (if o % 2 = 0 then 8 else osz p) = w
  obtain ⟨hlk, hrep, rfl, hlen, rfl, hfs⟩ := decode_test hpp ho hmd hw.symm hd
  rw [step_of_decode hd] at hstep
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [← hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  refine rm_frame hrel hcfg hcode hlim hpp (by unfold prefixGroup; omega) (by omega) (by omega)
    (by rcases ho with rfl | rfl <;> decide) hlk hmd hfs hW (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g 7 .Mode_64bit sr tr x rex (BitVec.ofNat 8 o)
      (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_one_byte_test o ho sr tr x hl rex _ sib s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr _ _ _
  simp only [exec] at hstep
  rw [hnext] at hstep
  cases hrd : readLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c)) w (rmDst p w mm.rm) with
  | error e => simp [hrd] at hstep
  | ok X =>
    obtain ⟨hok, rfl⟩ := readLoc_loc hrd
    simp only [hrd, readSrc, readLoc_regLocOf, Except.ok.injEq] at hstep
    subst hstep
    obtain ⟨s', hs', hrel', hc'⟩ := run_test_e_g hrel hcfg hpr hrv o ho hw.symm m hm256 sib tr _ inc eaddr
      (hX true false false hok) hinc8 js.rip.toNat (by omega) (by omega) (by omega)
    refine ⟨s', hs', ?_, hc'⟩
    rwa [hinc'] at hrel'

end JanusX86.Proofs
