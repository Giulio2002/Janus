import JanusX86.Proofs.Imul1
import JanusX86.Proofs.TwoByte

/-! # IMUL r, r/m (`0F AF`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_two_byte_imul_af (sr tr : BitVec 48) (x : BitVec 52) (mp : BitVec 8) (hl : _get_prefixes_lck x = 0#8)
    (rex m sib : BitVec 8) (s : SState) :
    (two_byte_opcode_execute .Mode_64bit sr tr x mp rex (BitVec.ofNat 8 0xAF) m sib).run s =
      (x86_imul_op_en_rm .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xAF) m sib).run s := by
  simp (config := {decide := true}) only [two_byte_opcode_execute, ext_two_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

theorem run_mflags {u : Nat} (t : SState) (rt : BitVec 32)
    (hrt : t.regs.get? .rflags = some rt) (hut : t.regs.get? .janus_undef = some u) (c : BitVec 1) :
    (do
      let rflags_var ← readReg Register.rflags
      writeReg Register.rflags (_update_rflagsbits_cf rflags_var c)
      let rflags_var ← readReg Register.rflags
      let sailval ← undef_flg ()
      writeReg Register.rflags (_update_rflagsbits_pf rflags_var sailval)
      let rflags_var ← readReg Register.rflags
      let sailval ← undef_flg ()
      writeReg Register.rflags (_update_rflagsbits_af rflags_var sailval)
      let rflags_var ← readReg Register.rflags
      let sailval ← undef_flg ()
      writeReg Register.rflags (_update_rflagsbits_zf rflags_var sailval)
      let rflags_var ← readReg Register.rflags
      let sailval ← undef_flg ()
      writeReg Register.rflags (_update_rflagsbits_sf rflags_var sailval)
      let rflags_var ← readReg Register.rflags
      writeReg Register.rflags (_update_rflagsbits_of rflags_var c) : SailM Unit).run t =
      .ok () (t.set .rflags (mfl rt c u)) := by
  have hu' : ∀ v : BitVec 32, (t.set .rflags v).regs.get? .janus_undef = some u := fun v => by
    rw [get?_set_ne _ _ (by decide)]; exact hut
  rw [← set_self hrt]
  simp only [run_bind, run_readReg (get?_set_same _ _ _), run_writeReg, set_set, run_undef_flg (hu' _), mfl]

theorem mul_ofInt {w : Nat} (a b : BitVec w) : a * b = BitVec.ofInt w (b.toInt * a.toInt) := by
  rw [BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt, BitVec.mul_comm]

set_option maxHeartbeats 4000000 in
theorem run_imul_rm {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (V : BitVec (osz p)) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (osz p / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_imul_op_en_rm .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 0xAF)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (((js.putReg (osz p) (regNum p m) (js.getReg (osz p) (regNum p m) * V)).setFlags
        (mulFlags (decide ((js.getReg (osz p) (regNum p m) * V).toInt ≠
          (js.getReg (osz p) (regNum p m)).toInt * V.toInt)))).setRip (BitVec.ofNat 64 (tr + inc))) s' ∧
      X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW3 := osz_cases p
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := Or.inr hW3
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hl := hc.log
  have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) = ((osz p / 8 : Nat) : Int) := by
    unfold osz; cases rexW p <;> cases p.opsize <;> simp
  have hreg : regLocOf p.rex.isSome (osz p) (regNum p m) = .reg (regNum p m) := by
    unfold regLocOf; rw [if_neg (by rcases hW3 with e | e | e <;> omega)]
  have hG := run_rgfi_size h hW _ rex hrex (regNum_lt p m) (regNum_8 p m) (s := s)
  rw [hreg] at hG; simp only [regVal] at hG
  generalize hGv : js.getReg (osz p) (regNum p m) = G at hG ⊢
  have hlow := imul_spec_eq hW V G
  generalize hY : BitVec.ofInt (osz p) (V.toInt * G.toInt) = Y at hlow
  have hwr := run_write_rgfi_size h hl hW _ rex hrex (regNum_lt p m) (regNum_8 p m) Y
  rw [hreg] at hwr
  simp only [x86_imul_op_en_rm, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hsz, hsg, Int.toNat_natCast,
    ← bits3_zero, hX sg hsg4 hsg5, run_add_inc tr inc hinc htr, hlen, is_some, Bool.false_eq_true, ↓reduceIte,
    run_pure, trunc128, nbytes_eq _ hW, show reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 =
      BitVec.ofNat 4 (regNum p m) by rw [hrexb]; exact hidx_reg hrv m, hG, hlow, hwr]
  have hn' := locReg_lt p.rex.isSome (osz p) (regNum p m) (regNum_lt p m)
  rw [hreg] at hn'
  generalize hS1 : setGpr s ((regWrite js (osz p) (Janus.Amd64.Loc.reg (regNum p m)) Y).regs
    (locReg (Janus.Amd64.Loc.reg (regNum p m)))) (locReg (Janus.Amd64.Loc.reg (regNum p m))) = S1
  have hr1 : S1.regs.get? .rflags = some rf := by rw [← hS1, get?_setGpr_of_not s _ hn' rfl]; exact hr
  have hu1 : ∀ v : BitVec 32, (S1.set .rflags v).regs.get? .janus_undef = some u := fun v => by
    rw [get?_set_ne _ _ (by decide), ← hS1, get?_setGpr_of_not s _ hn' rfl]; exact hu
  have hl1 : S1.regs.get? .log_register_writes = some false := by rw [← hS1, get?_setGpr_of_not s _ hn' rfl]; exact hl
  simp only [run_readReg hr1, run_writeReg, run_readReg (get?_set_same _ _ _), set_set, run_undef_flg (hu1 _)]
  have hrel1 := h.writeReg p.rex.isSome (regNum_lt p m) Y
  rw [hreg, hS1] at hrel1
  have hc1 : X86Config S1 := by rw [← hS1]; exact hc.setGpr hn' _
  have hGV : G * V = Y := by rw [mul_ofInt, ← hY]
  rw [hGV, show G.toInt * V.toInt = V.toInt * G.toInt from Int.mul_comm _ _]
  refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl1) _ htr, ?_,
    (hc1.set (by decide) _).set (by decide) _⟩
  have hdf : (regWrite js (osz p) (Janus.Amd64.Loc.reg (regNum p m)) Y).df = js.df := by
    simp only [regWrite, Janus.Amd64.State.putReg]; split <;> rfl
  exact hrel1.flagsRip _ _ (by rw [hdf]; exact flagsRel_mfl hfr _ u) _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem decode_imul_af {bytes : List Nat} {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: 0xAF :: m :: rest, n))
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ len = n + 2 + c ∧ len ≤ 15 ∧
      i = .imul (osz p) (regNum p m) (.reg (regNum p m)) (.loc (rmDst p (osz p) mm.rm)) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hreg : mm.reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have ho8 : (osz p = 8) = False := by rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hreg; subst hreg
  simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, hou, true_and, and_true,
    false_and, and_false, or_false, false_or] at hd ⊢
  by_cases hl : 15 < n + 1 + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
    cases rm <;>
    simp (config := {decide := true}) [hf, hk, hl, hrp, finish, withFS, rmDst, rmLoc, regLocOf, ho8, lockable] at hd ⊢
  all_goals (obtain ⟨rfl, rfl⟩ := hd; first | exact ⟨by omega, rfl⟩ | exact ⟨rfl, by omega, rfl⟩ | omega)

set_option maxRecDepth 100000 in
theorem modrmP2_af {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hr : p.rep = 0) : modrmP2 x 0xAF = true := by
  unfold modrmP2; rw [mpref_norep hp hr]
  cases p.opsize <;> decide

set_option maxHeartbeats 1000000 in
/-- **IMUL r16/32/64, r/m** (`0F AF`): register and memory sources, every width; `CF = OF`. -/
theorem imul2_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: 0xAF :: m :: rest, n))
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
    simp (config := {decide := true}) [twoByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hlk, hfs, hrep, rfl, hlen, rfl⟩ := decode_imul_af hpp hmd hd
  rw [step_of_decode hd] at hstep
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = 0x0F :: 0xAF :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := by rcases osz_cases p with e | e | e <;> simp [e]
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 2 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 2 + c) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  have hrr : ∀ (nx : BitVec 64) (r : Nat), readLoc js nx (osz p) (.reg r) = .ok (js.getReg (osz p) r) := fun _ _ => rfl
  simp only [exec, execImul, hrr, readSrc] at hstep
  rw [hnext] at hstep
  cases hrd : readLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c)) (osz p) (rmDst p (osz p) mm.rm) with
  | error e => simp only [hrd] at hstep; cases hstep
  | ok X =>
  simp only [hrd, Except.ok.injEq] at hstep; subst hstep
  obtain ⟨hok, rfl⟩ := readLoc_loc hrd
  refine rm_frame2 hrel hcfg hcode hlim hpp (fun x rex hpr => modrmP2_af hpr hrep) hlk hmd
    (fun _ _ => hfs) hW (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => x86_imul_op_en_rm .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xAF) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_two_byte_imul_af sr tr x _ hl rex _ sib s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX _ _ _ _
  obtain ⟨s', hs', hrel', hc'⟩ := run_imul_rm hrel hcfg hpr hrv m hm256 sib tr _ inc eaddr
    (hX true false false hok) hinc8 js.rip.toNat (by omega) (by omega) (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  rw [hinc'] at hrel'
  exact hrel'

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_imul3 (opc : Nat) (hopc : opc = 0x69 ∨ opc = 0x6B)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_imul_op_en_rmi .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases hopc with rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

theorem imm_sx (K w : Nat) (hK : K = 1 ∨ K = 2 ∨ K = 4) (hw : w = 16 ∨ w = 32 ∨ w = 64) (hKw : 8 * K ≤ w)
    (v : Nat) (hv : v < 2 ^ (8 * K)) :
    Sail.BitVec.truncate (Sail.BitVec.signExtend (Sail.BitVec.truncate
      (Sail.BitVec.signExtend (BitVec.ofNat (8 * K) v) 64) 32) 64) w =
      BitVec.ofNat w (Janus.Amd64.Decode.sext (8 * K) w v) := by
  apply BitVec.eq_of_toNat_eq
  rcases hK with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> (try omega) <;>
  simp only [Sail.BitVec.truncate, Sail.BitVec.signExtend, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_signExtend, BitVec.msb_eq_decide, BitVec.toNat_ofNat, Janus.Amd64.Decode.sext] <;>
  simp at hv ⊢ <;> split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem imul_src {w : Nat} (hW : w = 16 ∨ w = 32 ∨ w = 64) (a b : BitVec 64) :
    imul_spec (w / 8) a b = imul_spec (w / 8) a ((Sail.BitVec.truncate b w).setWidth 64) := by
  have e : ∀ k, k ≤ 64 → Sail.BitVec.truncate ((Sail.BitVec.truncate b k).setWidth 64) k = Sail.BitVec.truncate b k := by
    intro k hk; apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.truncate, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hk)]; simp
  rcases hW with rfl | rfl | rfl
  · simp only [imul_spec, Nat.reduceDiv, e 16 (by decide)]
  · simp only [imul_spec, Nat.reduceDiv, e 32 (by decide)]
  · simp only [imul_spec, Nat.reduceDiv]
    rw [show (Sail.BitVec.truncate b 64).setWidth 64 = b by apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate]]

/-- The immediate bytes of `IMUL r, r/m, imm` (`6B`: 1; `69`: 2 at 16 bits, else 4). -/
def imK (o w : Nat) : Nat := if o = 0x6B then 1 else if w = 16 then 2 else 4

set_option maxHeartbeats 4000000 in
theorem run_imul_rmi {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (opc : Nat) (hopc : opc = 0x69 ∨ opc = 0x6B)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr te : Nat) (V : BitVec (osz p)) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (osz p / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 (imK opc (osz p)))).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hte : te = tr + inc) (hinc : inc < 8) {ds : List Nat} (hds : CodeAt s te ds) {v : Nat} {r : List Nat}
    (hle : Janus.Amd64.Decode.readLE (imK opc (osz p)) ds = some (v, r))
    (sr : Nat) (hl1 : sr ≤ te + imK opc (osz p)) (hl2 : te + imK opc (osz p) ≤ sr + 15)
    (htr : te + imK opc (osz p) < 2 ^ 47) :
    ∃ s', (x86_imul_op_en_rmi .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (((js.putReg (osz p) (regNum p m)
          (V * BitVec.ofNat (osz p) (Janus.Amd64.Decode.sext (8 * imK opc (osz p)) (osz p) v))).setFlags
        (mulFlags (decide ((V * BitVec.ofNat (osz p) (Janus.Amd64.Decode.sext (8 * imK opc (osz p)) (osz p) v)).toInt ≠
          V.toInt * (BitVec.ofNat (osz p) (Janus.Amd64.Decode.sext (8 * imK opc (osz p)) (osz p) v)).toInt)))).setRip
        (BitVec.ofNat 64 (te + imK opc (osz p)))) s' ∧
      X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW3 := osz_cases p
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := Or.inr hW3
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hl := hc.log
  have hrip := h.rip
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  generalize hK : imK opc (osz p) = K at hX hle hl1 hl2 htr ⊢
  have hK4 : K = 1 ∨ K = 2 ∨ K = 4 := by rw [← hK]; unfold imK; split <;> (try split) <;> simp
  have hlen := check_len_ok sr (te + K) hl1 hl2 htr
  have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) = ((osz p / 8 : Nat) : Int) := by
    unfold osz; cases rexW p <;> cases p.opsize <;> simp
  have himm : (if (BitVec.ofNat 8 opc == 0x6B#8) = true then (1 : Int)
      else if (((osz p / 8 : Nat) : Int) == 2) = true then 2 else 4) = ((K : Nat) : Int) := by
    rw [← hK]; unfold imK
    rcases hopc with rfl | rfl <;> rcases hW3 with e | e | e <;> rw [e] <;> decide
  have hk3 : bits_of_int ((K : Nat) : Int) 3 = BitVec.ofNat 3 K := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  simp only [x86_imul_op_en_rmi, h1, h2, h3, run_bind, run_select_operand_size hp hrv, Bool.false_eq_true,
    ↓reduceIte, hsz, himm, hk3, hsg,
    Int.toNat_natCast, hX sg hsg4 hsg5, run_add_inc tr inc hinc (by omega), hsel, show (8 : Int).toNat = 8 from rfl]
  obtain ⟨-, hvv, -⟩ := readLE_sumLE _ ds hle
  have hvl : v < 2 ^ (8 * K) := by
    rw [hvv, Nat.pow_mul]
    exact sumLE_lt _ (fun j => by
      by_cases hj : j < ds.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hds.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
  subst hte
  have hrime : (rime_size .Mode_64bit 8 K (Sail.BitVec.signExtend (BitVec.ofNat 48 (tr + inc)) 64) none 1 ":X"
      false false).run s = .ok (Sail.BitVec.signExtend (BitVec.ofNat (8 * K) v) 64) s := by
    simp only [rime_size, run_bind, run_load_code hc hrip 8 hds (by omega) hle (by omega), run_pure]
  have hadd2 : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 (tr + inc)) (bits_of_int ((K : Nat) : Int) 48)).run s =
      .ok (BitVec.ofNat 48 (tr + inc + K)) s := by
    have ez : (bits_of_int ((K : Nat) : Int) 48).toNat = K := by
      rw [bits_of_int_natCast_toNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hW' : osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := hW3
  have hKw : 8 * K ≤ osz p := by
    rw [← hK]; unfold imK; rcases hopc with rfl | rfl <;> rcases hW3 with e | e | e <;> rw [e] <;> decide
  have hsx := imm_sx K (osz p) hK4 hW' hKw v hvl
  generalize hYd : BitVec.ofNat (osz p) (Janus.Amd64.Decode.sext (8 * K) (osz p) v) = Y at hsx ⊢
  have hspec : imul_spec (osz p / 8) (V.setWidth 64) (Sail.BitVec.signExtend (Sail.BitVec.truncate
      (Sail.BitVec.signExtend (BitVec.ofNat (8 * K) v) 64) 32) 64) = imul_spec (osz p / 8) (V.setWidth 64) (Y.setWidth 64) := by
    rw [imul_src hW', hsx]
  have hlow := imul_spec_eq hW V Y
  generalize hYY : BitVec.ofInt (osz p) (V.toInt * Y.toInt) = Z at hlow
  have hreg : regLocOf p.rex.isSome (osz p) (regNum p m) = .reg (regNum p m) := by
    unfold regLocOf; rw [if_neg (by rcases hW3 with e | e | e <;> omega)]
  have hwr := run_write_rgfi_size h hl hW _ rex hrex (regNum_lt p m) (regNum_8 p m) Z
  rw [hreg] at hwr
  simp only [hrime, run_pure, hadd2, hlen, is_some, Bool.false_eq_true, ↓reduceIte, trunc128, hspec, hlow,
    nbytes_eq _ hW, show reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 =
      BitVec.ofNat 4 (regNum p m) by rw [hrexb]; exact hidx_reg hrv m, hwr]
  have hn' := locReg_lt p.rex.isSome (osz p) (regNum p m) (regNum_lt p m)
  rw [hreg] at hn'
  generalize hS1 : setGpr s ((regWrite js (osz p) (Janus.Amd64.Loc.reg (regNum p m)) Z).regs
    (locReg (Janus.Amd64.Loc.reg (regNum p m)))) (locReg (Janus.Amd64.Loc.reg (regNum p m))) = S1
  have hr1 : S1.regs.get? .rflags = some rf := by rw [← hS1, get?_setGpr_of_not s _ hn' rfl]; exact hr
  have hu1 : ∀ v : BitVec 32, (S1.set .rflags v).regs.get? .janus_undef = some u := fun v => by
    rw [get?_set_ne _ _ (by decide), ← hS1, get?_setGpr_of_not s _ hn' rfl]; exact hu
  have hl1 : S1.regs.get? .log_register_writes = some false := by rw [← hS1, get?_setGpr_of_not s _ hn' rfl]; exact hl
  simp only [run_readReg hr1, run_writeReg, run_readReg (get?_set_same _ _ _), set_set, run_undef_flg (hu1 _)]
  have hrel1 := h.writeReg p.rex.isSome (regNum_lt p m) Z
  rw [hreg, hS1] at hrel1
  have hc1 : X86Config S1 := by rw [← hS1]; exact hc.setGpr hn' _
  have hGV : V * Y = Z := by rw [mul_ofInt, ← hYY, Int.mul_comm]
  rw [hGV]
  refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hl1) _ htr, ?_,
    (hc1.set (by decide) _).set (by decide) _⟩
  have hdf : (regWrite js (osz p) (Janus.Amd64.Loc.reg (regNum p m)) Z).df = js.df := by
    simp only [regWrite, Janus.Amd64.State.putReg]; split <;> rfl
  exact hrel1.flagsRip _ _ (by rw [hdf]; exact flagsRel_mfl hfr _ u) _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

/-- Janus' immediate of `IMUL r, r/m, imm`. -/
def immIM (o w v : Nat) : Nat := if o = 0x6B then sext 8 w v else if w = 64 then sext 32 64 v else v

theorem decode_imul3 {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o = 0x69 ∨ o = 0x6B)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ ∃ v r4, readLE (imK o (osz p)) r3 = some (v, r4) ∧
      len = n + 1 + c + imK o (osz p) ∧ len ≤ 15 ∧
      i = .imul (osz p) (regNum p m) (rmDst p (osz p) mm.rm) (.imm (immIM o (osz p) v)) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hreg : mm.reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have ho8 : (osz p = 8) = False := by rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hreg; subst hreg
  have hW3 := osz_cases p
  rcases ho with rfl | rfl
  · have hk : imK 0x69 (osz p) = (if osz p = 16 then 2 else 4) := by simp [imK]
    rw [hk]
    cases hr : readLE (if osz p = 16 then 2 else 4) r3 with
    | none => simp (config := {decide := true}) [oneByte, hmd, hou, immZ, ho8, hr] at hd
    | some vr =>
      obtain ⟨v, r4⟩ := vr
      simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, immZ, ho8, hr, true_and, and_true,
        false_and, and_false, or_false, false_or] at hd ⊢
      by_cases hl : 15 < n + 1 + c + (if osz p = 16 then 2 else 4) <;> by_cases hrp : p.rep = 0 <;>
        cases hf : p.fs <;> cases hkk : p.lock <;> cases rm <;>
        simp (config := {decide := true}) [hf, hkk, hl, hrp, finish, withFS, rmDst, rmLoc, regLocOf, ho8, lockable,
          immIM] at hd ⊢
      all_goals (obtain ⟨rfl, rfl⟩ := hd; first | exact ⟨by omega, rfl⟩ | exact ⟨rfl, by omega, rfl⟩ | omega)
  · have hk : imK 0x6B (osz p) = 1 := by simp [imK]
    rw [hk]
    cases hr : readLE 1 r3 with
    | none => simp (config := {decide := true}) [oneByte, hmd, hou, immB, hr] at hd
    | some vr =>
      obtain ⟨v, r4⟩ := vr
      simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, immB, hr, true_and, and_true,
        false_and, and_false, or_false, false_or] at hd ⊢
      by_cases hl : 15 < n + 1 + c + 1 <;> by_cases hrp : p.rep = 0 <;>
        cases hf : p.fs <;> cases hkk : p.lock <;> cases rm <;>
        simp (config := {decide := true}) [hf, hkk, hl, hrp, finish, withFS, rmDst, rmLoc, regLocOf, ho8, lockable,
          immIM] at hd ⊢
      all_goals (obtain ⟨rfl, rfl⟩ := hd; first | exact ⟨by omega, rfl⟩ | exact ⟨rfl, by omega, rfl⟩ | omega)

theorem immIM_eq (o w v : Nat) (ho : o = 0x69 ∨ o = 0x6B) (hW : w = 16 ∨ w = 32 ∨ w = 64) :
    BitVec.ofNat w (immIM o w v) = BitVec.ofNat w (sext (8 * imK o w) w v) := by
  rcases ho with rfl | rfl <;> rcases hW with rfl | rfl | rfl <;> simp [immIM, imK, sext] <;> (try split) <;> simp <;> omega

theorem modrmP1_imul3 : ∀ o, (o = 0x69 ∨ o = 0x6B) → modrmP1 o = true := by
  intro o h; rcases h with rfl | rfl <;> decide

set_option maxHeartbeats 1000000 in
/-- **IMUL r16/32/64, r/m, imm** (`69` imm16/32, `6B` imm8): register and memory sources, every width. -/
theorem imul3_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o = 0x69 ∨ o = 0x6B)
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
  obtain ⟨hlk, hfs, hrep, v, r4, hr4, rfl, hlen, rfl⟩ := decode_imul3 hpp ho hmd hd
  rw [step_of_decode hd] at hstep
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := by rcases osz_cases p with e | e | e <;> simp [e]
  have hK8 : imK o (osz p) < 8 := by unfold imK; split <;> (try split) <;> omega
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c + imK o (osz p))) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + imK o (osz p)) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  simp only [exec, execImul, readSrc] at hstep
  rw [hnext] at hstep
  cases hrd : readLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + imK o (osz p))) (osz p) (rmDst p (osz p) mm.rm) with
  | error e => simp only [hrd] at hstep; cases hstep
  | ok X =>
  simp only [hrd, Except.ok.injEq] at hstep; subst hstep
  obtain ⟨hok, rfl⟩ := readLoc_loc hrd
  rw [immIM_eq o (osz p) v ho (osz_cases p)]
  refine rm_frame hrel hcfg hcode hlim hpp (by unfold prefixGroup; rcases ho with rfl | rfl <;> decide) (by omega)
    (by omega) (modrmP1_imul3 o ho) hlk hmd (fun _ _ => hfs) hW (k := imK o (osz p)) hK8 (by omega)
    (fun sr tr x rex sib => x86_imul_op_en_rmi .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_one_byte_imul3 o ho sr tr x hl rex _ sib s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 hc3 hX _ _ _ _
  obtain ⟨s', hs', hrel', hc'⟩ := run_imul_rmi hrel hcfg hpr hrv o ho m hm256 sib tr (tr + inc) _ inc eaddr
    (hX true false false hok) rfl hinc8 (by rw [hinc']; exact hc3) hr4 js.rip.toNat (by omega) (by omega) (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  rw [hinc'] at hrel'
  exact hrel'

end JanusX86.Proofs
