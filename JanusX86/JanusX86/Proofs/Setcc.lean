import JanusX86.Proofs.Movx

/-! # SETcc (`0F 90–9F`) and CMOVcc (`0F 40–4F`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem setcc_val (b : Bool) :
    bits_of_int (if b = true then (1 : Int) else 0) 128 =
      ((BitVec.ofNat 8 (if b then 1 else 0)).setWidth 64).setWidth 128 := by
  cases b <;> decide

set_option maxHeartbeats 2000000 in
theorem run_setcc {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (opc : Nat) (ho : opc < 256) {b : Bool} (hcond : Janus.Amd64.condition (opc % 16) js.flags = some b)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (inc : Nat) (eaddr : BitVec 64)
    (NX : BitVec 64) (D : Janus.Amd64.Loc)
    (hWr : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      ∀ js0 s0, Rel js0 s0 → X86Config s0 → js0.regs = js.regs → js0.mem = js.mem → js0.fsBase = js.fsBase →
      ∀ y : BitVec 8, ∃ s1,
        (x86_operand_to_reg_mem .Mode_64bit (8 / 8) true false ((y.setWidth 64).setWidth 128) sg eaddr x rex
          (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run s0 = .ok () s1 ∧
        Rel (locWrite js0 NX 8 D y) s1 ∧ X86Config s1 ∧
        s1.regs.get? .rflags = s0.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s0.regs.get? .janus_undef)
    (hEA : m / 64 ≠ 3 → (x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 tr) rex (BitVec.ofNat 3 (m % 8))
        (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s = .ok (eaddr, (inc : Int)) s)
    (hR3 : m / 64 = 3 → inc = 0 ∧ eaddr = 0#64)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_setcc .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((locWrite js NX 8 D (BitVec.ofNat 8 (if b then 1 else 0))).setRip (BitVec.ofNat 64 (tr + inc))) s' ∧
      X86Config s' := by
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hea : (if (BitVec.ofNat 2 (m / 64) == 3#2) = true then (pure ((0x0000000000000000#64 : BitVec 64), (0 : Int)) : SailM _)
      else x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 tr) rex (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64))
        sib 0b000#3).run s = .ok (eaddr, (inc : Int)) s := by
    by_cases h3' : m / 64 = 3
    · obtain ⟨rfl, rfl⟩ := hR3 h3'
      rw [beq2_3 _ (by omega)]; simp [h3']
    · rw [beq2_3 _ (by omega)]; simp only [h3', decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [← bits3_zero]; exact hEA h3'
  simp only [x86_setcc, h1, h2, h3, run_bind, hea, run_add_inc tr inc hinc htr, hlen, is_some, Bool.false_eq_true,
    ↓reduceIte, run_pure, run_jcc_spec hr hfr opc ho hcond, hsg, setcc_val]
  obtain ⟨s1, hs1, hrel1, hcfg1, -, -⟩ := hWr sg hsg4 hsg5 _ _ h hc rfl rfl rfl (BitVec.ofNat 8 (if b then 1 else 0))
  rw [show (1 : Nat) = 8 / 8 from rfl, hs1]
  exact ⟨_, run_write_iptr hcfg1.log _ htr, hrel1.setRipR _, hcfg1.set (by decide) _⟩

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem withFS_setcc (cc : Nat) (d : Loc) : withFS (.setcc cc d) = none := rfl

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_setcc {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n)) (ho : 0x90 ≤ o ∧ o < 0xA0)
    (hext : m / 8 % 8 = 0)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ len = n + 2 + c ∧ len ≤ 15 ∧
      i = .setcc (o % 16) (rmDst p 8 mm.rm) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hex := modrm_ext hmd
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hex; subst hex
  have hcs : o = 0x90 ∨ o = 0x91 ∨ o = 0x92 ∨ o = 0x93 ∨ o = 0x94 ∨ o = 0x95 ∨ o = 0x96 ∨ o = 0x97 ∨
      o = 0x98 ∨ o = 0x99 ∨ o = 0x9A ∨ o = 0x9B ∨ o = 0x9C ∨ o = 0x9D ∨ o = 0x9E ∨ o = 0x9F := by omega
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, true_and, and_true,
      false_and, and_false, or_false, false_or, finish, hext] at hd ⊢
    by_cases hl : 15 < n + 1 + 1 + c <;> by_cases hrp : p.rep = 0 <;>
      cases hf : p.fs <;> cases hk : p.lock <;>
      simp (config := {decide := true}) only [hf, hk, hl, hrp, ↓reduceIte, Bool.false_eq_true, withFS_setcc] at hd ⊢ <;>
      (try simp [lockable] at hd ⊢)
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := hd; refine ⟨by omega, by omega, ?_⟩; cases rm <;> simp_all [rmDst, rmLoc, regLocOf])
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, by cases rm <;> simp_all [rmDst, rmLoc, regLocOf]⟩)
      | (simp at hd; done)
      | (rcases rm with _ | _ <;> simp at hd)

set_option maxRecDepth 100000 in
theorem run_two_byte_setcc (opc : Nat) (hopc : 0x90 ≤ opc ∧ opc < 0xA0)
    (sr tr : BitVec 48) (x : BitVec 52) (mp : BitVec 8) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (s : SState) :
    (two_byte_opcode_execute .Mode_64bit sr tr x mp rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_setcc .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  have hcs : opc = 0x90 ∨ opc = 0x91 ∨ opc = 0x92 ∨ opc = 0x93 ∨ opc = 0x94 ∨ opc = 0x95 ∨ opc = 0x96 ∨ opc = 0x97 ∨
      opc = 0x98 ∨ opc = 0x99 ∨ opc = 0x9A ∨ opc = 0x9B ∨ opc = 0x9C ∨ opc = 0x9D ∨ opc = 0x9E ∨ opc = 0x9F := by omega
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [two_byte_opcode_execute, ext_two_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxRecDepth 100000 in
theorem modrmP2_setcc {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hr : p.rep = 0) (o : Nat) (ho : 0x90 ≤ o ∧ o < 0xA0) : modrmP2 x o = true := by
  unfold modrmP2; rw [mpref_norep hp hr]
  have hcs : o = 0x90 ∨ o = 0x91 ∨ o = 0x92 ∨ o = 0x93 ∨ o = 0x94 ∨ o = 0x95 ∨ o = 0x96 ∨ o = 0x97 ∨
      o = 0x98 ∨ o = 0x99 ∨ o = 0x9A ∨ o = 0x9B ∨ o = 0x9C ∨ o = 0x9D ∨ o = 0x9E ∨ o = 0x9F := by omega
  cases p.opsize <;>
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **SETcc r/m8** (`0F 90–9F /0`): all 16 conditions, register (incl. `AH…BH`) and memory forms. -/
theorem setcc_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n)) (ho : 0x90 ≤ o ∧ o < 0xA0)
    (hext : m / 8 % 8 = 0)
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
    have hcs : o = 0x90 ∨ o = 0x91 ∨ o = 0x92 ∨ o = 0x93 ∨ o = 0x94 ∨ o = 0x95 ∨ o = 0x96 ∨ o = 0x97 ∨
        o = 0x98 ∨ o = 0x99 ∨ o = 0x9A ∨ o = 0x9B ∨ o = 0x9C ∨ o = 0x9D ∨ o = 0x9E ∨ o = 0x9F := by omega
    rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [twoByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hlk, hfs, hrep, rfl, hlen, rfl⟩ := decode_setcc hpp ho hext hmd hd
  rw [step_of_decode hd] at hstep
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = 0x0F :: o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 2 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 2 + c) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  simp only [exec] at hstep
  cases hc : condition (o % 16) js.flags with
  | none => simp [hc] at hstep
  | some b =>
  simp only [hc] at hstep
  rw [hnext] at hstep
  generalize hv : (if b = true then 1#8 else 0#8) = v at hstep
  cases hw : writeLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c)) 8 (rmDst p 8 mm.rm) v with
  | error e => simp [hw] at hstep
  | ok j2 =>
  simp only [hw, Except.ok.injEq] at hstep; subst hstep
  obtain ⟨hok, rfl⟩ := writeLoc_inv hw
  refine rm_frame2 hrel hcfg hcode hlim hpp (fun x rex hpr => modrmP2_setcc hpr hrep o ho) hlk hmd
    (fun _ _ => hfs) (w := 8) (by decide) (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => x86_setcc .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_two_byte_setcc o ho sr tr x _ hl rex _ sib s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr hEA hR3 _
  obtain ⟨s', hs', hrel', hc'⟩ := run_setcc hrel hcfg hpr o (by omega) hc m hm256 sib tr inc eaddr _ _
    (fun sg h4 h5 => hWr true false sg h4 h5 hok) hEA hR3 hinc8 js.rip.toNat (by omega) (by omega) (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  rw [hinc'] at hrel'
  have e : v = BitVec.ofNat 8 (if b then 1 else 0) := by rw [← hv]; cases b <;> rfl
  rw [e]; exact hrel'

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem setReg_self (js : Janus.Amd64.State) (r : Nat) : js.setReg r (js.regs r) = js := by
  cases js; simp only [Janus.Amd64.State.setReg, Janus.Amd64.State.mk.injEq, and_true]
  funext i; split <;> simp_all

theorem putReg_self (js : Janus.Amd64.State) {w : Nat} (hw : w = 16 ∨ w = 64) (r : Nat) :
    js.putReg w r (js.getReg w r) = js := by
  rcases hw with rfl | rfl
  · unfold Janus.Amd64.State.putReg Janus.Amd64.State.getReg
    simp only [show ¬ ((16 : Nat) = 64 ∨ (16 : Nat) = 32) by decide, ↓reduceIte]
    have : ((js.regs r &&& ~~~(BitVec.allOnes 16).setWidth 64) ||| ((js.regs r).setWidth 16).setWidth 64) = js.regs r := by
      have hk : ∀ i < 64, (18446744073709486080#64).getLsbD i = decide (16 ≤ i) := by decide
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [BitVec.getLsbD_setWidth, hk i hi, hi]
      by_cases h : i < 16 <;> simp [h]
      · intro a _; exact a
      · intro _; have := hk i hi; rw [BitVec.getLsbD_eq_getElem hi] at this; rw [this]; simp; omega
    rw [this, setReg_self]
  · unfold Janus.Amd64.State.putReg Janus.Amd64.State.getReg
    simp [setReg_self]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem wr32_eq (idx : BitVec 4) (v : BitVec 32) (rex : BitVec 8) :
    wr32 idx v = write_rgfi_size (BitVec.ofNat 4 (32 / 8)) idx (v.setWidth 64) rex := by
  simp (config := {decide := true}) only [write_rgfi_size, eq_bits_nat, ↓reduceIte, Bool.false_eq_true,
    Sail.BitVec.truncate, sw_sw32]

set_option maxHeartbeats 2000000 in
theorem run_cmovcc {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (ho : opc < 256) {b : Bool} (hcond : Janus.Amd64.condition (opc % 16) js.flags = some b)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (V : BitVec (osz p)) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (osz p / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_cmovcc .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((js.putReg (osz p) (regNum p m) (if b then V else js.getReg (osz p) (regNum p m))).setRip
        (BitVec.ofNat 64 (tr + inc))) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW3 := osz_cases p
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := Or.inr hW3
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hl := hc.log
  have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) = ((osz p / 8 : Nat) : Int) := by
    unfold osz; cases rexW p <;> cases p.opsize <;> simp
  have hreg8 : regLocOf p.rex.isSome (osz p) (regNum p m) = .reg (regNum p m) := by
    unfold regLocOf; rw [if_neg (by rcases hW3 with e | e | e <;> omega)]
  have hidx : reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 = BitVec.ofNat 4 (regNum p m) := by
    rw [hrexb]; exact hidx_reg hrv m
  have hn' := locReg_lt p.rex.isSome (osz p) (regNum p m) (regNum_lt p m)
  simp only [x86_cmovcc, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hsz, hsg, Int.toNat_natCast,
    ← bits3_zero, hX sg hsg4 hsg5, run_add_inc tr inc hinc htr, hlen, is_some, Bool.false_eq_true, ↓reduceIte,
    run_pure, run_jcc_spec hr hfr opc ho hcond, hidx, trunc128, nbytes_eq _ hW]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, in_64bit_mode, Bool.true_or, Bool.and_true]
    rcases hW3 with e | e | e
    · have hne : (((osz p / 8 : Nat) : Int) == 4) = false := by rw [e]; rfl
      simp only [hne, Bool.false_eq_true, ↓reduceIte, run_pure]
      refine ⟨_, run_write_iptr hl _ htr, ?_, hc.set (by decide) _⟩
      rw [putReg_self js (Or.inl e)]; exact h.setRipR _
    · have hne : (((osz p / 8 : Nat) : Int) == 4) = true := by rw [e]; rfl
      simp only [hne, ↓reduceIte, run_bind, run_rr32 (regNum_lt p m) (h.gpr _ (regNum_lt p m)), wr32_eq _ _ rex]
      have hw := run_write_rgfi_size h hl (w := 32) (by decide) p.rex.isSome rex hrex (regNum_lt p m) (regNum_8 p m)
        ((js.regs (regNum p m)).setWidth 32)
      have hreg32 : regLocOf p.rex.isSome 32 (regNum p m) = .reg (regNum p m) := rfl
      rw [hreg32] at hw
      rw [hw]
      have hn32 := locReg_lt p.rex.isSome 32 (regNum p m) (regNum_lt p m)
      rw [hreg32] at hn32
      refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn32 rfl]; exact hl) _ htr, ?_,
        (hc.setGpr hn32 _).set (by decide) _⟩
      have := (h.writeReg p.rex.isSome (w := 32) (regNum_lt p m) ((js.regs (regNum p m)).setWidth 32)).setRipR
        (BitVec.ofNat 64 (tr + inc))
      rw [hreg32] at this
      revert V hX; rw [e]; intro V hX
      exact this
    · have hne : (((osz p / 8 : Nat) : Int) == 4) = false := by rw [e]; rfl
      simp only [hne, Bool.false_eq_true, ↓reduceIte, run_pure]
      refine ⟨_, run_write_iptr hl _ htr, ?_, hc.set (by decide) _⟩
      rw [putReg_self js (Or.inr e)]; exact h.setRipR _
  · simp only [↓reduceIte, run_write_rgfi_size h hl hW _ rex hrex (regNum_lt p m) (regNum_8 p m) V]
    refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn' rfl]; exact hl) _ htr, ?_,
      (hc.setGpr hn' _).set (by decide) _⟩
    have := (h.writeReg p.rex.isSome (regNum_lt p m) V).setRipR (BitVec.ofNat 64 (tr + inc))
    rw [hreg8] at this ⊢
    exact this

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_cmov {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n)) (ho : 0x40 ≤ o ∧ o < 0x50)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ len = n + 2 + c ∧ len ≤ 15 ∧
      i = .cmov (o % 16) (osz p) (regNum p m) (rmDst p (osz p) mm.rm) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hreg : mm.reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hreg; subst hreg
  have hcs : o = 0x40 ∨ o = 0x41 ∨ o = 0x42 ∨ o = 0x43 ∨ o = 0x44 ∨ o = 0x45 ∨ o = 0x46 ∨ o = 0x47 ∨
      o = 0x48 ∨ o = 0x49 ∨ o = 0x4A ∨ o = 0x4B ∨ o = 0x4C ∨ o = 0x4D ∨ o = 0x4E ∨ o = 0x4F := by omega
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, hou, true_and, and_true,
      false_and, and_false, or_false, false_or, finish] at hd ⊢
    by_cases hl : 15 < n + 1 + 1 + c <;> by_cases hrp : p.rep = 0 <;>
      cases hf : p.fs <;> cases hk : p.lock <;>
      simp (config := {decide := true}) only [hf, hk, hl, hrp, ↓reduceIte, Bool.false_eq_true] at hd ⊢ <;>
      (try simp [lockable, withFS] at hd ⊢)
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := hd; refine ⟨by omega, by omega, ?_⟩; cases rm <;> simp_all [rmDst, rmLoc, regLocOf])
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, by cases rm <;> simp_all [rmDst, rmLoc, regLocOf]⟩)
      | (simp at hd; done)
      | (rcases rm with _ | _ <;> simp at hd)

set_option maxRecDepth 100000 in
theorem run_two_byte_cmov (opc : Nat) (hopc : 0x40 ≤ opc ∧ opc < 0x50)
    (sr tr : BitVec 48) (x : BitVec 52) (mp : BitVec 8) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (s : SState) :
    (two_byte_opcode_execute .Mode_64bit sr tr x mp rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_cmovcc .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  have hcs : opc = 0x40 ∨ opc = 0x41 ∨ opc = 0x42 ∨ opc = 0x43 ∨ opc = 0x44 ∨ opc = 0x45 ∨ opc = 0x46 ∨ opc = 0x47 ∨
      opc = 0x48 ∨ opc = 0x49 ∨ opc = 0x4A ∨ opc = 0x4B ∨ opc = 0x4C ∨ opc = 0x4D ∨ opc = 0x4E ∨ opc = 0x4F := by omega
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [two_byte_opcode_execute, ext_two_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxRecDepth 100000 in
theorem modrmP2_cmov {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hr : p.rep = 0) (o : Nat) (ho : 0x40 ≤ o ∧ o < 0x50) : modrmP2 x o = true := by
  unfold modrmP2; rw [mpref_norep hp hr]
  have hcs : o = 0x40 ∨ o = 0x41 ∨ o = 0x42 ∨ o = 0x43 ∨ o = 0x44 ∨ o = 0x45 ∨ o = 0x46 ∨ o = 0x47 ∨
      o = 0x48 ∨ o = 0x49 ∨ o = 0x4A ∨ o = 0x4B ∨ o = 0x4C ∨ o = 0x4D ∨ o = 0x4E ∨ o = 0x4F := by omega
  cases p.opsize <;>
  rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **CMOVcc r, r/m** (`0F 40–4F`): all 16 conditions, register and memory sources, every width
(the 32-bit form zero-extends its destination whether or not it moves). -/
theorem cmov_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n)) (ho : 0x40 ≤ o ∧ o < 0x50)
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
    have hcs : o = 0x40 ∨ o = 0x41 ∨ o = 0x42 ∨ o = 0x43 ∨ o = 0x44 ∨ o = 0x45 ∨ o = 0x46 ∨ o = 0x47 ∨
        o = 0x48 ∨ o = 0x49 ∨ o = 0x4A ∨ o = 0x4B ∨ o = 0x4C ∨ o = 0x4D ∨ o = 0x4E ∨ o = 0x4F := by omega
    rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [twoByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hlk, hfs, hrep, rfl, hlen, rfl⟩ := decode_cmov hpp ho hmd hd
  rw [step_of_decode hd] at hstep
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := Or.inr (osz_cases p)
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = 0x0F :: o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 2 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 2 + c) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  simp only [exec] at hstep
  rw [hnext] at hstep
  cases hrd : readLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c)) (osz p) (rmDst p (osz p) mm.rm) with
  | error e => simp [hrd] at hstep
  | ok X =>
  obtain ⟨hok, rfl⟩ := readLoc_loc hrd
  simp only [hrd] at hstep
  cases hc : condition (o % 16) js.flags with
  | none => simp [hc] at hstep
  | some b =>
  simp only [hc, Except.ok.injEq] at hstep; subst hstep
  refine rm_frame2 hrel hcfg hcode hlim hpp (fun x rex hpr => modrmP2_cmov hpr hrep o ho) hlk hmd
    (fun _ _ => hfs) hW (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => x86_cmovcc .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_two_byte_cmov o ho sr tr x _ hl rex _ sib s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr _ _ _
  obtain ⟨s', hs', hrel', hc'⟩ := run_cmovcc hrel hcfg hpr hrv o (by omega) hc m hm256 sib tr _ inc eaddr
    (hX true false false hok) hinc8 js.rip.toNat (by omega) (by omega) (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  rwa [hinc'] at hrel'

end JanusX86.Proofs
