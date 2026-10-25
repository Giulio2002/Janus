import JanusX86.Proofs.Lock

/-! # NOP (`90`, `66 90`, `F3 90` PAUSE) and NOP r/m (`0F 1F /0`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_nop90 (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hrb : logbitp_bits 0 rex = false) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x90) m sib).run s =
      (x86_one_byte_nop .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x90) m sib).run s := by
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, hrb, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem logbitp0_rex : ∀ r < 16, logbitp_bits 0 (BitVec.ofNat 8 (0x40 + r)) = decide (r % 2 = 1) := by
  decide +kernel

theorem logbitp0_rexByte {p : Prefixes} (hr : ∀ r, p.rex = some r → r < 16) (hb : p.rex.getD 0 % 2 = 0) :
    logbitp_bits 0 (BitVec.ofNat 8 (rexByte p)) = false := by
  unfold rexByte
  cases e : p.rex with
  | none => decide
  | some r => rw [e] at hb; simp only [Option.getD_some] at hb ⊢; rw [logbitp0_rex r (hr r e)]; simp [hb]

theorem decode_nop90 {bytes : List Nat} {p : Prefixes} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x90 :: rest, n)) (hrb : p.rex.getD 0 % 2 = 0)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ len = n + 1 ∧ len ≤ 15 ∧ i = .nop := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  simp (config := {decide := true}) only [↓reduceIte, oneByte, hrb, true_and, and_true, finish,
    false_and, and_false, or_false, false_or] at hd
  by_cases hl : 15 < n + 1 <;> by_cases hrp : p.rep = 0xF2 <;> cases hf : p.fs <;> cases hk : p.lock <;>
    simp (config := {decide := true}) [hf, hk, hl, hrp, withFS, lockable] at hd
  all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, rfl, by omega, rfl⟩)

set_option maxHeartbeats 1000000 in
/-- **NOP** (`90`, with any operand-size/`REX.W`/segment prefix, and `F3 90` = PAUSE). -/
theorem nop_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x90 :: rest, n)) (hrb : p.rex.getD 0 % 2 = 0)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hlk, rfl, hlen, rfl⟩ := decode_nop90 hpp hrb hd
  rw [step_of_decode hd] at hstep
  simp only [exec, Except.ok.injEq] at hstep; subst hstep
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim (by decide) (by decide)
    ⟨by decide, by decide, by decide⟩ (by rw [show modrmP1 0x90 = false by decide]; simp [modrmSib])
  rw [show modrmP1 0x90 = false by decide] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hpr.rexb]; rfl
  rw [run_one_byte_nop90 _ _ x hl0 rex _ _ (by rw [hrexb]; exact logbitp0_rexByte hrv hrb)] at hf
  have hlen' := check_len_ok js.rip.toNat (js.rip.toNat + n + 1) (by omega) (by omega) (by omega)
  simp only [x86_one_byte_nop, hlen', is_some, Bool.false_eq_true, ↓reduceIte, run_bind, run_pure] at hf
  rw [run_write_iptr hcfg.log _ (by omega)] at hf
  refine ⟨_, run_janus_x86_step hf, ?_, hcfg.set (by decide) _⟩
  have := hrel.setRipR (BitVec.ofNat 64 (js.rip.toNat + n + 1))
  rwa [show BitVec.ofNat 64 ((js.rip.toNat + (n + 1)) % 2 ^ 64) = BitVec.ofNat 64 (js.rip.toNat + n + 1) by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

set_option maxRecDepth 100000 in
theorem run_two_byte_nop1f (sr tr : BitVec 48) (x : BitVec 52) (mp : BitVec 8) (hl : _get_prefixes_lck x = 0#8)
    (rex m sib : BitVec 8) (s : SState) :
    (two_byte_opcode_execute .Mode_64bit sr tr x mp rex (BitVec.ofNat 8 0x1F) m sib).run s =
      (x86_two_byte_nop .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x1F) m sib).run s := by
  simp (config := {decide := true}) only [two_byte_opcode_execute, ext_two_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

theorem decode_nop1f {bytes : List Nat} {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: 0x1F :: m :: rest, n))
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ len = n + 2 + c ∧ len ≤ 15 ∧ i = .nop := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, true_and, and_true,
    false_and, and_false, or_false, false_or] at hd
  by_cases hl : 15 < n + 1 + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
    cases ho : p.opsize <;> by_cases he : mm.ext = 0 <;>
    simp (config := {decide := true}) [hf, hk, hl, hrp, ho, he, finish, withFS, lockable] at hd
  all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, rfl, hrp, by omega, by omega, rfl⟩)

set_option maxRecDepth 100000 in
theorem modrmP2_1f {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hr : p.rep = 0) : modrmP2 x 0x1F = true := by
  unfold modrmP2; rw [mpref_norep hp hr]
  cases p.opsize <;> decide

set_option maxHeartbeats 1000000 in
/-- **NOP r/m** (`0F 1F /0`, the multi-byte NOP): every addressing form, no memory access. -/
theorem nop1f_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: 0x1F :: m :: rest, n))
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
    simp (config := {decide := true}) [twoByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hlk, hfs, hrep, rfl, hlen, rfl⟩ := decode_nop1f hpp hmd hd
  rw [step_of_decode hd] at hstep
  simp only [exec, Except.ok.injEq] at hstep; subst hstep
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = 0x0F :: 0x1F :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  refine rm_frame2 hrel hcfg hcode hlim hpp (fun x rex hpr => modrmP2_1f hpr hrep) hlk hmd
    (fun _ _ => hfs) (w := 8) (by decide) (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => x86_two_byte_nop .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x1F) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_two_byte_nop1f sr tr x _ hl rex _ sib s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ _ _ hEA hR3 _
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm256
  have hinc3 : (bits_of_int (inc : Int) 3) = BitVec.ofNat 3 inc := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have hlen' := check_len_ok js.rip.toNat (tr + inc) (by omega) (by omega) (by omega)
  have hmod : ((BitVec.ofNat 2 (m / 64) : BitVec 2) == 0b11#2) = decide (m / 64 = 3) := by
    have : m / 64 < 4 := by omega
    revert this; generalize m / 64 = q; intro hq
    rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl | rfl <;> decide
  have hEA' : (if (BitVec.ofNat 2 (m / 64) == 0b11#2) = true then (pure (0x0000000000000000#64, (0 : Int)) : SailM _)
      else x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 tr) rex (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64))
        sib 0b000#3).run s = .ok (eaddr, (inc : Int)) s := by
    rw [hmod]
    by_cases h3m : m / 64 = 3
    · obtain ⟨rfl, rfl⟩ := hR3 h3m; simp [h3m]
    · simp only [h3m, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hEA h3m
  simp only [x86_two_byte_nop, h1, h2, h3, run_bind, hEA', run_add_inc tr inc hinc8 (by omega), hlen', is_some,
    Bool.false_eq_true, ↓reduceIte, run_pure]
  refine ⟨_, run_write_iptr hcfg.log _ (by omega), ?_, hcfg.set (by decide) _⟩
  have := hrel.setRipR (BitVec.ofNat 64 (tr + inc))
  have e : BitVec.ofNat 64 (tr + inc) = BitVec.ofNat 64 ((js.rip.toNat + (n + 2 + c)) % 2 ^ 64) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  rw [e] at this ⊢
  exact this

end JanusX86.Proofs
