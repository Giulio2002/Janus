import JanusX86.Proofs.Mov
import JanusX86.Proofs.Stack

/-! # MOVSXD r64, r/m32 (`REX.W 63`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_63 (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x63) m sib).run s =
      (x86_movsx .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x63) m sib).run s := by
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure, in_64bit_mode,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxHeartbeats 4000000 in
theorem run_movsxd63 {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (hw : rexW p = true)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (V : BitVec 32) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (32 / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_movsx .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 0x63)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((js.setReg (regNum p m) (V.signExtend 64)).setRip (BitVec.ofNat 64 (tr + inc))) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hlb : logbitp_bits 3 rex = rexW p := by rw [hrexb]; exact logbitp3_rexByte hrv
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hl := hc.log
  have hn := regNum_lt p m
  have hv : Sail.BitVec.truncate (Sail.BitVec.zeroExtend (Sail.BitVec.signExtend (Sail.BitVec.truncate
      (BitVec.setWidth 128 (BitVec.setWidth 64 V)) 32) 64) 128) 64 = V.signExtend 64 := by
    have e : Sail.BitVec.truncate (BitVec.setWidth 128 (BitVec.setWidth 64 V)) 32 = V := by
      apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate]
    rw [e]; apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Sail.BitVec.signExtend]
  simp only [x86_movsx, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hw, ↓reduceIte, hsg,
    show (4 : Int).toNat = 32 / 8 from rfl, ← bits3_zero, hX sg hsg4 hsg5, run_add_inc tr inc hinc htr, hlen,
    is_some, Bool.false_eq_true, run_pure, hlb, show ((8 : Int) == 8) = true from rfl, hv,
    show reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 = BitVec.ofNat 4 (regNum p m) by
      rw [hrexb]; exact hidx_reg hrv m, run_write_rgfi_size8 hl hn]
  refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn rfl]; exact hl) _ htr,
    (h.setReg hn _).setRipR _, (hc.setGpr hn _).set (by decide) _⟩

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem decode_movsxd {bytes : List Nat} {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x63 :: m :: rest, n))
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.rep = 0 ∧ rexW p = true ∧ len = n + 1 + c ∧ len ≤ 15 ∧
      i = .movx true 64 32 (regNum p m) (rmDst p 32 mm.rm) ∧ (∀ k', mm.rm = .r k' → p.fs = false) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hreg : mm.reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hreg; subst hreg
  cases hw : rexW p
  · exfalso
    simp only [rexW] at hw
    simp (config := {decide := true}) [oneByte, hw] at hd
  · simp only [rexW, decide_eq_true_eq] at hw
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hw, true_and, and_true,
      false_and, and_false, or_false, false_or, finish, Bool.not_true, Bool.false_eq_true] at hd ⊢
    by_cases hl : 15 < n + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
      cases rm <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, withFS, lockable, rmDst, rmLoc, regLocOf] at hd ⊢
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, rfl, fun _ h => by cases h⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; refine ⟨by omega, rfl, ?_⟩; simp)
      | omega

set_option maxHeartbeats 1000000 in
/-- **MOVSXD r64, r/m32** (`REX.W 63`): register, memory and `FS`-relative sources. -/
theorem movsxd_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x63 :: m :: rest, n))
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
    simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hlk, hrep, hw, rfl, hlen, rfl, hfs⟩ := decode_movsxd hpp hmd hd
  rw [step_of_decode hd] at hstep
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = 0x63 :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + 0) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  simp only [exec] at hstep
  rw [hnext] at hstep
  cases hrd : readLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + 0)) 32 (rmDst p 32 mm.rm) with
  | error e => simp only [hrd] at hstep; cases hstep
  | ok X =>
  simp only [hrd, ↓reduceIte, Except.ok.injEq] at hstep; subst hstep
  obtain ⟨hok, rfl⟩ := readLoc_loc hrd
  refine rm_frame hrel hcfg hcode hlim hpp (by decide) (by omega) (by omega) (by decide) hlk hmd hfs
    (w := 32) (by decide) (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => x86_movsx .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x63) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_one_byte_63 sr tr x hl rex _ sib s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX _ _ _ _
  obtain ⟨s', hs', hrel', hc'⟩ := run_movsxd63 hrel hcfg hpr hrv hw m hm256 sib tr _ inc eaddr
    (hX true false false hok) hinc8 js.rip.toNat (by omega) (by omega) (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  rw [hinc'] at hrel'
  simpa [Janus.Amd64.State.putReg] using hrel'

end JanusX86.Proofs
