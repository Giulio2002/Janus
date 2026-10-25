import JanusX86.Proofs.Xchg9

/-! # BT r, r (`0F A3`, register destination) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxHeartbeats 4000000 in
theorem run_bt_a3 {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (m : Nat) (hm : m < 256) (hm3 : m / 64 = 3) (sib : BitVec 8)
    (tr sr : Nat) (hl1 : sr ≤ tr) (hl2 : tr ≤ sr + 15) (htr : tr < 2 ^ 47) :
    ∃ s', (x86_bt_0f_a3 .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 0xA3)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((js.setFlags (btFlags ((regVal js (osz p) (.reg (rmNum p m))).getLsbD
        ((regVal js (osz p) (.reg (regNum p m))).toNat % osz p)))).setRip (BitVec.ofNat 64 tr)) s' ∧
      X86Config s' := by
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW3 := osz_cases p
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := Or.inr hW3
  obtain ⟨sg, hsg, -, -⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr tr hl1 hl2 htr
  have hl := hc.log
  have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) = ((osz p / 8 : Nat) : Int) := by
    have := size_int p false; simp only [Bool.false_eq_true, ↓reduceIte] at this; rw [this]
  have hreg : ∀ k, regLocOf p.rex.isSome (osz p) k = .reg k := fun k => by
    unfold regLocOf; rw [if_neg (by rcases hW3 with e | e | e <;> omega)]
  have hidx : reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 = BitVec.ofNat 4 (regNum p m) := by
    rw [hrexb]; exact hidx_reg hrv m
  have hidx2 : reg_index (BitVec.ofNat 3 (m % 8)) rex 0#2 = BitVec.ofNat 4 (rmNum p m) := by
    rw [hrexb]; exact hidx_rm hrv m
  have hO := run_rgfi_size h hW _ rex hrex (regNum_lt p m) (regNum_8 p m) (s := s)
  have hB := run_rgfi_size h hW _ rex hrex (rmNum_lt p m) (rmNum_8 p m) (s := s)
  rw [hreg] at hO hB
  generalize regVal js (osz p) (.reg (regNum p m)) = O at hO ⊢
  generalize regVal js (osz p) (.reg (rmNum p m)) = B at hB ⊢
  have hmod : (BitVec.ofNat 2 (m / 64) == 0b11#2) = true := by rw [hm3]; decide
  have hash : ash_left_int ((osz p / 8 : Nat) : Int) 3 = ((osz p : Nat) : Int) := by
    rcases hW3 with e | e | e <;> rw [e] <;> decide
  have hmodv : X86Sail.Functions.mod (Sail.BitVec.toNatInt (O.setWidth 64)) (ash_left_int ((osz p / 8 : Nat) : Int) 3) =
      ((O.toNat % osz p : Nat) : Int) := by
    rw [hash, show Sail.BitVec.toNatInt (O.setWidth 64) = ((O.toNat : Nat) : Int) by
      simp only [Sail.BitVec.toNatInt, BitVec.toNat_setWidth]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le O.isLt (Nat.pow_le_pow_right (by decide)
        (by rcases hW3 with e | e | e <;> omega)))]; rfl]
    exact mod_nat _ _ (by rcases hW3 with e | e | e <;> omega)
  have hbit : logbit_bits ((O.toNat % osz p : Nat) : Int) (Sail.BitVec.zeroExtend (B.setWidth 64) 128) =
      BitVec.ofBool (B.getLsbD (O.toNat % osz p)) := by
    have : O.toNat % osz p < osz p := Nat.mod_lt _ (by rcases hW3 with e | e | e <;> omega)
    have h128 : O.toNat % osz p < 128 := by rcases hW3 with e | e | e <;> omega
    have h64 : O.toNat % osz p < 64 := by rcases hW3 with e | e | e <;> omega
    rw [logbit_eq _ _ h128]
    simp [Sail.BitVec.zeroExtend, BitVec.getLsbD_setWidth, h128, h64]
  simp only [x86_bt_0f_a3, h1, h2, h3, run_bind, hsg, run_select_operand_size hp hrv, hsz, nbytes_eq _ hW,
    hidx, hO, hmod, ↓reduceIte, run_pure, show ((0 : Int)) = ((0 : Nat) : Int) from rfl,
    run_add_inc tr 0 (by decide) (by omega), Nat.add_zero, hlen, is_some, Bool.false_eq_true, hidx2, hB, hmodv, hbit]
  have hu' : ∀ v : BitVec 32, (s.set .rflags v).regs.get? .janus_undef = some u := fun v => by
    rw [get?_set_ne _ _ (by decide)]; exact hu
  simp only [run_readReg hr, run_writeReg, run_readReg (get?_set_same _ _ _), set_set, run_undef_flg (hu' _)]
  have hl' : (s.set .rflags (btfl rf (BitVec.ofBool (B.getLsbD (O.toNat % osz p))) u)).regs.get?
      .log_register_writes = some false := by rw [get?_set_ne _ _ (by decide)]; exact hl
  refine ⟨_, run_write_iptr hl' _ htr, ?_, (hc.set (by decide) _).set (by decide) _⟩
  exact h.flagsRip _ _ (flagsRel_bt hfr _ u) _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem decode_bta3 {bytes : List Nat} {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: 0xA3 :: m :: rest, n))
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ ∃ k, mm.rm = .r k ∧ len = n + 2 + c ∧
      len ≤ 15 ∧ i = .bit .bt (osz p) (.reg k) (.loc (.reg mm.reg)) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  obtain ⟨md, rg, ext, rm⟩ := mm
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, hou, true_and, and_true,
    false_and, and_false, or_false, false_or] at hd ⊢
  by_cases hl : 15 < n + 1 + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
    cases rm <;>
    simp (config := {decide := true}) [hf, hk, hl, hrp, finish, withFS, lockable] at hd ⊢
  all_goals (obtain ⟨rfl, rfl⟩ := hd; first | exact ⟨by omega, rfl⟩ | exact ⟨rfl, by omega, rfl⟩ | omega)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

set_option maxHeartbeats 1000000 in
/-- **BT r16/32/64, r** (`0F A3`, register destination; Janus rejects the memory bit-string form). -/
theorem bt_a3_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: 0xA3 :: m :: rest, n))
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
  obtain ⟨hlk, hfs, hrep, k, hk, rfl, hlen, rfl⟩ := decode_bta3 hpp hmd hd
  rw [step_of_decode hd] at hstep
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = 0x0F :: 0xA3 :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hk; subst hk
  obtain ⟨hm3, hkk, rfl, rfl⟩ := modrm_r hmd
  have hrg : rg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  have hkr : k = rmNum p m := by rw [hkk]; rfl
  subst hrg hkr
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := by rcases osz_cases p with e | e | e <;> simp [e]
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 2 + 1)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 2 + 1) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1
  simp only [exec, execBit, readSrc, readLoc, Except.ok.injEq] at hstep
  rw [hnext] at hstep
  subst hstep
  refine rm_frame2 hrel hcfg hcode hlim hpp (fun x rex hpr => modrmP2_bt hpr hrep 0xA3 (Or.inr rfl)) hlk hmd
    (fun _ _ => hfs) hW (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => x86_bt_0f_a3 .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xA3) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_two_byte_bt_a3 sr tr x _ hl rex _ sib s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ _ _ _ hR3 _
  obtain ⟨rfl, -⟩ := hR3 hm3
  obtain ⟨s', hs', hrel', hc'⟩ := run_bt_a3 hrel hcfg hpr hrv m hm256 hm3 sib tr js.rip.toNat
    (by omega) (by omega) (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  rw [show js.rip.toNat + n + 2 + 1 = tr by omega]
  exact hrel'

end JanusX86.Proofs
