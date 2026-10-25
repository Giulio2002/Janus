import JanusX86.Proofs.Div

/-! # LEAVE (`C9`), PUSH imm (`68/6A`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_leave (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xC9) m sib).run s =
      (x86_leave .Mode_64bit sr tr x rex (BitVec.ofNat 8 0xC9) m sib).run s := by
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxHeartbeats 4000000 in
theorem run_leave {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hos : p.opsize = false) (m sib : BitVec 8) (tr sr : Nat) (htr : tr < 2 ^ 47)
    (hacc : js.mem.accessible (js.regs 5).toNat 8 false = true)
    (hbp : (js.regs 5).toNat + 8 < 2 ^ 47) :
    ∃ s', (x86_leave .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 0xC9)
      m sib).run s = .ok () s' ∧
      Rel (((js.setReg 4 (js.regs 5 + 8)).setReg 5
        (BitVec.ofNat 64 (js.mem.readLE (js.regs 5).toNat 8))).setRip (BitVec.ofNat 64 tr)) s' ∧ X86Config s' := by
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  have hbp4 : (js.regs 5).toNat < 2 ^ 48 := by omega
  have hadd : js.regs 5 + 8 = BitVec.ofNat 64 ((js.regs 5).toNat + 8) := by
    apply BitVec.eq_of_toNat_eq; simp
  have hspadd : (add_to_sptr .Mode_64bit (js.regs 5) (bits_of_int (8 : Int) 64)).run s = .ok (js.regs 5 + 8) s := by
    rw [run_add_to_sptr_int _ _ hbp4 (by omega) (by omega) (by omega), hadd]
    congr 2
  have hload := run_load_rel h hc 8 (n := 8) (by decide) (js.regs 5) (seg := 2) ⟨by decide, by decide⟩ ":R" false hacc
  have hv : Sail.BitVec.truncate (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * 8) (js.mem.readLE (js.regs 5).toNat 8)) 128) 64 =
      BitVec.ofNat 64 (js.mem.readLE (js.regs 5).toNat 8) := by
    apply BitVec.eq_of_toNat_eq
    have := Janus.Arm64.Memory.readLE_lt js.mem (js.regs 5).toNat 8
    simp [Sail.BitVec.truncate, Sail.BitVec.zeroExtend] at this ⊢
  have hl := hc.log
  simp only [x86_leave, run_bind, run_select_operand_size_d64 hp hos, hcr8, run_rgfi_size8 (n := 5) (by decide)
    (h.gpr 5 (by decide)), show (0x5#4 : BitVec 4) = BitVec.ofNat 4 5 from rfl, run_alignment_checking h hc, hsel,
    show (8 : Int).toNat = 8 from rfl, Int.toNat_natCast, Int.reduceToNat, rme_size, hload,
    show (5#4 : BitVec 4) = BitVec.ofNat 4 5 from rfl, run_pure, hspadd, hv,
    run_write_rgfi_size8 hl (n := 5) (by decide), write_sptr, in_64bit_mode, ↓reduceIte]
  have hl5 : (setGpr s (BitVec.ofNat 64 (js.mem.readLE (js.regs 5).toNat 8)) 5).regs.get? .log_register_writes =
      some false := by rw [get?_setGpr_of_not _ _ (by decide) rfl]; exact hl
  rw [show (4 : Int) = ((4 : Nat) : Int) from rfl, run_write_rgfi hl5 (n := 4) (by decide)]
  simp only [run_bind]
  refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not _ _ (by decide) rfl]; exact hl5) _ htr, ?_,
    (((hc.setGpr (by decide) _).setGpr (by decide) _).set (by decide) _)⟩
  have := ((h.setReg (r := 5) (by decide) (BitVec.ofNat 64 (js.mem.readLE (js.regs 5).toNat 8))).setReg
    (r := 4) (by decide) (js.regs 5 + 8)).setRipR (BitVec.ofNat 64 tr)
  have e : (js.setReg 4 (js.regs 5 + 8)).setReg 5 (BitVec.ofNat 64 (js.mem.readLE (js.regs 5).toNat 8)) =
      (js.setReg 5 (BitVec.ofNat 64 (js.mem.readLE (js.regs 5).toNat 8))).setReg 4 (js.regs 5 + 8) := by
    cases js; simp only [Janus.Amd64.State.setReg, Janus.Amd64.State.mk.injEq, and_true]
    funext i; split <;> split <;> simp_all
  rw [e]; exact this

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem decode_leave {bytes : List Nat} {p : Prefixes} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0xC9 :: rest, n))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.opsize = false ∧ len = n + 1 ∧ len ≤ 15 ∧ i = .leave := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  simp (config := {decide := true}) only [↓reduceIte, oneByte, true_and, and_true, finish,
    false_and, and_false, or_false, false_or] at hd
  by_cases hl : 15 < n + 1 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
    cases ho : p.opsize <;> cases hs : p.seg <;>
    simp (config := {decide := true}) [hf, hk, hl, hrp, ho, hs, withFS, lockable] at hd
  all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, rfl, rfl, by omega, rfl⟩)

set_option maxHeartbeats 1000000 in
/-- **LEAVE** (`C9`), for a frame that does not end at the top of the lower half (`RBP + 8 < 2^47`: the
model stops with a model error on a non-canonical new `RSP`, Sail-x86 defect D7). -/
theorem leave_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0xC9 :: rest, n))
    (hbp : (js.regs 5).toNat + 8 < 2 ^ 47)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hlk, hos, rfl, hlen, rfl⟩ := decode_leave hpp hd
  rw [step_of_decode hd] at hstep
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim (by decide) (by decide)
    ⟨by decide, by decide, by decide⟩ (by rw [show modrmP1 0xC9 = false by decide]; simp [modrmSib])
  rw [show modrmP1 0xC9 = false by decide] at hf
  simp only [modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  rw [run_one_byte_leave _ _ x hl0] at hf
  simp only [exec] at hstep
  have hnk : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1)) % 2 ^ 64) = BitVec.ofNat 64 (js.rip.toNat + n + 1) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1
  rw [hnk] at hstep
  cases hld : load js.mem (js.regs 5).toNat 8 with
  | error e => simp only [hld] at hstep; cases hstep
  | ok v =>
    simp only [hld, Except.ok.injEq] at hstep; subst hstep
    unfold load at hld
    split at hld
    · rename_i hacc
      simp only [Except.ok.injEq] at hld; subst hld
      obtain ⟨s', hs', hrel', hcfg'⟩ := run_leave hrel hcfg hpr hos 0#8 0#8 (js.rip.toNat + n + 1) js.rip.toNat
        (by omega) hacc hbp
      exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hrel', hcfg'⟩
    · simp at hld

end JanusX86.Proofs
