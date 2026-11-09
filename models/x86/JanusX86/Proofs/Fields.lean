import JanusX86.Proofs.Flags

/-! # Decoded fields: ModRM, REX, operand size

The model extracts ModRM/SIB fields and REX bits from bit vectors; these lemmas give them as
Janus' natural-number formulas (`Decode.modrm`: `md = m / 64`, `ext = m / 8 % 8`, `rm = m % 8`,
`REX = WRXB`). Finite facts are checked on every byte by `decide +kernel`. -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem modrm_fields : ∀ m < 256,
    _get_modr_m_mod (BitVec.ofNat 8 m) = BitVec.ofNat 2 (m / 64) ∧
    _get_modr_m_reg (BitVec.ofNat 8 m) = BitVec.ofNat 3 (m / 8 % 8) ∧
    _get_modr_m_r_m (BitVec.ofNat 8 m) = BitVec.ofNat 3 (m % 8) := by
  decide +kernel

theorem sib_fields : ∀ m < 256,
    _get_sib_scale (BitVec.ofNat 8 m) = BitVec.ofNat 2 (m / 64) ∧
    _get_sib_index (BitVec.ofNat 8 m) = BitVec.ofNat 3 (m / 8 % 8) ∧
    _get_sib_base (BitVec.ofNat 8 m) = BitVec.ofNat 3 (m % 8) := by
  decide +kernel

/-- The REX byte of Janus' prefixes (`0` when there is none). -/
def rexByte (p : Janus.Amd64.Decode.Prefixes) : Nat :=
  match p.rex with
  | some r => 0x40 + r
  | none => 0

theorem reg_index_rex : ∀ a < 8, ∀ r < 16, ∀ k < 3,
    reg_index (BitVec.ofNat 3 a) (BitVec.ofNat 8 (0x40 + r)) (BitVec.ofNat 2 k) =
      BitVec.ofNat 4 (a + 8 * (r / 2 ^ k % 2)) := by
  decide +kernel

theorem reg_index_norex : ∀ a < 8, ∀ k < 3,
    reg_index (BitVec.ofNat 3 a) 0#8 (BitVec.ofNat 2 k) = BitVec.ofNat 4 a := by
  decide +kernel

theorem logbitp3_rex : ∀ r < 16, logbitp_bits 3 (BitVec.ofNat 8 (0x40 + r)) = decide (r / 8 = 1) := by
  decide +kernel

theorem logbitp3_norex : logbitp_bits 3 (0#8) = false := by decide

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- Janus' `REX.W`. -/
def rexW (p : Janus.Amd64.Decode.Prefixes) : Bool := (p.rex.getD 0) / 8 = 1

theorem logbitp3_rexByte {p : Janus.Amd64.Decode.Prefixes} (hr : ∀ r, p.rex = some r → r < 16) :
    logbitp_bits 3 (BitVec.ofNat 8 (rexByte p)) = rexW p := by
  unfold rexByte rexW
  cases e : p.rex with
  | none => simpa using logbitp3_norex
  | some r => simp only [Option.getD_some]; exact logbitp3_rex r (hr r e)

theorem run_select_operand_size {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8}
    (hp : PfxRel p x rex) (hrv : ∀ r, p.rex = some r → r < 16) (byte imm : Bool) (s : SState) :
    (select_operand_size .Mode_64bit byte rex imm x false false false).run s =
      .ok (if byte then 1 else if rexW p then (if imm then 4 else 8) else if p.opsize then 2 else 4) s := by
  have hrex : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  subst hrex
  have hopr := hp.opr
  simp only [select_operand_size, in_64bit_mode, logbitp3_rexByte hrv, hopr]
  cases byte <;> cases hw : rexW p <;> cases imm <;> cases hs : p.opsize <;> simp <;> rfl

end JanusX86.Proofs
