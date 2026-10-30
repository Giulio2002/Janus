import JanusX86.Proofs.AluDispatch

/-! # The one-byte dispatch of the ALU opcodes -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- The `#UD` check of the (E, G) ALU arms: `LOCK` on a register destination, or `LOCK` on `CMP`. -/
def lockChkEG (k : Nat) (m : BitVec 8) (x : BitVec 52) : Bool :=
  if k = 7 then (0xF0#8 == _get_prefixes_lck x) else ((_get_modr_m_mod m == 3#2) && (0xF0#8 == _get_prefixes_lck x))

set_option maxRecDepth 100000 in
theorem run_one_byte_e_g (k f : Nat) (hk : k < 8) (hf : f < 2) (sr tr : BitVec 48) (x : BitVec 52)
    (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 (8 * k + f)) m sib).run s =
      (((if lockChkEG k m x = true then x86_fault "(:UD)"
          else pure ()) : SailM Unit) >>= fun _ =>
        x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g (sailOp (Janus.Amd64.Decode.aluOp k)) .Mode_64bit sr tr x rex
          (BitVec.ofNat 8 (8 * k + f)) m sib).run s := by
  match k, hk, f, hf with
  | 0, _, 0, _ | 0, _, 1, _ | 1, _, 0, _ | 1, _, 1, _ | 2, _, 0, _ | 2, _, 1, _ | 3, _, 0, _ | 3, _, 1, _
  | 4, _, 0, _ | 4, _, 1, _ | 5, _, 0, _ | 5, _, 1, _ | 6, _, 0, _ | 6, _, 1, _ | 7, _, 0, _ | 7, _, 1, _ =>
    simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
      ↓reduceIte, Bool.false_eq_true, Janus.Amd64.Decode.aluOp, sailOp, lockChkEG] <;> rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_g_e (k f : Nat) (hk : k < 8) (hf : 2 ≤ f ∧ f < 4) (sr tr : BitVec 48) (x : BitVec 52)
    (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 (8 * k + f)) m sib).run s =
      (x86_add_adc_sub_sbb_or_and_xor_cmp_g_e (sailOp (Janus.Amd64.Decode.aluOp k)) .Mode_64bit sr tr x rex
          (BitVec.ofNat 8 (8 * k + f)) m sib).run s := by
  obtain ⟨hf1, hf2⟩ := hf
  match k, hk, f, hf1, hf2 with
  | 0, _, 2, _, _ | 0, _, 3, _, _ | 1, _, 2, _, _ | 1, _, 3, _, _ | 2, _, 2, _, _ | 2, _, 3, _, _
  | 3, _, 2, _, _ | 3, _, 3, _, _ | 4, _, 2, _, _ | 4, _, 3, _, _ | 5, _, 2, _, _ | 5, _, 3, _, _
  | 6, _, 2, _, _ | 6, _, 3, _, _ | 7, _, 2, _, _ | 7, _, 3, _, _ =>
    simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
      ↓reduceIte, Bool.false_eq_true, Janus.Amd64.Decode.aluOp, sailOp, hl, Bool.and_false, run_bind, run_pure,
      show (240#8 == 0#8) = false from rfl] <;> rfl

end JanusX86.Proofs
