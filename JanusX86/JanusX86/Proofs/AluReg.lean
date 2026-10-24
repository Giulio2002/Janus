import JanusX86.Proofs.AluDispatch
import JanusX86.Proofs.Fields

/-! # ALU instructions, register forms -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem byteop_all : ∀ opc < 256, (0#1 == Sail.BitVec.truncate (1#8 &&& BitVec.ofNat 8 opc) 1) = decide (opc % 2 = 0) := by
  decide +kernel

/-- Janus' operand size from the prefixes (`oneByte`'s `osz`). -/
def osz (p : Janus.Amd64.Decode.Prefixes) : Nat := if rexW p then 64 else if p.opsize then 16 else 32

theorem osz_cases (p : Janus.Amd64.Decode.Prefixes) : osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := by
  unfold osz; split <;> (try split) <;> simp

theorem size_int (p : Janus.Amd64.Decode.Prefixes) (b : Bool) :
    (if b = true then (1 : Int) else if rexW p = true then (if false = true then 4 else 8) else if p.opsize = true then 2 else 4) =
      (((if b then 8 else osz p) / 8 : Nat) : Int) := by
  unfold osz; cases b <;> cases rexW p <;> cases p.opsize <;> rfl

theorem run_select_segment_register {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8}
    (hp : PfxRel p x rex) (md : BitVec 2) (rm : BitVec 3) (sib : BitVec 8) (s : SState) :
    ∃ sg, (select_segment_register .Mode_64bit x md rm sib).run s = .ok sg s ∧ (sg = 4 ↔ p.fs = true) ∧
      sg ≠ 5 := by
  have hseg := hp.seg
  have hadr : (0x67#8 == _get_prefixes_adr x) = false := by rw [hp.adr]; decide
  cases hf : p.fs
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hseg
    simp only [select_segment_register, hseg, eq_bits_nat]
    simp (config := {decide := true}) only [↓reduceIte, run_bind, run_select_address_size x hadr]
    split
    · exact ⟨2, rfl, by simp, by decide⟩
    · exact ⟨3, rfl, by simp, by decide⟩
  · simp only [hf, ↓reduceIte] at hseg
    simp only [select_segment_register, hseg, eq_bits_nat]
    simp (config := {decide := true}) only [↓reduceIte]
    exact ⟨4, rfl, by simp, by decide⟩

theorem run_operand_from_reg {js : Janus.Amd64.State} {s : SState} (h : Rel js s) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (rexP : Bool) (rex : BitVec 8) (hrex : (rex == 0#8) = !rexP)
    {n : Nat} (hn : n < 16) (hn8 : n < 8 ∨ rexP = true) (a : BitVec 3) (hidx : reg_index a rex 0#2 = BitVec.ofNat 4 n)
    (iac mp : Bool) (sg : Nat) (x : BitVec 52) (tr : BitVec 48) (sib : BitVec 8) (ni : BitVec 3) :
    (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) iac mp sg x tr rex a 3#2 sib ni).run s =
      .ok (((regVal js w (regLocOf rexP w n)).setWidth 64).setWidth 128, 0, 0#64) s := by
  have e : bits_of_int ((w / 8 : Nat) : Int) 4 = BitVec.ofNat 4 (w / 8) := nbytes_eq w hw
  simp only [x86_operand_from_modr_m_and_sib_bytes, run_bind, run_pure, ↓reduceIte, e, hidx,
    run_rgfi_size h hw rexP rex hrex hn hn8, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
  simp (config := {decide := true}) only [↓reduceIte, run_pure, run_bind, run_rgfi_size h hw rexP rex hrex hn hn8]

end JanusX86.Proofs
