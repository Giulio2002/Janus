import JanusX86.Proofs.Mem
import JanusX86.Proofs.Config

/-! # The 64-bit application-level path: mode, address size, memory loads

Under `X86Config`, `x86_operation_mode` is 64-bit mode, the address size is 8 bytes (no `67`
prefix), and `load_bytes_from_ea` of a non-FS/GS segment reads the bytes at the effective
address (`rb`). -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_x86_operation_mode {s : SState} (h : X86Config s) :
    (x86_operation_mode ()).run s = .ok .Mode_64bit s := by
  obtain ⟨v, hv, he⟩ := h.efer
  obtain ⟨a, ha, hl⟩ := h.csl
  simp only [x86_operation_mode, n64_bit_modep, read_msr, run_bind, run_readReg hv, run_readReg ha,
    run_pure, he, hl]
  rfl

theorem run_ms {s : SState} (h : X86Config s) : (ms ()).run s = .ok false s := run_readReg h.ms

theorem run_fault {s : SState} (h : X86Config s) : (fault ()).run s = .ok false s := run_readReg h.fault

theorem run_select_address_size (p : BitVec 52) (hp : (0x67#8 == _get_prefixes_adr p) = false)
    (s : SState) : (select_address_size .Mode_64bit (some p)).run s = .ok 8 s := by
  simp only [select_address_size, hp, in_64bit_mode]; rfl

theorem canon_ok {x : Int} (h1 : 0 ≤ x) (h2 : x < 2 ^ 47) :
    decide (-(2 ^ 47 : Int) ≤ x ∧ x < 2 ^ 47) = true := by
  simp only [decide_eq_true_eq]; omega

theorem run_ea_to_la {s : SState} (eff : BitVec 64) {seg : Nat} (hseg : seg ≠ 4 ∧ seg ≠ 5)
    (n : Nat) (ha : eff.toNat < 2 ^ 47) :
    (ea_to_la .Mode_64bit eff seg n).run s = .ok eff s := by
  have h1 : ((seg == 4) || (seg == 5)) = false := by simp [hseg.1, hseg.2]
  have hint : eff.toInt = eff.toNat := toInt_of_lt eff (by omega)
  simp only [ea_to_la, in_64bit_mode, h1, ↓reduceIte, Bool.false_eq_true, run_bind, run_pure,
    run_canonical_address_p, hint, canon_ok (Int.natCast_nonneg _) (by omega : (eff.toNat : Int) < 2 ^ 47),
    Bool.not_true]

theorem run_check_linear_memory_access_nochk (asz n : Nat) (la : BitVec 64) (b : Option Nat)
    (seg : Nat) (k : String) (mp : Bool) (s : SState) :
    (check_linear_memory_access .Mode_64bit asz n la b seg k false mp).run s = .ok () s := by
  simp only [check_linear_memory_access]; rfl

/-- A load through a non-FS/GS segment, without alignment check, of bytes in the Sail memory. -/
theorem run_load_bytes_from_ea {s : SState} (h : X86Config s) {r : BitVec 64}
    (hr : s.regs.get? .rip = some r) (asz : Nat) {n : Nat} (hn : 0 < n) (eff : BitVec 64)
    (b : Option Nat) {seg : Nat} (hseg : seg ≠ 4 ∧ seg ≠ 5) (k : String) (mp : Bool)
    (ha : eff.toNat + n ≤ 2 ^ 47) (f : Nat → BitVec 8)
    (hm : ∀ j < n, s.mem[eff.toNat + j]? = some (f j)) :
    (load_bytes_from_ea .Mode_64bit asz n eff b seg k false mp).run s =
      .ok (BitVec.ofNat (8 * n) (sumLE (fun j => (f j).toNat) n)) s := by
  obtain ⟨v, hv, _⟩ := h.csl
  simp only [load_bytes_from_ea, run_bind, run_readReg hv, run_pure, in_64bit_mode, Bool.not_true,
    Bool.false_and, Bool.false_eq_true, ite_false, run_ea_to_la eff hseg n (by omega),
    run_check_linear_memory_access_nochk]
  exact run_rb h.app hr hn eff ha f hm k

/-- Instruction fetch of one byte. -/
theorem run_rme08 {s : SState} (h : X86Config s) {r : BitVec 64} (hr : s.regs.get? .rip = some r)
    (asz : Nat) (eff : BitVec 64) (ha : eff.toNat < 2 ^ 47) {byte : BitVec 8}
    (hm : s.mem[eff.toNat]? = some byte) (k : String) :
    (rme08 .Mode_64bit asz eff none 1 k).run s = .ok byte s := by
  simp only [rme08]
  rw [run_load_bytes_from_ea h hr asz (by decide) eff none (by decide) k false (by omega)
    (fun _ => byte) (fun j hj => by
      have : j = 0 := by omega
      subst this; simpa using hm)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [sumLE]

end JanusX86.Proofs
