import JanusX86.Proofs.Monad

/-! # `X86Config`: the configuration the class theorems assume

The analogue of JanusASL's `LinuxEL0Config`: the part of the Sail x86 state that the
64-bit application-level path of `x86_fetch_decode_execute` reads and that is not Janus
architectural state. `janus_x86_init` (JanusX86/sail/harness.sail) establishes it, and
`janus-x86-check` checks the Boolean version `cfgOk` on the base state and on every case's pre-
and post-states (docs/X86FORMAL.md).

* no machine-status or fault flag is pending (`ms_reg`, `fault_reg`; `x86_fetch_decode_execute`
  does nothing when one is set), and register-write logging is off (`write_gpr` and `write_rip`
  read `log_register_writes`), and the undefined-value source `janus_undef` is set (any value);
* the application-level memory view (`app_view`: linear address = physical address, no paging
  structures);
* 64-bit mode: `IA32_EFER.LMA` (bit 10 of `msrs[0]`) and `CS.L` (bit 9 of the hidden CS
  attributes) set;
* CPL 3 (`CS.RPL` = 3);
* `CR4.OSFXSR` (bit 9 of `ctrs[4]`) set, as Linux does (the SSE instructions `#UD` otherwise);
* `CR0.AM` (bit 18 of `ctrs[0]`) clear, so the model never alignment-checks an integer access
  (Linux sets AM, but with `RFLAGS.AC = 0`, which Go code never changes, no access is
  alignment-checked either: `alignment_checking_enabled_p` needs both).

Each field is stated with the model's own accessors (`_get_ia32_eferbits_lma`, ...), exactly as the
model reads it, so that the evaluation lemmas need no bit-field bridging.
-/

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

structure X86Config (s : SState) : Prop where
  ms : s.regs.get? .ms_reg = some false
  fault : s.regs.get? .fault_reg = some false
  app : s.regs.get? .app_view = some true
  log : s.regs.get? .log_register_writes = some false
  undef : ∃ u, s.regs.get? .janus_undef = some u
  efer : ∃ v : Vector (BitVec 64) 7, s.regs.get? .msrs = some v ∧
    _get_ia32_eferbits_lma (Mk_ia32_eferbits (Sail.BitVec.truncate (GetElem?.getElem! v 0) 12)) = 1#1
  csl : ∃ v : Vector (BitVec 16) 6, s.regs.get? .seg_hidden_attrs = some v ∧
    _get_code_segment_descriptor_attributesbits_l (Mk_code_segment_descriptor_attributesbits
      (GetElem?.getElem! v 1)) = 1#1
  cpl : ∃ v : Vector (BitVec 16) 6, s.regs.get? .seg_visibles = some v ∧
    _get_segment_selectorbits_rpl (Mk_segment_selectorbits (GetElem?.getElem! v 1)) = 3#2
  ctrs : ∃ v : Vector (BitVec 64) 17, s.regs.get? .ctrs = some v ∧
    _get_cr4bits_osfxsr (Mk_cr4bits (loghead_bits 22 (GetElem?.getElem! v 4))) = 1#1 ∧
    _get_cr0bits_am (Mk_cr0bits (Sail.BitVec.truncate (GetElem?.getElem! v 0) 32)) = 0#1

/-- The Boolean version, evaluated by `janus-x86-check`. -/
def cfgOk (s : SState) : Bool :=
  s.regs.get? .ms_reg == some false && s.regs.get? .fault_reg == some false &&
  s.regs.get? .app_view == some true && s.regs.get? .log_register_writes == some false &&
  (s.regs.get? .janus_undef).isSome &&
  (match s.regs.get? .msrs with
    | some v => _get_ia32_eferbits_lma (Mk_ia32_eferbits (Sail.BitVec.truncate (GetElem?.getElem! v 0) 12)) == 1#1
    | none => false) &&
  (match s.regs.get? .seg_hidden_attrs with
    | some v => _get_code_segment_descriptor_attributesbits_l (Mk_code_segment_descriptor_attributesbits
        (GetElem?.getElem! v 1)) == 1#1
    | none => false) &&
  (match s.regs.get? .seg_visibles with
    | some v => _get_segment_selectorbits_rpl (Mk_segment_selectorbits (GetElem?.getElem! v 1)) == 3#2
    | none => false) &&
  (match s.regs.get? .ctrs with
    | some v => _get_cr4bits_osfxsr (Mk_cr4bits (loghead_bits 22 (GetElem?.getElem! v 4))) == 1#1 &&
        _get_cr0bits_am (Mk_cr0bits (Sail.BitVec.truncate (GetElem?.getElem! v 0) 32)) == 0#1
    | none => false)

theorem cfgOk_sound {s : SState} (h : cfgOk s = true) : X86Config s := by
  simp only [cfgOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h0⟩, hu⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h0, ?_, ?_, ?_, ?_, ?_⟩
  · revert hu; cases s.regs.get? .janus_undef <;> simp
  · revert h4; cases s.regs.get? .msrs <;> simp
  · revert h5; cases s.regs.get? .seg_hidden_attrs <;> simp
  · revert h6; cases s.regs.get? .seg_visibles <;> simp
  · revert h7; cases s.regs.get? .ctrs <;> simp

end JanusX86.Proofs
