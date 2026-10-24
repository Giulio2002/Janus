import JanusX86.Proofs.Flags
import JanusX86.Proofs.Gpr

/-! # Janus amd64 states against Sail x86 states

`Rel js s`: the Sail state `s` holds Janus' architectural state `js` for the integer subset:
the 16 GPRs, `RIP`, the six status flags where Janus defines them (`FlagsRel`; undefined ones
are unrelated), `DF`, `RFLAGS.AC = 0`, the `FS` base (`IA32_FS_BASE`, `msrs[1]`), and every byte
Janus can read. Janus' memory regions lie below `2^47` (canonical lower-half addresses: every
real user mapping does, docs/AMD64.md), so every Janus access is canonical for the model.
Everything else in `s` is unconstrained (other bytes, vector registers, segment state beyond
`X86Config`, the undefined-value source). -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

structure Rel (js : Janus.Amd64.State) (s : SState) : Prop where
  gpr : ∀ i < 16, gprVal s i = some (js.regs i)
  rip : s.regs.get? .rip = some js.rip
  flags : ∃ r, s.regs.get? .rflags = some r ∧ FlagsRel js.flags js.df r
  fs : ∃ v : Vector (BitVec 64) 7, s.regs.get? .msrs = some v ∧ GetElem?.getElem! v 1 = js.fsBase
  mem : ∀ a, js.mem.accessible a 1 false = true → s.mem[a]? = some (js.mem.bytes a)
  canon : ∀ r ∈ js.mem.regions, r.base + r.size ≤ 2 ^ 47

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem gprVal_setGpr (s : SState) {r : Nat} (hr : r < 16) (v : BitVec 64) {i : Nat} (hi : i < 16) :
    gprVal (setGpr s v r) i = if i = r then some v else gprVal s i := by
  split
  · subst_vars; exact gprVal_setGpr_same s hr v
  · exact gprVal_setGpr_ne s hr hi (by assumption) v

theorem setGpr_mem (s : SState) (v : BitVec 64) (r : Nat) : (setGpr s v r).mem = s.mem := by
  unfold setGpr; split <;> rfl

theorem Rel.setReg {js : Janus.Amd64.State} {s : SState} (h : Rel js s) {r : Nat} (hr : r < 16)
    (v : BitVec 64) : Rel (js.setReg r v) (setGpr s v r) := by
  obtain ⟨f, hf, hfr⟩ := h.flags
  obtain ⟨m, hm, hmr⟩ := h.fs
  refine ⟨?_, ?_, ⟨f, ?_, hfr⟩, ⟨m, ?_, hmr⟩, ?_, h.canon⟩
  · intro i hi
    rw [gprVal_setGpr s hr v hi]
    simp only [Janus.Amd64.State.setReg]
    split
    · simp_all
    · simp_all [h.gpr i hi]
  · rw [get?_setGpr_of_not s v hr (by rfl)]; exact h.rip
  · rw [get?_setGpr_of_not s v hr (by rfl)]; exact hf
  · rw [get?_setGpr_of_not s v hr (by rfl)]; exact hm
  · intro a ha; rw [setGpr_mem]; exact h.mem a ha

theorem X86Config.set {s : SState} (h : X86Config s) {r : Register}
    (hr : r ∉ [Register.ms_reg, .fault_reg, .app_view, .log_register_writes, .janus_undef, .msrs,
      .seg_hidden_attrs, .seg_visibles, .ctrs]) (v : RegisterType r) : X86Config (s.set r v) := by
  obtain ⟨u, hu⟩ := h.undef
  obtain ⟨a, ha, ha'⟩ := h.efer
  obtain ⟨b, hb, hb'⟩ := h.csl
  obtain ⟨c, hc, hc'⟩ := h.cpl
  obtain ⟨d, hd, hd'⟩ := h.ctrs
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hr
  exact ⟨by rw [get?_set_ne _ _ r1]; exact h.ms, by rw [get?_set_ne _ _ r2]; exact h.fault,
    by rw [get?_set_ne _ _ r3]; exact h.app, by rw [get?_set_ne _ _ r4]; exact h.log,
    ⟨u, by rw [get?_set_ne _ _ r5]; exact hu⟩, ⟨a, by rw [get?_set_ne _ _ r6]; exact ha, ha'⟩,
    ⟨b, by rw [get?_set_ne _ _ r7]; exact hb, hb'⟩, ⟨c, by rw [get?_set_ne _ _ r8]; exact hc, hc'⟩,
    ⟨d, by rw [get?_set_ne _ _ r9]; exact hd, hd'⟩⟩

theorem X86Config.setGpr {s : SState} (h : X86Config s) {r : Nat} (hr : r < 16) (v : BitVec 64) :
    X86Config (setGpr s v r) := by
  obtain ⟨u, hu⟩ := h.undef
  obtain ⟨a, ha, ha'⟩ := h.efer
  obtain ⟨b, hb, hb'⟩ := h.csl
  obtain ⟨c, hc, hc'⟩ := h.cpl
  obtain ⟨d, hd, hd'⟩ := h.ctrs
  have e := fun (x : Register) (hx : isGprReg x = false) => get?_setGpr_of_not s v hr hx
  exact ⟨by rw [e _ rfl]; exact h.ms, by rw [e _ rfl]; exact h.fault, by rw [e _ rfl]; exact h.app,
    by rw [e _ rfl]; exact h.log, ⟨u, by rw [e _ rfl]; exact hu⟩, ⟨a, by rw [e _ rfl]; exact ha, ha'⟩,
    ⟨b, by rw [e _ rfl]; exact hb, hb'⟩, ⟨c, by rw [e _ rfl]; exact hc, hc'⟩, ⟨d, by rw [e _ rfl]; exact hd, hd'⟩⟩

end JanusX86.Proofs
