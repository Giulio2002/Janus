import Janus
import Extracted

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel

namespace Proof

/-- `syscall.errEAGAIN`, `errEINVAL`, `errENOENT` (`.data`, 16 bytes each, contiguous). -/
def errVars : Nat := 0x54fc80

set_option hygiene false in
/-- After the `write` system call: the two kernel outcomes, each run on to the return. -/
macro "after_write" : tactic => `(tactic| (
  rintro s' k' ⟨sc, m', r, r11, hsc, heff, rfl⟩
  simp [sysOf, Sys.ofAmd64, setRegF] at hsc
  subst hsc
  simp only [Effect, Amd64.Kernel.argsOf, setRegF] at heff
  obtain ⟨rfl, ⟨c, hc, rfl, rfl⟩ | ⟨⟨he1, he2⟩, rfl⟩⟩ := heff
  · simp [setRegF] at hc
    apply Amd64.Kernel.ReturnsK.of_reaches
    janus64_run calls [hent, hexit, hconv]
  · apply Amd64.Kernel.ReturnsK.of_reaches
    janus64_run calls [hent, hexit, hconv]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hent : Amd64.Kernel.SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.entersyscall") rt 1024)
    (hexit : Amd64.Kernel.SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.exitsyscall") rt 1024)
    (hconv : Amd64.Kernel.ConvT64Contract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") rt 1024)
    (ptr len cap : BitVec 64) :
    Amd64.Kernel.EnsuresK (Extracted.program.link impl) E Extracted.entry [ptr, len, cap]
      (fun s _ => StackGuardOK s 48 ∧ StackWritable s 1232 16 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Outside ((s.regs 4).toNat - 1232) 1248 rt ∧
        Buf s.mem ptr.toNat len.toNat false ∧ len.toNat ≤ 2 ^ 48 ∧ Outside ptr.toNat len.toNat rt ∧
        (ptr.toNat + len.toNat ≤ (s.regs 4).toNat - 1232 ∨ (s.regs 4).toNat + 16 ≤ ptr.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 1232 ∨ (s.regs 4).toNat + 16 ≤ (s.regs 14).toNat + 16) ∧
        s.mem.accessible errVars 48 false = true ∧
        (errVars + 48 ≤ (s.regs 4).toNat - 1232 ∨ (s.regs 4).toNat + 16 ≤ errVars))
      (fun _ _ _ _ => True) := by
  intro ret hret s k hs ⟨hg, ⟨hb, ha, hw⟩, hal, hout, hbuf, hlen, hbo, hbd, hgd, herr, hed⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, errVars] at hgl hgb hnw2 hgr hb ha hw hout hal herr hed ⊢
  apply Amd64.Kernel.ReturnsK.of_reaches
  janus64_intro hs
  janus64_run calls [hent, hexit, hconv]
  all_goals refine ⟨.syscall, by kernel_site64, Or.inl ⟨⟨.write, by simp [sysOf, Sys.ofAmd64, setRegF], by decide, ?_⟩, ?_⟩⟩
  · simp [Safe, Buf, Amd64.Kernel.argsOf, setRegF]
  · after_write
  · simp [Safe, Buf, Amd64.Kernel.argsOf, setRegF]
    rcases hbuf with h0 | hacc
    · exact Or.inl h0
    · right; rw [(‹MemFrame _ _ _›).accessible]; simpa using hacc
  · after_write

end Proof
