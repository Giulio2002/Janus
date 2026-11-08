import Janus
import Extracted

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Kernel Janus.Amd64.Kernel

namespace Proof

theorem correctness (E : KEnv) :
    EnsuresK Extracted.program E Extracted.entry []
      (fun s _ => StackGuardOK s 0 ∧ StackWritable s 64 8 ∧ TlsG s ∧
        (s.fsBase.toNat ≤ (s.regs regSP).toNat - 64 ∨ (s.regs regSP).toNat + 16 ≤ s.fsBase.toNat))
      (fun _ k s' k' => k' = k ∧ s'.regs 0 = BitVec.ofNat 64 k.pid) := by
  intro ret hret s k hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, ha, hw⟩, ⟨htb, htr, htg⟩, htd⟩
  apply Janus.Amd64.Kernel.ReturnsK.of_reaches
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb ha hw htg htd
  janus64_run
  refine ⟨.syscall, by rw [Amd64.Kernel.siteOf_withExit]; decide,
    Or.inl ⟨⟨.getpid, ?_, by decide, trivial⟩, ?_⟩⟩
  · simp [sysOf, Sys.ofAmd64, setRegF]
  rintro s' k' ⟨sc, m', r, r11, hsc, heff, rfl⟩
  simp [sysOf, Sys.ofAmd64, setRegF] at hsc
  subst hsc
  obtain ⟨rfl, rfl, rfl⟩ := heff
  apply Janus.Amd64.Kernel.ReturnsK.of_reaches
  janus64_run
  exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_ofNat])

namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def tls0 : Nat := 0x400000

def bytes (a : Nat) : Byte := if a = sp0 + 2 then 0x20 else if a = tls0 + 2 then 0x30 else 0

def s0 : Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨g0, 0x100, false⟩, ⟨tls0, 0x100, false⟩]⟩,
    fsBase := BitVec.ofNat 64 (tls0 + 8) }

def k0 : Kern := {}
def E0 : KEnv := ⟨[], 1024⟩

/-- Fixes the types of the witness's kernel environment and kernel state in the printed statement. -/
def pin (_E : KEnv) (_k : Kern) : Prop := True

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h, rfl⟩

theorem pre : StackGuardOK s0 0 ∧ StackWritable s0 64 8 ∧ TlsG s0 ∧
    (s0.fsBase.toNat ≤ (s0.regs regSP).toNat - 64 ∨ (s0.regs regSP).toNat + 16 ≤ s0.fsBase.toNat) := by
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide⟩

/-- The theorem fires: `Getpid()` returns the kernel's pid. -/
theorem returns : Amd64.Kernel.ReturnsK (Extracted.program.withExit ret) E0
    (fun s' k' => ABIReturn s0 s' ∧ (k' = k0 ∧ s'.regs 0 = BitVec.ofNat 64 k0.pid))
    (fun _ _ => False) s0 k0 :=
  correctness E0 ret hret s0 k0 setup pre

/-- All the hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (E : KEnv) (ret : Nat) (s : Amd64.State) (k : Kern), pin E k ∧
    RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 64 8 ∧ TlsG s ∧
      (s.fsBase.toNat ≤ (s.regs regSP).toNat - 64 ∨ (s.regs regSP).toNat + 16 ≤ s.fsBase.toNat)) ∧
    Amd64.Kernel.ReturnsK (Extracted.program.withExit ret) E
      (fun s' k' => ABIReturn s s' ∧ (k' = k ∧ s'.regs 0 = BitVec.ofNat 64 k.pid))
      (fun _ _ => False) s k :=
  ⟨E0, ret, s0, k0, trivial, hret, setup, pre, returns⟩

end Witness

end Proof
