import Janus
import Extracted

/-!
# `LoadThird(p *[4]uint64) uint64` on amd64: `MOVQ 0x10(AX), AX`, and its nil-dereference fault

**Guarantee (`correctness`).** For every pointer `p` in `RAX` whose 8 bytes at `p + 16` are
readable (one region, below `2^48`) and every Go call state with 8 readable bytes at `RSP`, the
call returns, obeys the ABI, and returns the word at `p + 16` (`p[2]`).

**The nil case (`faults`).** For `p = nil` and memory that maps nothing below `4096` (every
region starts at or above `4096`), the first instruction faults with `outsideAllocation 16 8`: a
load from address `16 < 4096`. As on arm64 the statement gives the faulting instruction (the
call state's, ordinary code) and its `outsideAllocation` error below `4096`, and `Faults`; the
signal-to-panic conversion (`SIGSEGV` → `runtime.sigpanic`) is the panic library's.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p]
      (fun s => StackWritable s 0 8 ∧ s.mem.accessible (p.toNat + 16) 8 false = true ∧
        p.toNat + 16 + 8 ≤ 2 ^ 48)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE (p.toNat + 16) 8) := by
  intro ret hret s hs ⟨hst, hacc', hlim⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run

theorem faults :
    ∀ ret, RetAddr Extracted.program ret →
    ∀ s, CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s →
      (∀ r ∈ s.mem.regions, 4096 ≤ r.base) →
      (s.rip.toNat ≠ (Extracted.program.withExit ret).exitAddr ∧
        (Extracted.program.withExit ret).stubAt s.rip.toNat = none ∧
        ∃ w, (Extracted.program.withExit ret).fetch s.rip.toNat = some w ∧
          ∃ a n, Janus.Amd64.step w s = .error (Fault.outsideAllocation a n) ∧ a < 4096) ∧
      Faults (Extracted.program.withExit ret) s := by
  intro ret hret s hs hpage
  have h0 : s.regs 0 = 0#64 := hs.args 0 (by decide)
  have hpcn : s.rip.toNat = Extracted.entry := by rw [hs.rip, BitVec.toNat_ofNat]; rfl
  have hfetch : (Extracted.program.withExit ret).fetch s.rip.toNat = some [0x48, 0x8b, 0x40, 0x10, 0xc3] := by
    rw [hpcn]; rfl
  have hna : s.mem.accessible 16 8 false = false := by
    unfold Janus.Arm64.Memory.accessible
    simp only [Bool.and_eq_false_iff]
    left
    rw [List.any_eq_false]
    intro r hr
    have := hpage r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h1; omega
  have hstep : Janus.Amd64.step [0x48, 0x8b, 0x40, 0x10, 0xc3] s = .error (Fault.outsideAllocation 16 8) := by
    have hd : decode [0x48, 0x8b, 0x40, 0x10, 0xc3] = some (.mov 64 (Loc.reg 0) (Src.loc (Loc.mem
      ⟨some 0, none, 0, 16, false, false⟩)), 4) := by decide
    rw [step_of_decode hd]
    have he : (eaOff s (BitVec.ofNat 64 ((BitVec.toNat s.rip + 4) % 2 ^ 64))
        { base := some 0, index := none, scale := 0, disp := 16, rip := false }).toNat = 16 := by
      simp only [eaOff, h0, Bool.false_eq_true, ite_false]; decide
    simp only [exec, readSrc, readLoc, ea, Bool.false_eq_true, ite_false, he, load,
      show 64 / 8 = 8 from rfl, hna]
  have hx : s.rip.toNat ≠ (Extracted.program.withExit ret).exitAddr := by
    rw [hpcn, Program.exitAddr_withExit]
    exact hret.ne_of_fetch (pc := Extracted.entry) (w := [0x48, 0x8b, 0x40, 0x10, 0xc3]) (by rfl)
  have hst : (Extracted.program.withExit ret).stubAt s.rip.toNat = none := by rw [hpcn]; rfl
  refine ⟨⟨hx, hst, _, hfetch, 16, 8, hstep, by decide⟩, 1, _, Program.run_succ_fault hx hst hfetch hstep,
    by simp⟩

end Proof
