import Extracted

/-!
# `LoadThird(p *[4]uint64) uint64`: `LDR X0, [X0, #16]`, and its nil-dereference fault

**Guarantee (`correctness`).** For every pointer `p` and every Go call state of
`example.com/basic.LoadThird` with `p` in `X0` whose 8 bytes at `p + 16` are readable (in one
region, below `2^48`), the call returns, obeys the ABI, and returns the word at `p + 16` (`p[2]`).

**The nil case (`faults`).** Go emits no nil check here: for a field or element offset below the
4096-byte guard page the hardware fault is the check. For `p = nil` (`X0 = 0`) and any call state
whose memory maps nothing in the first page (every region starts at or above `4096`, as on Linux,
where `vm.mmap_min_addr` is at least `4096`), the first instruction faults: execution stops with
`outsideAllocation 16 8`, a load from address `16 < 4096`. The statement gives the fault at the
level of the machine (the faulting state is the call state; its instruction is ordinary code, not
the exit or a stub, and its step is an `outsideAllocation` error at an address below `4096`), and
also as `Faults` (`Janus.GoABI.Faults`). Turning such a fault into Go's nil-pointer panic
(`SIGSEGV` → `runtime.sigpanic` → `panicmem`) is the signal-delivery contract of the panic library,
which lifts exactly this statement shape.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p]
      (fun s => s.mem.accessible (p.toNat + 16) 8 false = true ∧ p.toNat + 16 + 8 ≤ 2 ^ 48)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE (p.toNat + 16) 8) := by
  intro ret hret s hs ⟨hacc, hlim⟩
  janus_intro hs
  janus_run

theorem faults :
    ∀ ret, RetAddr Extracted.program ret →
    ∀ s, CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s →
      (∀ r ∈ s.mem.regions, 4096 ≤ r.base) →
      (s.pc.toNat ≠ (Extracted.program.withExit ret).exitAddr ∧
        (Extracted.program.withExit ret).stubAt s.pc.toNat = none ∧
        ∃ w, (Extracted.program.withExit ret).fetch s.pc.toNat = some w ∧
          ∃ a n, Arm64.step w s = .error (.outsideAllocation a n) ∧ a < 4096) ∧
      Faults (Extracted.program.withExit ret) s := by
  intro ret hret s hs hpage
  have h0 : s.regs 0 = 0#64 := hs.args 0 (by decide)
  have hpcn : s.pc.toNat = Extracted.entry := by rw [hs.pc, BitVec.toNat_ofNat]; rfl
  have hfetch : (Extracted.program.withExit ret).fetch s.pc.toNat = some 0xf9400800 := by
    rw [hpcn]; rfl
  have hna : s.mem.accessible 16 8 false = false := by
    unfold Memory.accessible
    simp only [Bool.and_eq_false_iff]
    left
    rw [List.any_eq_false]
    intro r hr
    have := hpage r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h1; omega
  have hstep : Arm64.step 0xf9400800 s = .error (.outsideAllocation 16 8) := by
    rw [step_of_decode (i := .ldstUImm 3 1 2 0 0) (by decide)]
    simp only [exec]
    unfold memIndexed baseAddr memSingle load
    simp only [reduceIte, Nat.reduceEqDiff, Bool.false_eq_true, ite_false, h0]
    rw [show ((0#64 : BitVec 64) + BitVec.ofNat 64 (2 * 2 ^ 3)).toNat = 16 from by decide,
      show (2 : Nat) ^ 3 = 8 from rfl, hna]
    rfl
  have hx : s.pc.toNat ≠ (Extracted.program.withExit ret).exitAddr := by
    rw [hpcn, Program.exitAddr_withExit]
    exact hret.ne_of_fetch (pc := Extracted.entry) (w := 0xf9400800) (by rfl)
  have hst : (Extracted.program.withExit ret).stubAt s.pc.toNat = none := by rw [hpcn]; rfl
  refine ⟨⟨hx, hst, 0xf9400800, hfetch, 16, 8, hstep, by decide⟩, ?_⟩
  exact faults_of_steps (Program.Steps.refl s) hx hst hfetch hstep (by simp)

end Proof
