import Janus
import Extracted

/-! `example.com/basic.LoadField(c)` on amd64: a nil receiver dereference (`MOVQ 0(AX), AX` with
`AX = 0`) faults, which Go turns into a nil-pointer panic via `sigpanic`. Example 5 of
docs/COVERAGE.md R6. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.PanicAmd64

theorem correctness (P : Spec.PanicRuntime) :
    EnsuresGo Extracted.program Extracted.entry [0#64]
      (fun s => s.mem.accessible 0 8 false = false)
      (fun _ => goClass P)
      (fun _ _ => True)
      (fun _ v _ => v = P.err Spec.ErrKind.mem) := by
  intro ret hret s hs hna
  have h0 : s.regs 0 = 0#64 := hs.args 0 (by decide)
  have hrip : s.rip = BitVec.ofNat 64 Extracted.entry := hs.rip
  have hripn : s.rip.toNat = Extracted.entry := by rw [hrip, BitVec.toNat_ofNat]; rfl
  have hfetch : (Extracted.program.withExit ret).fetch s.rip.toNat = some [0x48, 0x8b, 0x00, 0xc3] := by
    rw [hripn]; rfl
  have hstep : Amd64.step [0x48, 0x8b, 0x00, 0xc3] s = .error (.outsideAllocation 0 8) := by
    rw [step_of_decode (by decide : decode [0x48, 0x8b, 0x00, 0xc3]
        = some (.mov 64 (.reg 0) (.loc (.mem ⟨some 0, none, 0, 0, false, false⟩)), 3)) s]
    simp only [exec, readSrc, readLoc, ea, eaOff, h0, Bool.false_eq_true, if_false,
      reduceCtorEq, BitVec.zero_add, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reduceDiv]
    rw [show (BitVec.toNat (0 : BitVec 64)) = 0 from rfl, load, if_neg (by rw [hna]; decide)]
  refine GoReturns.fault (Janus.Amd64.Program.Steps.refl s) ⟨?_, ?_, [0x48, 0x8b, 0x00, 0xc3], hfetch, hstep⟩
    (goClass_nil P s (by decide)) rfl
  · rw [hripn, Janus.Amd64.Program.exitAddr_withExit]
    exact hret.ne_of_fetch (pc := Extracted.entry) (w := [0x48, 0x8b, 0x00, 0xc3]) (by rfl)
  · rw [hripn]; rfl

end Proof
