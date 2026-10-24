import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-! Round 7 G1c (control): on the round-7 extraction of `main.Add` (audit/round7/asmstub),
`runtime.panicJanusR7` is ordinary code, and Add returns `x + y`, as it does on hardware. -/
namespace Proof
theorem correctness (x y : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s)
    (hg : GuardOK s 0) (hst : StackOK s 64 64) :
    Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ s'.regs 0 = x + y) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  janus_run
  exact BitVec.add_comm y x
end Proof
