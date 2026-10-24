import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-! Round 7 G1b: `main.Inc` (audit/round7/asmstub) calls `lib.Boom`, whose Go-assembly body
calls `runtime·morestackJanusR7`, an assembly function **of package lib** that calls a Go
function doing `panic("boom")`. Before round 7 the extractor took it for a `morestack` stub
(its symbol starts with `runtime.morestack`, with no `/`), and `NeverPanics` allows reaching
`morestack`, so "Inc never panics" verified while every call of Inc panics on hardware (qemu
prints `panic: boom`). -/
namespace Proof
theorem growsStack (x : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s)
    (hg : GuardOK s 0) (hst : StackOK s 256 256) :
    GrowsStack (Extracted.program.withExit ret) s := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  janus_run

theorem correctness (x : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s)
    (hg : GuardOK s 0) (hst : StackOK s 256 256) :
    NeverPanics (Extracted.program.withExit ret) s := by
  obtain ⟨m, name, s₁, hm⟩ := growsStack x ret hret s hs hg hst
  intro n
  refine ⟨fun name' s' h => ?_, fun e h => ?_⟩
  · cases Program.run_ok_unique hm h
  · by_cases he : e = .outOfFuel
    · exact he
    · exact (Program.run_ok_not_error hm h he).elim
end Proof
