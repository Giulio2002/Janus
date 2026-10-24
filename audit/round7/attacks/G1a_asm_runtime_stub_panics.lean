import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-! Round 7 G1a: `main.Add` (audit/round7/asmstub) calls `lib.Zero`, whose Go-assembly body
calls `runtime·panicJanusR7`, an assembly function **of package lib** whose linker symbol is
`runtime.panicJanusR7`. It returns 0 (`MOVD $0, R0; RET`), so Add returns `x + y` (qemu prints 3).
No `-checklinkname=0` and no linkname are needed: the Go assembler lets any package define a
TEXT symbol in another package's namespace. Before round 7 the extractor took it for a panic stub
because its name is `runtime.panic…` with no `/`, and this theorem ("every call of Add panics")
verified. -/
namespace Proof
theorem correctness (x y : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s)
    (hg : GuardOK s 0) (hst : StackOK s 64 64) :
    Panics (Extracted.program.withExit ret) s := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  janus_run
end Proof
