import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-! Round 6 F3a: `main.Add` (audit/round6/stubmod) calls `runtime.panicky/lib.Zero`, an ordinary
function in a package whose import path starts with `runtime.panic`. Before round 6 the
extractor classified it as a panic stub by symbol-name prefix, so this theorem ("every call of
Add panics") verified, while the real Add returns `x + y`. Round 6 classifies stubs only in
package `runtime` itself, so `Zero` is extracted as code and this proof no longer checks. -/
namespace Proof
theorem correctness (x y : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 24) :
    Panics (Extracted.program.withExit ret) s := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  janus_run
end Proof
