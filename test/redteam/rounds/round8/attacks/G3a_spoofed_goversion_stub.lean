import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-! ATTACK G3a (expected BLOCKED): `main.Add` of audit/round8/govers returns `x + y` (qemu prints
3). The binary was linked by go1.25.5, whose runtime has no `panicSimdImm`, so the package-lib
assembly function `runtime·panicSimdImm` (it returns 0) is the only symbol of that name, and
`-ldflags=-X runtime.buildVersion=go1.26.0` labels the binary go1.26. Round 7's gate read the
version from build info and took the function for the go1.26 panic stub, so "every call of Add
panics" verified. -/
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
