import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E3d: a proof-local def in the `Janus.Arm64.State` namespace, so field notation prints
it like a Janus field (`s'.result`). It is a plain def, so it is disclosed with its body and
round-tripped; expected Verified with `Janus.Arm64.State.result` shown in the definitions. -/
def Janus.Arm64.State.result (s : Janus.Arm64.State) : BitVec 64 := s.regs 0
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.result = x + y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  rfl
end Proof
