import Extracted
/-! ATTACK: a proof module declares its own `Extracted.dataAddr.«…»` constant (a data symbol the binary
does not have, or a lookalike) and states a theorem about the program using it. The name lives in the
reserved `Extracted` namespace, which only the generated module may declare. -/
open Janus Janus.Arm64 Janus.GoABI
def Extracted.dataAddr.«example.com/basic.other» : Nat := 0x1000
namespace Proof
theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i]
      (fun s => s.mem.accessible Extracted.dataAddr.«example.com/basic.other» 8 false = true)
      (fun _ _ => True) := by
  sorry
end Proof
