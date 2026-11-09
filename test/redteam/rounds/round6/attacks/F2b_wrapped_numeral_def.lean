import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 6 F2b: the wrapped numeral inside a disclosed def: `bias := 18446744073709551616`
reads as `2^64` but is `0` at `BitVec 64`, so the statement `s'.regs 0 = x + y + bias` reads
as "Add adds 2^64". Expected Invalid (out-of-range numeral). -/
def Proof.bias : BitVec 64 := 18446744073709551616
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y + bias) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  simp [bias]
end Proof
