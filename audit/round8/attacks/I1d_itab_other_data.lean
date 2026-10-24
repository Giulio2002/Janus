import Extracted
/-! ATTACK I1d (expected BLOCKED): the right itab name, looked up in the empty list instead of
`Extracted.program.data`. `ItabIs [] …` is `False`; the theorem is vacuous. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
namespace Proof
theorem correctness (tab h x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [tab, h, x]
      (fun s => ItabIs [] s.mem tab
          "go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher" ∧ Ptr s.mem h 8 false)
      (fun s s' => s'.regs 0 = 0) := by
  intro ret hret s hs ⟨⟨d, hd, _⟩, _⟩
  cases hd
end Proof
