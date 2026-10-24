import Extracted
/-! ATTACK I1a (expected BLOCKED): the itab name in `ItabIs` has a Cyrillic `а` (U+0430) in
"MulHаsher". No data object has that name, so `ItabIs` is `False` and the theorem is vacuous; it
reads "HashWith(MulHasher) returns 0". -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
namespace Proof
theorem correctness (tab h x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [tab, h, x]
      (fun s => ItabIs Extracted.program.data s.mem tab
          "go:itab.*example.com/basic.MulHаsher,example.com/basic.Hasher" ∧ Ptr s.mem h 8 false)
      (fun s s' => s'.regs 0 = 0) := by
  intro ret hret s hs ⟨⟨d, hd, _⟩, _⟩
  have hn : dataNamed Extracted.program.data "go:itab.*example.com/basic.MulHаsher,example.com/basic.Hasher" = none := by rfl
  rw [hn] at hd; cases hd
end Proof
