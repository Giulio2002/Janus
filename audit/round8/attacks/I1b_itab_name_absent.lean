import Extracted
/-! ATTACK I1b (expected BLOCKED): an ASCII itab name the binary does not have (the value-receiver
itab `go:itab.example.com/basic.MulHasher,…`, no `*`). `ItabIs` is `False`; the theorem is
vacuous and reads "HashWith with a MulHasher returns 0". -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
namespace Proof
theorem correctness (tab h x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [tab, h, x]
      (fun s => ItabIs Extracted.program.data s.mem tab
          "go:itab.example.com/basic.MulHasher,example.com/basic.Hasher" ∧ Ptr s.mem h 8 false)
      (fun s s' => s'.regs 0 = 0) := by
  intro ret hret s hs ⟨⟨d, hd, _⟩, _⟩
  have hn : dataNamed Extracted.program.data "go:itab.example.com/basic.MulHasher,example.com/basic.Hasher" = none := by rfl
  rw [hn] at hd; cases hd
end Proof
