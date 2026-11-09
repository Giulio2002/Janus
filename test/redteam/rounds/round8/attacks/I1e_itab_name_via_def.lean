import Extracted
/-! ATTACK I1e (expected BLOCKED): the lookalike name reaches `ItabIs` through the parameter of
a proof-local definition (`IsHasher m tab "…MulHаsher…"`, Cyrillic `а`). Checked after the
definition is expanded. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
namespace Proof
def IsHasher (m : Memory) (tab : BitVec 64) (n : String) : Prop :=
  ItabIs Extracted.program.data m tab n
theorem correctness (tab h x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [tab, h, x]
      (fun s => IsHasher s.mem tab "go:itab.*example.com/basic.MulHаsher,example.com/basic.Hasher" ∧
        Ptr s.mem h 8 false)
      (fun s s' => s'.regs 0 = 0) := by
  intro ret hret s hs ⟨⟨d, hd, _⟩, _⟩
  have hn : dataNamed Extracted.program.data "go:itab.*example.com/basic.MulHаsher,example.com/basic.Hasher" = none := by rfl
  rw [hn] at hd; cases hd
end Proof
