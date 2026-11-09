import Janus

/-! # The `‹T›` / `assumption` after `janus_run` warning (linter `janusAssumption`)

Reported only: the proof elaborates exactly as before. `janus_assumption` and the text before the first `janus_run` are not flagged. -/

namespace JanusTests.AssumptionLint
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

def seg : Segment := ⟨"f", 0x1000, [0xf100001f, 0x54000060, 0xd2800021, 0x14000002, 0xd2800041, 0x91000422, 0xd65f03c0]⟩
def P : Program := { segments := [seg], stubs := [], exitAddr := 0 }

/-- warning: `‹T›`/`assumption` after `janus_run` tries every hypothesis at default transparency and can cost minutes in the large context of a run: use `by janus_assumption` (or `janus_assumption_reducible` in a `first`)

Note: This linter can be disabled with `set_option linter.janusAssumption false`
-/
#guard_msgs in
theorem warned (x : W64) (h : x.toNat < 5) :
    Ensures P 0x1000 [x] (fun _ => True) (fun _ s' => s'.regs 2 = if x = 0 then 3 else 2) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run join [0x1014]
  have : x.toNat < 5 := ‹_›
  rcases hjoin with ⟨⟨hx, -⟩, rfl, -⟩ | ⟨⟨hx, -⟩, rfl, -⟩ <;> simp_all [BitVec.toNat_eq]

#guard_msgs in
theorem notWarned (x : W64) (h : x.toNat < 5) :
    Ensures P 0x1000 [x] (fun _ => True) (fun _ s' => s'.regs 2 = if x = 0 then 3 else 2) := by
  intro ret hret s hs _
  have : x.toNat < 5 := ‹_›
  janus_intro hs
  janus_run join [0x1014]
  have : x.toNat < 5 := by janus_assumption
  rcases hjoin with ⟨⟨hx, -⟩, rfl, -⟩ | ⟨⟨hx, -⟩, rfl, -⟩ <;> simp_all [BitVec.toNat_eq]

set_option linter.janusAssumption false in
#guard_msgs in
theorem disabled (x : W64) (h : x.toNat < 5) :
    Ensures P 0x1000 [x] (fun _ => True) (fun _ s' => s'.regs 2 = if x = 0 then 3 else 2) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run join [0x1014]
  have : x.toNat < 5 := ‹_›
  rcases hjoin with ⟨⟨hx, -⟩, rfl, -⟩ | ⟨⟨hx, -⟩, rfl, -⟩ <;> simp_all [BitVec.toNat_eq]

end JanusTests.AssumptionLint
