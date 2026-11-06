import Janus

/-! # `janus_grab`: content-based lookup of facts, and the `rename_i` linter (`janusRenameI`) -/

namespace JanusTests.Grab
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

example (s st : State) (rs : List (Nat × Nat)) (a : Nat) (_h0 : a < 7) (hfr : MemFrame s.mem st.mem rs)
    (h3 : st.regs 3 = 5#64) (h4 : st.regs 4 = 6#64) : st.regs 3 = 5#64 ∧ st.regs 4 = 6#64 := by
  -- by constant: the first hypothesis mentioning `MemFrame`
  janus_grab MemFrame as f1
  have : MemFrame s.mem st.mem rs := f1
  -- by projection of the returned state of the callee with frame `hfr`, whatever the order of the other hypotheses
  janus_grab hfr regs 4 as g4
  janus_grab hfr regs 3 as g3
  exact ⟨g3, g4⟩

example (s st : State) (a : Nat) (hfr : MemFrame s.mem st.mem [(a - 112 - 4096, a - 112)]) (_h : a = 3) :
    MemFrame s.mem st.mem [(a - 112 - 4096, a - 112)] := by
  janus_grab 112 as f
  exact f

/-- error: janus_grab: no MemFrame hypothesis mentions 8 -/
#guard_msgs in
example (s st : State) (a : Nat) (hfr : MemFrame s.mem st.mem [(a - 112, a)]) : True := by
  janus_grab 8 as f
  trivial

/-- error: janus_grab: no hypothesis st.regs 9 = _ for the state of hfr -/
#guard_msgs in
example (s st : State) (hfr : MemFrame s.mem st.mem []) (h : st.regs 3 = 5#64) : True := by
  janus_grab hfr regs 9 as f
  trivial

def seg : Segment := ⟨"f", 0x1000, [0xf100001f, 0x54000060, 0xd2800021, 0x14000002, 0xd2800041, 0x91000422, 0xd65f03c0]⟩
def P : Program := { segments := [seg], stubs := [], exitAddr := 0 }

/-- warning: positional `rename_i` after `janus_run` re-binds names silently when a callee's contract gains or reorders a conjunct: select the hypothesis by content with `janus_grab c as h`, `janus_grab 112 as h` or `janus_grab fr f i as h`

Note: This linter can be disabled with `set_option linter.janusRenameI false`
-/
#guard_msgs in
theorem warned (x : W64) (_h : x.toNat < 5) :
    Ensures P 0x1000 [x] (fun _ => True) (fun _ s' => s'.regs 2 = if x = 0 then 3 else 2) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run join [0x1014]
  rename_i y
  rcases hjoin with ⟨⟨hx, -⟩, rfl, -⟩ | ⟨⟨hx, -⟩, rfl, -⟩ <;> simp_all [BitVec.toNat_eq]

#guard_msgs in
theorem notWarned (x : W64) (_h : x.toNat < 5) :
    Ensures P 0x1000 [x] (fun _ => True) (fun _ s' => s'.regs 2 = if x = 0 then 3 else 2) := by
  intro ret hret s hs _
  rename_i y
  janus_intro hs
  janus_run join [0x1014]
  rcases hjoin with ⟨⟨hx, -⟩, rfl, -⟩ | ⟨⟨hx, -⟩, rfl, -⟩ <;> simp_all [BitVec.toNat_eq]

end JanusTests.Grab
