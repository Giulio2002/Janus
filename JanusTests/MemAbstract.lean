import Janus

/-! # `janus_mem_abstract`: a store chain as a `MemFrame` and an atom (S16)

Opt-in. The stores of a path are proved to stay in their own ranges (`hf_mem0 : MemFrame m₀ M ranges`), the reads outside
them go to `m₀`, and a chain nothing reads any more is replaced by a fresh memory atom: the goal loses the chain. -/

namespace JanusTests.MemAbstract
open Janus Janus.Arm64 Janus.Tactic

/-- Two stack stores under reads of the inputs: the goal is size-independent of the stores afterwards. -/
example (m0 : Memory) (sp x : Nat) (hx : x + 8 ≤ sp - 16) (hsp : 16 ≤ sp) :
    ((((m0.writeLE (sp - 8) 8 (m0.readLE x 8)).writeLE (sp - 16) 8 5).readLE x 8 = m0.readLE x 8) ∧
      MemFrame m0 ((m0.writeLE (sp - 8) 8 (m0.readLE x 8)).writeLE (sp - 16) 8 5) [(sp - 16, sp)] ∧
      ((m0.writeLE (sp - 8) 8 (m0.readLE x 8)).writeLE (sp - 16) 8 5).accessible x 8 false = m0.accessible x 8 false) := by
  janus_mem_abstract
  -- the chain is gone from the goal
  run_tac do
    let t ← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)
    if (t.find? fun e => e.isAppOf ``Janus.Arm64.Memory.writeLE).isSome then
      Lean.throwError "the chain is still in the goal"
  refine ⟨trivial, ?_, trivial⟩
  exact hf_mem0.mono (by intro a n h; simp only [Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢; omega)

/- A stored value that is read back stays: the chain is kept (with the frame and the reads outside rewritten). -/
#guard_msgs (drop info) in
example (m0 : Memory) (sp x : Nat) (_hx : x + 8 ≤ sp - 16) (hsp : 16 ≤ sp) :
    ((m0.writeLE (sp - 8) 8 7).writeLE (sp - 16) 8 5).readLE (sp - 8) 8 = 7 := by
  janus_mem_abstract
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]

/-- No chain: an error. -/
example (m0 : Memory) (x : Nat) : m0.readLE x 8 = m0.readLE x 8 := by
  fail_if_success janus_mem_abstract
  rfl

end JanusTests.MemAbstract
