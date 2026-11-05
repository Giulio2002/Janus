import Janus

/-! # `janus_data hd [hw]` / `janus64_data hd [hw]` require a WRITABLE range (U-DATAWRITE)

The `hw` hypotheses are `m.accessible a n true = true`: writable memory, which `disjoint_of_dataLoaded` shows disjoint from the read-only
data. A read-only `Buffer` hypothesis (`m.accessible a n false = true`, which may overlap read-only data) used to be accepted by the tactic
and only the kernel rejected the proof built from it, far from the mistake. Now the tactic says so at once. -/

namespace JanusTests.DataWritable
open Janus Janus.Arm64 Janus.Tactic

def tablep : Program where
  segments := [{ name := "table", base := 0x40000, words := [0xd65f03c0] }]
  stubs := []
  exitAddr := 0
  data := [{ name := ".rodata", base := 0x40100, bytes := [1, 0, 0, 0, 0, 0, 0, 0] }]

/-- A writable range: accepted, and the disjointness fact is added. -/
example (m : Memory) (a : Nat) (hd : tablep.DataLoaded m) (hw : m.accessible a 8 true = true) : True := by
  janus_data hd [hw]
  have := h_ddisj0_0
  trivial

/-- A read-only range: an early error that says the range is read-only. -/
example (m : Memory) (a : Nat) (hd : tablep.DataLoaded m) (hw : m.accessible a 8 false = true) : True := by
  run_tac do
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| janus_data hd [hw]))
      Lean.throwError "accepted a read-only range"
    catch e =>
      unless (← e.toMessageData.toString).contains "READ-ONLY" do throw e
  trivial

/-- Another memory: an error. -/
example (m m' : Memory) (a : Nat) (hd : tablep.DataLoaded m) (hw : m'.accessible a 8 true = true) : True := by
  fail_if_success janus_data hd [hw]
  trivial

end JanusTests.DataWritable
