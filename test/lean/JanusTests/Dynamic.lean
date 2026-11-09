import Janus

/-!
# Tests for dynamic calls (`Janus.Spec.Dynamic`, `janus_dyn`)

Two hand-assembled programs (`aarch64-linux-gnu-as`) whose only call is indirect: an interface
method call through the `Fun[0]` slot of a static itab (a tail call `br x3`), and a closure call
whose function and captured variable come from a funcval (`br x2` with the context in `X26`).
The hypotheses say which code the call reaches; `janus_dyn` turns them into the equations the
executor uses, and `janus_run` follows the call.
-/

namespace JanusTests.Dynamic

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-- `ldr x3, [x0, #24]; br x3` at `0x10000`; the method `add x0, x1, x1; ret` at `0x10100`; the
itab `go:itab.T,I` at `0x20000` (`Fun[0] = 0x10100`) and another one after it. -/
def iface : Program where
  segments := [{ name := "call", base := 0x10000, words := [0xf9400c03, 0xd61f0060] },
               { name := "T.M", base := 0x10100, words := [0x8b010020, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0
  data := [{ name := "go:itab.T,I", base := 0x20000, bytes :=
              [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0,
               0x00, 0x01, 0x01, 0, 0, 0, 0, 0] },
           { name := "go:itab.U,I", base := 0x20020, bytes := List.replicate 32 0 }]

theorem iface_spec (tab x : W64) :
    Ensures iface 0x10000 [tab, x] (fun s => ItabIs iface.data s.mem tab "go:itab.T,I")
      (fun _ s' => s'.regs 0 = x + x) := by
  intro ret hret s hs hi
  janus_intro hs
  janus_dyn hi
  janus_run

/-- The itab facts `janus_dyn` derives, including the disjointness from a writable range. -/
example (tab : W64) (s : State) (hi : ItabIs iface.data s.mem tab "go:itab.T,I")
    (hw : s.mem.accessible 0x30000 64 true = true) : tab = 0x20000#64 := by
  janus_dyn hi
  have : 0x30000 + 64 ≤ 0x20000 ∨ 0x20000 + 32 ≤ 0x30000 := h_dyn0_disj0
  have : s.mem.readLE 0x20018 8 = 0x10100 := h_dyn0_w3
  -- `tab` was a variable: it is substituted by the itab's address
  rfl

/-- `ItabIs` follows from `Program.DataLoaded` for an itab of the program's data. -/
example (s : State) (h : iface.DataLoaded s.mem) :
    ItabIs iface.data s.mem 0x20020#64 "go:itab.U,I" :=
  ItabIs.of_dataLoaded h (by decide) (by decide)

set_option linter.unusedVariables false in
/-- A missing itab is reported. -/
example (tab : W64) (s : State) (hi : ItabIs iface.data s.mem tab "go:itab.V,I") : True := by
  fail_if_success janus_dyn hi
  trivial

/-- `ldr x2, [x0]; mov x26, x0; mov x0, x1; br x2` at `0x10000`; the closure
`ldr x1, [x26, #8]; add x0, x0, x1; ret` at `0x10200`. -/
def closure : Program where
  segments := [{ name := "call", base := 0x10000, words := [0xf9400002, 0xaa0003fa, 0xaa0103e0, 0xd61f0040] },
               { name := "F.func1", base := 0x10200, words := [0xf9400741, 0x8b010000, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0

theorem closure_spec (f x c : W64) :
    Ensures closure 0x10000 [f, x]
      (fun s => FuncvalIs s.mem f (segAddr closure "F.func1") ∧ ClosureCtx s.mem f [c])
      (fun _ s' => s'.regs 0 = x + c ∧ s'.regs 26 = f) := by
  intro ret hret s hs ⟨hf, hc⟩
  janus_intro hs
  janus_dyn hf hc
  janus_run

set_option linter.unusedVariables false in
/-- Without the funcval hypothesis the call target is unknown and the run is stuck. -/
example (f x c : W64) : True := by
  fail_if_success
    have : Ensures closure 0x10000 [f, x] (fun s => ClosureCtx s.mem f [c])
        (fun _ s' => s'.regs 0 = x + c) := by
      intro ret hret s hs hc
      janus_intro hs
      janus_dyn hc
      janus_run
  trivial

end JanusTests.Dynamic
