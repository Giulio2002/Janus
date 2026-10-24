import Janus
import JanusTests.Tactic

/-!
# Tests for the stuck diagnostics of `janus_run` / `janus64_run`

Each test is a tiny hand-assembled program on which symbolic execution cannot proceed, checked
with `#guard_msgs (substring := true)`: the error must name the pc, the instruction and the
reason. (These `example`s fail on purpose; `#guard_msgs` turns the expected error into a
passing test.) Also: the disassemblers, and the information message about unresolved aliasing.
-/

namespace JanusTests.Diagnostics

/-! ## The disassemblers -/

section Disasm
open Janus.Arm64

#guard Disasm.disasm (some 0x10000) (.b true 4) == "bl 0x10010"
#guard Disasm.disasm none (.addSubShifted true false false .lsl 1 0 0 0) == "add x0, x0, x1"
#guard Disasm.disasm none (.ldstUImm 3 1 2 28 16) == "ldr x16, [x28, #0x10]"
#guard Disasm.disasm none (.ldstImm9 3 0 .pre 496 31 30) == "str x30, [sp, #-0x10]!"
#guard Disasm.disasm none (.addSubShifted true true true .lsl 2 0 0 31) == "cmp x0, x2"
#guard Disasm.disasm none (.madd true false 2 31 1 0) == "mul x0, x1, x2"
#guard Disasm.disasm none (.ret 30) == "ret"
end Disasm

section Disasm64
open Janus.Amd64

#guard Disasm.disasm none 3 (.alu .add 64 (.reg 0) (.loc (.reg 3))) == "add rax, rbx"
#guard Disasm.disasm (some 0x1000) 5 (.call 0x10) == "call 0x1015"
#guard Disasm.disasm none 4 (.alu .cmp 64 (.reg 4) (.loc (.mem ⟨some 14, none, 0, 16, false, false⟩))) ==
  "cmp rsp, qword ptr [r14 + 0x10]"
#guard Disasm.disasm none 4 (.mov 64 (.mem ⟨some 4, some 1, 3, 0, false, false⟩) (.loc (.reg 2))) ==
  "mov qword ptr [rsp + rcx*8], rdx"
#guard Disasm.disasm none 9 (.mov 64 (.reg 14) (.loc (.mem ⟨none, none, 0, 0xfffffffffffffff8, false, true⟩))) ==
  "mov r14, qword ptr fs:[-0x8]"
end Disasm64

/-! ## arm64 -/

section Arm64
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-- `add x0, x0, x1; udf #0` -/
def undec : Program where
  segments := [{ name := "undec", base := 0x10000, words := [0x8b010000, 0x00000000] }]
  stubs := []
  exitAddr := 0

/-- error: janus_run: stuck at pc 0x10004 (undec+0x4): the word 0x0 does not decode -/
#guard_msgs (substring := true) in
example : Ensures undec 0x10000 [] (fun _ => True) (fun _ _ => True) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

/-- `b .+0x100` (out of the extracted code) -/
def nocode : Program where
  segments := [{ name := "nocode", base := 0x10000, words := [0x14000040] }]
  stubs := []
  exitAddr := 0

/-- error: janus_run: stuck after 1 instructions: pc 0x10100 is not in the extracted code (segments: nocode [0x10000, 0x10004)) -/
#guard_msgs (substring := true) in
example : Ensures nocode 0x10000 [] (fun _ => True) (fun _ _ => True) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

/-- `br x5` -/
def indirect : Program where
  segments := [{ name := "indirect", base := 0x10000, words := [0xd61f00a0] }]
  stubs := []
  exitAddr := 0

/-- error: janus_run: stuck after 1 instructions: the pc of the current state is not a concrete address:
  s.regs 5 -/
#guard_msgs (substring := true) in
example : Ensures indirect 0x10000 []
    (fun s => (s.regs 5).toNat < 2 ^ 56 ∧ (s.regs 5).toNat % 4 = 0) (fun _ _ => True) := by
  intro ret hret s hs ⟨h1, h2⟩
  janus_intro hs
  janus_run

-- Without the facts about `x5`, the branch on its range is not pruned, and on that branch the
-- jump faults.
/-- hbr : `72057594037927936 ≤ BitVec.toNat (s.regs 5)` -/
#guard_msgs (substring := true) in
example : Ensures indirect 0x10000 [] (fun _ => True) (fun _ _ => True) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

/-- `ldr x0, [x1]; ret` -/
def load : Program where
  segments := [{ name := "load", base := 0x10000, words := [0xf9400020, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0

/-- error: janus_run: stuck at pc 0x10000 (load): ldr x0, [x1]
• cannot prove that the 8-byte read at `p.toNat` is allowed -/
#guard_msgs (substring := true) in
example (x p : BitVec 64) :
    Ensures load 0x10000 [x, p] (fun _ => True) (fun _ _ => True) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

-- The `accessible` fact is there but too short: the message says which bound fails.
/-- `p.toNat + 8 ≤ p.toNat + 4` is not provable by omega -/
#guard_msgs (substring := true) in
example (x p : BitVec 64) :
    Ensures load 0x10000 [x, p] (fun s => s.mem.accessible p.toNat 4 false = true)
      (fun _ _ => True) := by
  intro ret hret s hs hp
  janus_intro hs
  janus_run

/-- error: janus_run: heartbeat budget exceeded -/
#guard_msgs (substring := true) in
example (x y : W64) :
    Ensures JanusTests.Tactic.straight 0x10000 [x, y] (fun _ => True) (fun _ _ => True) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run (budget := 1)

-- A summary whose precondition does not hold at the call site.
theorem g_summary_strict :
    Summary JanusTests.Tactic.callp 0x50014
      (fun s => s.regs 0 = 0#64 ∧ (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56)
      (fun s s' => s' = { s with regs := setReg s.regs 0 (s.regs 0 + 1#64), pc := s.regs 30 }) := by
  intro s hpc ⟨h0, h1, h2⟩
  janus_run

/-- error: janus_run: at pc 0x50014, the entry of f+0x14: the precondition of its summary could not be proved. Remaining goals (after simplification):
  BitVec.toNat x = 0 -/
#guard_msgs (substring := true) in
example (x : W64) :
    Ensures JanusTests.Tactic.callp 0x50000 [x] (fun s => StackOK s 16 0) (fun _ _ => True) := by
  intro ret hret s hs ⟨hal, hb, ha, hw⟩
  janus_intro hs
  janus_run calls [g_summary_strict]

/-- `str x2, [x0]; ldr x0, [x1]; ret`: the run succeeds, but the result is the read of `x1`
after the store to `x0`, whose aliasing is unknown. -/
def alias : Program where
  segments := [{ name := "alias", base := 0x10000, words := [0xf9000002, 0xf9400020, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0

/-- info: janus_run: the remaining goals contain reads over earlier stores whose aliasing is unknown -/
#guard_msgs (substring := true) in
example (a b v : BitVec 64) :
    Ensures alias 0x10000 [a, b, v]
      (fun s => s.mem.accessible a.toNat 8 true = true ∧ s.mem.accessible b.toNat 8 false = true ∧
        a.toNat + 8 ≤ 2 ^ 48 ∧ b.toNat + 8 ≤ 2 ^ 48)
      (fun _ s' => (s'.regs 0).toNat < 2 ^ 64) := by
  intro ret hret s hs ⟨ha, hb, ha', hb'⟩
  janus_intro hs
  janus_run
  janus_arith

end Arm64

/-! ## amd64 -/

section Amd64
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `add rax, rbx; syscall` -/
def undec64 : Program where
  segments := [⟨"undec", 0x1000, [0x48, 0x01, 0xd8, 0x0f, 0x05]⟩]
  stubs := []
  exitAddr := 0

/-- error: janus64_run: stuck at rip 0x1003 (undec+0x3): the bytes [0xf, 0x5] do not decode -/
#guard_msgs (substring := true) in
example (a b : BitVec 64) : Ensures undec64 0x1000 [a, b] (fun _ => True) (fun _ _ => True) := by
  intro ret hret s hs _
  janus64_intro hs
  janus64_run

/-- `jmp .+0x105` -/
def nocode64 : Program where
  segments := [⟨"nocode", 0x1000, [0xe9, 0x00, 0x01, 0x00, 0x00]⟩]
  stubs := []
  exitAddr := 0

/-- error: janus64_run: stuck after 1 instructions: rip 0x1105 is not in the extracted code -/
#guard_msgs (substring := true) in
example : Ensures nocode64 0x1000 [] (fun _ => True) (fun _ _ => True) := by
  intro ret hret s hs _
  janus64_intro hs
  janus64_run

/-- `mov rax, qword ptr [rbx]; ret` -/
def load64 : Program where
  segments := [⟨"load", 0x1000, [0x48, 0x8b, 0x03, 0xc3]⟩]
  stubs := []
  exitAddr := 0

/-- error: janus64_run: stuck at pc 0x1000 (load): mov rax, qword ptr [rbx]
• cannot prove that the 8-byte read at `p.toNat` is allowed -/
#guard_msgs (substring := true) in
example (a p : BitVec 64) :
    Ensures load64 0x1000 [a, p] (fun s => StackWritable s 0 8) (fun _ _ => True) := by
  intro ret hret s hs hpre
  janus64_intro hs
  janus64_run

/-- error: janus64_run: heartbeat budget exceeded -/
#guard_msgs (substring := true) in
example (a p : BitVec 64) :
    Ensures load64 0x1000 [a, p] (fun s => StackWritable s 0 8) (fun _ _ => True) := by
  intro ret hret s hs hpre
  janus64_intro hs
  janus64_run (budget := 1)

end Amd64

end JanusTests.Diagnostics
