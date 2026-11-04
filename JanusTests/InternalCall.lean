import Janus
import Janus.Contracts.InternalCall
import Janus.Contracts.InternalCallAmd64

/-! Internal calls (`Janus.Contracts.InternalCall`, `InternalCallAmd64`): `caller` calls `callee`, both
segments of ONE program. The callee is proved about its own code (`P.onlySegments ["callee"]`, where
the caller's return site is an admissible return address), moved to the whole program as a `Summary`
(`Ensures.toSummaryIn`) and used by the caller's proof (`calls [S]`). -/

namespace JanusTests.InternalCall.Arm

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

/-- `x0 + 1`: `ADD X0, X0, #1; RET`. -/
def callee : Segment := ⟨"callee", 0x1000, [0x91000400, 0xd65f03c0]⟩
/-- `callee(x) + 1`: `STR X30, [SP, #-16]!; BL callee; LDR X30, [SP], #16; ADD X0, X0, #1; RET`. -/
def caller : Segment := ⟨"caller", 0x2000, [0xf81f0ffe, 0x97fffbff, 0xf84107fe, 0x91000400, 0xd65f03c0]⟩

def P : Program := { segments := [caller, callee], stubs := [], exitAddr := 0 }

/-- The whole program and the callee's own program (here with no runtime code linked). -/
def Pw : Program := P.link []
def P0 : Program := (P.onlySegments ["callee"]).link []

theorem hc : CodeIn P0 Pw := codeIn_restrict P ["callee"] [] (by decide) (by decide)

theorem noExit : P0.fetch P0.exitAddr = none := by decide

theorem calleeEns (x : W64) :
    Ensures P0 0x1000 [x] (fun _ => True) (fun s s' => s'.regs 0 = x + 1 ∧ s'.mem = s.mem) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

set_option linter.defProp false in
def calleeSum (x : W64) := Ensures.toSummaryIn (calleeEns x) noExit hc

/-- The caller, with the callee as a summary. -/
theorem callerEns (x : W64) :
    Ensures Pw 0x2000 [x] (fun s => StackOK s 16 0) (fun _ s' => s'.regs 0 = x + 2) := by
  intro ret hret s hs ⟨hal, hb, ha, hw⟩
  janus_intro hs
  janus_run calls [calleeSum x]

/-! The runtime contracts are hypotheses about a program with no user code (`ofImpl`), and move up. -/

def impl : List Segment := [⟨"stub", 0x50000, [0xd65f03c0]⟩]

example (a : Nat) (R : RtInv) (h : NewobjectLiveContract (P.ofImpl impl) a 4096 R) :
    NewobjectLiveContract ((P.onlySegments ["callee"]).link impl) a 4096 R :=
  NewobjectLiveContract.of_codeIn (codeIn_ofImpl P (P.onlySegments ["callee"]) impl ⟨rfl, rfl⟩ (by decide)) h

example (a : Nat) (R : RtInv) (h : NewobjectLiveContract (P.ofImpl impl) a 4096 R) :
    NewobjectLiveContract (P.link impl) a 4096 R :=
  NewobjectLiveContract.of_codeIn (codeIn_ofImpl P P impl ⟨rfl, rfl⟩ (by decide)) h

/-- The callee's program with the runtime linked is still the callee's code inside the whole program. -/
example : CodeIn ((P.onlySegments ["callee"]).link impl) (P.link impl) :=
  codeIn_restrict P ["callee"] impl (by decide) (by decide)

end JanusTests.InternalCall.Arm

namespace JanusTests.InternalCall.Amd

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel

/-- `rax + 1`: `ADD RAX, 1; RET`. -/
def callee : Janus.Amd64.Segment := ⟨"callee", 0x1000, [0x48, 0x83, 0xc0, 0x01, 0xc3]⟩
/-- `callee(x) + 1`: `CALL callee; ADD RAX, 1; RET`. -/
def caller : Janus.Amd64.Segment :=
  ⟨"caller", 0x2000, [0xe8, 0xfb, 0xef, 0xff, 0xff, 0x48, 0x83, 0xc0, 0x01, 0xc3]⟩

def P : Janus.Amd64.Program := { segments := [caller, callee], stubs := [], exitAddr := 0 }

def Pw : Janus.Amd64.Program := P.link []
def P0 : Janus.Amd64.Program := (P.onlySegments ["callee"]).link []

theorem hc : CodeIn64 P0 Pw := codeIn_restrict64 P ["callee"] [] (by decide) (by decide)

theorem noExit : P0.fetch P0.exitAddr = none := by decide

theorem calleeEns (x : W64) :
    Ensures P0 0x1000 [x] (fun s => StackWritable s 0 8) (fun s s' => s'.regs 0 = x + 1 ∧ s'.mem = s.mem) := by
  intro ret hret s hs ⟨hb, ha, hw⟩
  janus64_intro hs
  simp only [regSP] at hb ha hw
  janus64_run

set_option linter.defProp false in
def calleeSum (x : W64) := Ensures.toSummaryIn (calleeEns x) noExit (by show 1 ≤ 9; decide) hc

theorem callerEns (x : W64) :
    Ensures Pw 0x2000 [x] (fun s => StackWritable s 8 8 ∧ (s.regs 4).toNat % 8 = 0)
      (fun _ s' => s'.regs 0 = x + 2) := by
  intro ret hret s hs ⟨⟨hb, ha, hw⟩, hal⟩
  janus64_intro hs
  simp only [regSP] at hb ha hw hal
  janus64_run calls [calleeSum x]

def impl : List Janus.Amd64.Segment := [⟨"stub", 0x50000, [0xc3]⟩]

example (a : Nat) (R : RtInv) (h : NewobjectLiveContract64 (P.ofImpl impl) a 4096 R) :
    NewobjectLiveContract64 ((P.onlySegments ["callee"]).link impl) a 4096 R :=
  NewobjectLiveContract64.of_codeIn (codeIn_ofImpl64 P (P.onlySegments ["callee"]) impl ⟨rfl, rfl⟩ (by decide)) h

example : CodeIn64 ((P.onlySegments ["callee"]).link impl) (P.link impl) :=
  codeIn_restrict64 P ["callee"] impl (by decide) (by decide)

end JanusTests.InternalCall.Amd
