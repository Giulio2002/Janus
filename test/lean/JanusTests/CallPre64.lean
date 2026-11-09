import Janus
import Janus.Contracts.InternalCallAmd64

/-! # The precondition of an internal callee's summary, closed by `janus64_run … calls [S]` (S5, amd64)

The amd64 twin of `JanusTests/CallPre.lean`: `CALL` pushes the return address (a store into the stack window), the
callee's precondition mentions the program's read-only data (`DataLoaded` across that store), the return site must be
an admissible return address of the callee's program with an abstract runtime stand-in `impl` (a), (b), and a
bound `64 ≤ b` follows from `blockSize 32 false + blockSize 32 true ≤ b` (c). -/

namespace JanusTests.CallPre64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel

/-- `rax + 1`: `ADD RAX, 1; RET`. -/
def callee : Janus.Amd64.Segment := ⟨"callee", 0x1000, [0x48, 0x83, 0xc0, 0x01, 0xc3]⟩
/-- `callee(x) + 1`: `CALL callee; ADD RAX, 1; RET`. -/
def caller : Janus.Amd64.Segment :=
  ⟨"caller", 0x2000, [0xe8, 0xfb, 0xef, 0xff, 0xff, 0x48, 0x83, 0xc0, 0x01, 0xc3]⟩
def tbl : Janus.DataSegment := ⟨"tbl", 0x8000, [1, 2, 3, 4]⟩

def P : Janus.Amd64.Program := { segments := [caller, callee], stubs := [], exitAddr := 0, data := [tbl] }

variable (impl : List Janus.Amd64.Segment)

theorem calleeEns (x : W64) (b : Nat) :
    Ensures ((P.onlySegments ["callee"]).link impl) 0x1000 [x]
      (fun s => StackWritable s 0 8 ∧ P.DataLoaded s.mem ∧ 64 ≤ b)
      (fun s s' => s'.regs 0 = x + 1 ∧ s'.mem = s.mem) := by
  intro ret hret s hs ⟨⟨hb, ha, hw⟩, _⟩
  janus64_intro hs
  simp only [regSP] at hb ha hw
  janus64_run

set_option linter.defProp false in
def calleeSum
    (hx : ((P.onlySegments ["callee"]).link impl).fetch ((P.onlySegments ["callee"]).link impl).exitAddr = none)
    (hc : CodeIn64 ((P.onlySegments ["callee"]).link impl) (P.link impl)) (x : W64) (b : Nat) :=
  Janus.Amd64.Ensures.toSummaryIn (calleeEns impl x b) hx (by show 1 ≤ 9; decide) hc

theorem callerEns (hd : (P.segments ++ impl).Pairwise Janus.Amd64.Segment.Apart)
    (hs : ∀ seg ∈ P.segments ++ impl, ∀ i < seg.bytes.length,
      P.stubAt (seg.base + i) = none ∧ seg.base + i ≠ P.exitAddr)
    (hx : ((P.onlySegments ["callee"]).link impl).fetch ((P.onlySegments ["callee"]).link impl).exitAddr = none)
    (x : W64) (b : Nat) :
    Ensures (P.link impl) 0x2000 [x]
      (fun s => (StackWritable s 8 8 ∧ (s.regs 4).toNat % 8 = 0) ∧ P.DataLoaded s.mem ∧
        blockSize 32 false + blockSize 32 true ≤ b)
      (fun _ s' => s'.regs 0 = x + 2) := by
  intro ret hret s hs0 ⟨⟨⟨hb, ha, hw⟩, hal⟩, hdl, hbud⟩
  have S := calleeSum impl hx (codeIn_restrict64 P ["callee"] impl hd hs) x b
  janus64_intro hs0
  simp only [regSP] at hb ha hw hal
  janus64_run calls [S]

end JanusTests.CallPre64
