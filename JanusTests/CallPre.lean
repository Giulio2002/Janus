import Janus
import Janus.Contracts.InternalCall

/-! # The precondition of an internal callee's summary, closed by `janus_run … calls [S]` (S5)

`caller` stores `X30` on the stack and calls `callee`; both are segments of ONE program with a read-only data
object. The runtime stand-in `impl` is abstract, with the layout hypothesis `(P.segments ++ impl).Pairwise
Segment.Apart` that `codeIn_restrict` needs. The callee's summary (`Ensures.toSummaryIn`) has the precondition

* `RetAddr p0 X30` for the callee's program `p0 = (P.onlySegments ["callee"]).link impl`: the return site is
  outside the callee's segments *and `impl`* and not a stub (b);
* `P.DataLoaded s.mem` for the memory after the caller's stack store (a);
* `64 ≤ b`, where the caller's context says `blockSize 32 false + blockSize 32 true ≤ b` (c).

All three used to remain as goals of `janus_run`. -/

namespace JanusTests.CallPre

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

/-- `x0 + 1`: `ADD X0, X0, #1; RET`. -/
def callee : Segment := ⟨"callee", 0x1000, [0x91000400, 0xd65f03c0]⟩
/-- `callee(x) + 1`: `STR X30, [SP, #-16]!; BL callee; LDR X30, [SP], #16; ADD X0, X0, #1; RET`. -/
def caller : Segment := ⟨"caller", 0x2000, [0xf81f0ffe, 0x97fffbff, 0xf84107fe, 0x91000400, 0xd65f03c0]⟩
def tbl : DataSegment := ⟨"tbl", 0x8000, [1, 2, 3, 4]⟩

def P : Program := { segments := [caller, callee], stubs := [], exitAddr := 0, data := [tbl] }

variable (impl : List Segment)

theorem calleeEns (x : W64) (b : Nat) :
    Ensures ((P.onlySegments ["callee"]).link impl) 0x1000 [x] (fun s => P.DataLoaded s.mem ∧ 64 ≤ b)
      (fun s s' => s'.regs 0 = x + 1 ∧ s'.mem = s.mem) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

set_option linter.defProp false in
def calleeSum (hx : ((P.onlySegments ["callee"]).link impl).fetch ((P.onlySegments ["callee"]).link impl).exitAddr = none)
    (hc : CodeIn ((P.onlySegments ["callee"]).link impl) (P.link impl)) (x : W64) (b : Nat) :=
  Ensures.toSummaryIn (calleeEns impl x b) hx hc

/-- The caller: the memory at the call is the entry memory after one 8-byte store into the stack. -/
theorem callerEns (hd : (P.segments ++ impl).Pairwise Segment.Apart)
    (hs : ∀ seg ∈ P.segments ++ impl, ∀ i < seg.words.length,
      P.stubAt (seg.base + 4 * i) = none ∧ seg.base + 4 * i ≠ P.exitAddr)
    (hx : ((P.onlySegments ["callee"]).link impl).fetch ((P.onlySegments ["callee"]).link impl).exitAddr = none)
    (x : W64) (b : Nat) :
    Ensures (P.link impl) 0x2000 [x]
      (fun s => StackOK s 16 0 ∧ P.DataLoaded s.mem ∧ blockSize 32 false + blockSize 32 true ≤ b)
      (fun _ s' => s'.regs 0 = x + 2) := by
  intro ret hret s hs0 ⟨⟨hal, hb, ha, hw⟩, hdl, hbud⟩
  have S := calleeSum impl hx (codeIn_restrict P ["callee"] impl hd hs) x b
  janus_intro hs0
  janus_run calls [S]

end JanusTests.CallPre
