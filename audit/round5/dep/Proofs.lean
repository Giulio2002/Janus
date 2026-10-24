import Extracted
import DecLib

/-! Round 5 consumer proofs against the DecLib dependency (example.com/basic.Add). -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace R5Proofs

theorem honest (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

/-- E1h: `decide` in a hypothesis elaborates to the dependency's instance. Expected Invalid. -/
theorem decInst (x y : BitVec 64) (_h : decide (x = 0) = false) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := honest x y

/-- E1i: the dependency's class-valued def passed to `decide`. Expected Invalid. -/
theorem decDef (x y : BitVec 64) (_h : @decide (x = 0) (DecLib.myDec x) = false) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := honest x y

/-- E1j: a dependency def whose *body* uses the custom instance. Allowed (dependency bodies are
the pinned dependency's; `Decidable p` is a subsingleton, so the instance cannot change what
`isZero` means). Expected Verified, with `DecLib.isZero` listed as a dependency constant. -/
theorem decBody (x y : BitVec 64) (_h : DecLib.isZero x = false) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := honest x y

/-- E3e: a dependency structure whose field is named `regs`. Allowed; the statement prints the
dependency's names in full and lists them. Expected Verified. -/
theorem viewRegs (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (DecLib.View.ofFun s'.regs).regs 0 = x + y) := honest x y

end R5Proofs
