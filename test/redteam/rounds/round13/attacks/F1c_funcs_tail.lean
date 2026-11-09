import Extracted

/-! Round 13 F1c_funcs_tail: the table is `Extracted.funcs.tail`. The statement assumes the runtime's `gopanic` contract for a function table the statement chose (not exactly `Extracted.funcs`), which can make the contract unsatisfiable or false for every implementation. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Proof

theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hpan : GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs.tail)
    (p x etyp edata : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [p, x, etyp, edata]
      (fun s => PanicCallerOK P s 128 40 ∧ Ptr s.mem p 8 true)
      (goClassU P U)
      (fun s s' => (s'.regs 0).toNat = x.toNat)
      (fun s v s' => 10 < x.toNat) := by
  sorry

end Proof
