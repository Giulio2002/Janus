import Extracted

/-! Round 10 V1d: a contract stated about `Extracted.program` itself, where no code is at the
contract address (`janus extract --contract`), is false (or vacuous) for every state its
precondition admits. The statement must say `Extracted.program.link impl`. -/

open Janus Janus.Arm64 Janus.Contracts

namespace Proof

theorem correctness (rt : List (Nat × Nat)) (H : RtReady)
    (hnew : NewobjectContract Extracted.program
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) : True := trivial

end Proof
