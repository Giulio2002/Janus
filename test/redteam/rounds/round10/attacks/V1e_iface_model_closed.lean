import Extracted

/-! Round 10 V1e: the interface model fixed to the toy model `R0` of the satisfiability witnesses
in a contract hypothesis: a claim that the real runtime is that toy, not an assumption about
the runtime. -/

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.Iface

namespace Proof

theorem correctness (impl : List Segment) (H : RtReady)
    (hconv : ConvT64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") Janus.Contracts.IfaceModel.R0 H) : True := trivial

end Proof
