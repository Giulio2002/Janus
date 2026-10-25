import Janus.Contracts.Sat
import Janus.Contracts.SatAmd64

/-!
# Non-vacuity of the write-barrier contracts (`WbContract`, `WbContract64`)

Toy witnesses (`Sat.wb_satisfiable`, `SatAmd64.wb_satisfiable`: code returning a heap address in
`R25`/`R11`) for every `N = 1 … 8`. The runtime's own `gcWriteBarrierN` meets the contracts as
well, when the buffer has room: `examples/proofs/WriteBarrier.lean` and its amd64 counterpart.
-/

namespace Janus.Contracts.WriteBarrierSat

open Janus Janus.Contracts

/-- `WbContract` (arm64) is satisfiable for `N = 1 … 8`. -/
theorem wb_satisfiable (n : Nat) (hn : n ≤ 8) : ∃ (rt : List (Nat × Nat)) (H : RtReady)
    (impl : List Janus.Segment), WbContract (Sat.toy.link impl) Sat.A0 rt Sat.wstack H n ∧
      ∃ s : Janus.Arm64.State, s.pc = BitVec.ofNat 64 Sat.A0 ∧ CallOK s Sat.wstack 0 ∧ Ready H rt [n] s :=
  Sat.wb_satisfiable n hn

/-- `WbContract64` (amd64) is satisfiable for `N = 1 … 8`. -/
theorem wb64_satisfiable (n : Nat) (hn : n ≤ 8) : ∃ (rt : List (Nat × Nat)) (H : RtReady)
    (impl : List Janus.Amd64.Segment), WbContract64 (SatAmd64.toy.link impl) SatAmd64.A0 rt SatAmd64.wstack H n ∧
      ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 SatAmd64.A0 ∧ CallOK64 s SatAmd64.wstack 0 ∧ Ready64 H rt [n] s :=
  SatAmd64.wb_satisfiable n hn

end Janus.Contracts.WriteBarrierSat
